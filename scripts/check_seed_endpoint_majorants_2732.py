#!/usr/bin/env python3
"""Check endpoint majorants, source copies, coefficient ties and axiom audit."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
MODULE = "ConnesWeilRH/Dev/C1SeedEndpointMajorants2732"
PREFIX = "ConnesWeilRH.Source.C1ExplicitSmoothSeed."


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--workspace", type=Path, required=True)
    args = parser.parse_args()
    log = args.workspace / "build-logs/2732_seed_endpoint.log"
    body = log.read_text(encoding="utf-8")
    source = (ROOT / (MODULE + ".lean")).read_text(encoding="utf-8")
    audit = (ROOT / (MODULE + "Audit.lean")).read_text(encoding="utf-8")
    names = re.findall(r"^theorem (\w+)\b", source, re.M)
    pins = re.findall(r"^#print axioms (\w+)\s*$", audit, re.M)
    checks = {
        "build_footer": bool(re.search(r"^Build completed successfully \(\d+ jobs\)\.$", body, re.M)),
        "no_errors": not re.search(r"^error:", body, re.M),
        "no_entry_warnings": not re.search(r"^warning: " + re.escape(MODULE), body, re.M),
        "declaration_audit_exact": names == pins and len(names) == 14 and len(set(names)) == 14,
    }
    clean = re.sub(r"/\-.*?\-/|--[^\n]*", "", source, flags=re.S)
    checks["no_admissions_or_new_axioms"] = not re.search(r"\b(sorry|admit|axiom)\b", clean)
    axioms = {}
    for name in names:
        pattern = (r"^info: " + re.escape(MODULE + "Audit.lean") + r":\d+:\d+: '"
                   + re.escape(PREFIX + name) + r"' depends on axioms: \[([^\]]*)\]")
        hits = re.findall(pattern, body, re.M)
        axioms[name] = hits[0].replace("\n", " ").split(",") if len(hits) == 1 else []
        axioms[name] = [a.strip() for a in axioms[name]]
        checks["axioms_" + name] = axioms[name] == ["propext", "Classical.choice", "Quot.sound"]
    hashes = {}
    for suffix in [".lean", "Audit.lean"]:
        relative = MODULE + suffix
        hashes[relative] = digest(ROOT / relative)
        checks["source_copy_" + suffix] = hashes[relative] == digest(args.workspace / relative)
        olean = args.workspace / ".lake/build/lib/lean" / relative.replace(".lean", ".olean")
        checks["olean_" + suffix] = (olean.is_file() and olean.stat().st_size > 0
                                          and olean.stat().st_mtime >= (args.workspace / relative).stat().st_mtime)
    original = json.loads((ROOT / "results/2730_seed_derivative_bounds.json").read_text())
    for function, key in [("endpointExpCoef2732", "E"),
                          ("endpointReciprocalCoef2732", "reciprocal"),
                          ("endpointTransitionCoef2732", "T")]:
        block = re.search(r"^def " + function + r" :.*?(?=^def |^theorem )", source, re.M | re.S)
        pairs = re.findall(r"\| (\d+) => (\d+)", block.group() if block else "")
        checks["coefficient_tie_" + key] = (len(pairs) == 8 and
            [int(k) for k, _ in pairs] == list(range(8)) and
            [int(v) for _, v in pairs] == original["majorants"][key])
    final = re.search(r"^theorem abs_iteratedDeriv_smoothTransition_endpoint2732\b(.*?) := by", source, re.M | re.S)
    checks["endpoint_order_domain_pins"] = (final is not None and
        "(hn : n ≤ 7)" in final.group(1) and "(hx0 : 0 < x)" in final.group(1)
        and "(hxhalf : x ≤ 1 / 2)" in final.group(1)
        and source.count("(hn : n ≤ 7)") == 6)
    payload = {"record": 2732, "status": "PASS" if all(checks.values()) else "FAIL",
               "checks": checks, "axioms": axioms, "source_sha256": hashes,
               "build_log_sha256": digest(log), "checker_sha256": digest(Path(__file__)),
               "coefficient_reference_sha256": digest(ROOT / "results/2730_seed_derivative_bounds.json"),
               "nonclaims": ["Pointwise endpoint derivative bounds are proved; no endpoint integral or D4/D7 integral certificate is proved.",
                             "No carrier re-seed, gate or universal-rho producer is supplied."]}
    out = ROOT / "results/2732_seed_endpoint_majorants.json"
    out.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    for key, value in checks.items():
        print(("PASS " if value else "FAIL ") + key)
    return 0 if all(checks.values()) else 1


if __name__ == "__main__":
    sys.exit(main())
