#!/usr/bin/env python3
"""Read back the focused Linux build, exact source copies and axiom audit."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
MODULE = "ConnesWeilRH/Dev/C1SeedJetSemantics2731"
PREFIX = "ConnesWeilRH.Source.C1ExplicitSmoothSeed."


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--workspace", type=Path, required=True)
    args = parser.parse_args()
    log = args.workspace / "build-logs/2731_seed_semantics.log"
    body = log.read_text(encoding="utf-8")
    source = (ROOT / (MODULE + ".lean")).read_text(encoding="utf-8")
    audit = (ROOT / (MODULE + "Audit.lean")).read_text(encoding="utf-8")
    names = re.findall(r"^theorem (\w+)\b", source, re.M)
    pins = re.findall(r"^#print axioms (\w+)\s*$", audit, re.M)
    checks = {
        "build_footer": bool(re.search(r"^Build completed successfully \(\d+ jobs\)\.$", body, re.M)),
        "no_errors": not re.search(r"^error:", body, re.M),
        "no_entry_warnings": not re.search(r"^warning: " + re.escape(MODULE), body, re.M),
        "declaration_audit_exact": names == pins and len(names) == 9 and len(set(names)) == 9,
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
    payload = {"record": 2731, "status": "PASS" if all(checks.values()) else "FAIL",
               "checks": checks, "axioms": axioms, "source_sha256": hashes,
               "build_log_sha256": digest(log), "checker_sha256": digest(Path(__file__)),
               "nonclaims": ["No D4/D7 integral bound, endpoint certificate or interval replay is proved.",
                             "No carrier re-seed, gate or universal-rho producer is supplied."]}
    out = ROOT / "results/2731_seed_jet_semantics.json"
    out.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    for key, value in checks.items():
        print(("PASS " if value else "FAIL ") + key)
    return 0 if all(checks.values()) else 1


if __name__ == "__main__":
    sys.exit(main())
