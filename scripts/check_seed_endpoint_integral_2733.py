#!/usr/bin/env python3
"""Verify the endpoint integral proof and exact rational charge tie."""
from fractions import Fraction
import argparse
import hashlib
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
MODULE = "ConnesWeilRH/Dev/C1SeedEndpointIntegral2733"
PREFIX = "ConnesWeilRH.Source.C1ExplicitSmoothSeed."


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--workspace", type=Path, required=True)
    args = parser.parse_args()
    log = args.workspace / "build-logs/2733_seed_endpoint_integral.log"
    body = log.read_text(encoding="utf-8")
    source = (ROOT / (MODULE + ".lean")).read_text(encoding="utf-8")
    audit = (ROOT / (MODULE + "Audit.lean")).read_text(encoding="utf-8")
    names = re.findall(r"^theorem (\w+)\b", source, re.M)
    pins = re.findall(r"^#print axioms (\w+)\s*$", audit, re.M)
    checks = {
        "build_footer": bool(re.search(r"^Build completed successfully \(\d+ jobs\)\.$", body, re.M)),
        "no_errors": not re.search(r"^error:", body, re.M),
        "no_entry_warnings": not re.search(r"^warning: " + re.escape(MODULE), body, re.M),
        "declaration_audit_exact": names == pins and len(names) == 8 and len(set(names)) == 8,
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
    reference = ROOT / "results/2730_seed_derivative_bounds.json"
    original = json.loads(reference.read_text())
    charge_block = re.search(r"^def seedEndpointCharge2733 \(n : ℕ\) : ℝ :=(.*?)(?=^theorem )", source, re.M | re.S)
    expected = "32 * (endpointTransitionCoef2732 n : ℝ) * (1 / 4096 : ℝ) * (4096 : ℝ) ^ (2 * n) / (2 : ℝ) ^ 4096"
    checks["charge_definition_pin"] = (charge_block is not None and
        re.sub(r"\s+", "", charge_block.group(1)) == re.sub(r"\s+", "", expected))
    charges = {}
    for n in range(1, 8):
        charge = Fraction(32 * original["majorants"]["T"][n] * 4096 ** (2*n), 4096 * 2 ** 4096)
        charges[str(n)] = str(charge)
        checks["charge_tie_" + str(n)] = charge == Fraction(original["bounds"][str(n)]["endpoint_upper_rational"])
    final = re.search(r"^theorem transition_endpoint_integral_le_charge2733\b(.*?) := by", source, re.M | re.S)
    checks["integral_order_and_owner_pins"] = (final is not None and
        "(hn0 : 0 < n)" in final.group(1) and "(hn : n ≤ 7)" in final.group(1)
        and "iteratedDeriv n Real.smoothTransition x" in final.group(1)
        and source.count("(hn : n ≤ 7)") == 2 and source.count("(hn0 : 0 < n)") == 2)
    payload = {"record": 2733, "status": "PASS" if all(checks.values()) else "FAIL",
               "checks": checks, "axioms": axioms, "source_sha256": hashes,
               "build_log_sha256": digest(log), "checker_sha256": digest(Path(__file__)),
               "charge_reference_sha256": digest(reference), "endpoint_charges": charges,
               "nonclaims": ["Endpoint charge is proved; full D4/D7 integrals and finite interval replay remain open.",
                             "No carrier re-seed, gate or universal-rho producer is supplied."]}
    out = ROOT / "results/2733_seed_endpoint_integral.json"
    out.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    for key, value in checks.items():
        print(("PASS " if value else "FAIL ") + key)
    return 0 if all(checks.values()) else 1


if __name__ == "__main__":
    sys.exit(main())
