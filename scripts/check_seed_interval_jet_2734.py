#!/usr/bin/env python3
"""Check canonical interval-jet containment and the one-cell convention control."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
MODULE = "ConnesWeilRH/Dev/C1SeedIntervalJet2734"
PREFIX = "ConnesWeilRH.Source.C1ExplicitSmoothSeed."


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--workspace", type=Path, required=True)
    args = parser.parse_args()
    log = args.workspace / "build-logs/2734_seed_interval_jet.log"
    body = log.read_text(encoding="utf-8")
    source = (ROOT / (MODULE + ".lean")).read_text(encoding="utf-8")
    audit = (ROOT / (MODULE + "Audit.lean")).read_text(encoding="utf-8")
    names = re.findall(r"^theorem (\w+)\b", source, re.M)
    pins = re.findall(r"^#print axioms (\w+)\s*$", audit, re.M)
    checks = {
        "build_footer": bool(re.search(r"^Build completed successfully \(\d+ jobs\)\.$", body, re.M)),
        "no_errors": not re.search(r"^error:", body, re.M),
        "no_entry_warnings": not re.search(r"^warning: " + re.escape(MODULE), body, re.M),
        "declaration_audit_exact": names == pins and len(names) == 13 and len(set(names)) == 13,
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
    cell_theorems = ["phaseJetInterval_mem2734", "seedExpJetInterval_mem2734",
                     "seedDenominatorJetInterval_mem2734", "seedReciprocalJetInterval_mem2734",
                     "seedTransitionJetInterval_mem2734", "norm_iteratedDeriv_le_seedCellJet2734"]
    scopes = []
    for name in cell_theorems:
        region = re.search(r"^theorem " + name + r"\b(.*?) := by", source, re.M | re.S)
        scopes.append(region is not None and all(pin in region.group(1) for pin in
                      ["(hlo : 0 < B.lo)", "(hhi : B.hi < 1)", "(hx : B.Mem x)"]))
    checks["cell_binding_and_global_count_pins"] = (all(scopes) and
        source.count("(hlo : 0 < B.lo)") == 6 and source.count("(hhi : B.hi < 1)") == 6)
    control_path = ROOT / "results/2734_seed_interval_jet_control.json"
    control = json.loads(control_path.read_text())
    checks["one_cell_control"] = (control["status"] == "CONTROL-PASS" and
        len(control["checks"]) == 34 and all(control["checks"].values()))
    checks["control_source_hash"] = (control["checker_sha256"] == digest(ROOT / "scripts/seed_interval_jet_control_2734.py")
        and control["parent_sha256"] == digest(ROOT / "scripts/p3_certified_strip_constants_2720.py"))
    dependencies = {}
    for name in ["C1RouteAIntervalAlgebra", "C1SeedJetSemantics2731"]:
        relative = "ConnesWeilRH/Dev/" + name + ".lean"
        dependencies[relative] = digest(ROOT / relative)
        checks["dependency_source_" + name] = dependencies[relative] == digest(args.workspace / relative)
    payload = {"record": 2734, "status": "PASS" if all(checks.values()) else "FAIL",
               "checks": checks, "axioms": axioms, "source_sha256": hashes,
               "build_log_sha256": digest(log), "checker_sha256": digest(Path(__file__)),
               "dependency_source_sha256": dependencies, "control_sha256": digest(control_path),
               "nonclaims": ["Exact real interval-jet containment is proved; rational/floating endpoint replay and full D4/D7 integrals remain open.",
                             "No carrier re-seed, gate or universal-rho producer is supplied."]}
    out = ROOT / "results/2734_seed_interval_jet.json"
    out.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    for key, value in checks.items():
        print(("PASS " if value else "FAIL ") + key)
    return 0 if all(checks.values()) else 1


if __name__ == "__main__":
    sys.exit(main())
