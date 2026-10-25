#!/usr/bin/env python3
"""Build the actual detector parameter bounds and their integration controls.

Only Lean's reported standard axiom trio is accepted. The JSON is portable;
the full build log remains a local diagnostic. Use --self-test to exercise
failure detection without invoking Lake.
"""

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

from routea_local_screen_audit_3094 import MODULES as SCREEN_MODULES
from routea_local_screen_audit_3094 import REQUIRED as SCREEN_REQUIRED


MODULES = SCREEN_MODULES + [
    "C1DetectorHeightCost3095Audit",
    "C1DetectorNearCollisionCost3096Audit",
    "C1RouteBSeedLedgerAllowance3071Audit",
    "C1RowBPrefixTransport2723Audit",
]
HEIGHT = "ConnesWeilRH.Source.C1DetectorHeightCost3095."
GAP = "ConnesWeilRH.Source.C1DetectorNearCollisionCost3096."
REQUIRED = SCREEN_REQUIRED + [
    "ConnesWeilRH.Source.C1RouteAOwnerAnalyticTransform3092."
    "routeAOwner_laplaceAt_rho_eq_one",
    HEIGHT + "unit_laplace_target_height_le",
    HEIGHT + "no_unit_target_above_height_budget",
    HEIGHT + "fixed_detector_unit_targets_not_unbounded",
    HEIGHT + "selected_detector_height_le",
    GAP + "laplace_derivative_norm_le_mass",
    GAP + "laplace_gap_le_mass",
    GAP + "raw_factor_unit_targets",
    GAP + "raw_factor_height_le",
    GAP + "opposite_targets_nodes_ne",
    GAP + "raw_factor_inverse_gap_mass",
    GAP + "no_raw_factor_mass_cap_below_inverse_gap",
    "ConnesWeilRH.Dev.routeBSeedLedger_order4_full_target3071",
    "ConnesWeilRH.Dev.routeBSeedLedger_order7_full_target3071",
    "ConnesWeilRH.Source.C1RowBPrefixTransport2723."
    "fourPointContradictionRowBStored2723",
]
SOURCES = [
    "ConnesWeilRH/Dev/C1DetectorHeightCost3095.lean",
    "ConnesWeilRH/Dev/C1DetectorNearCollisionCost3096.lean",
    "ConnesWeilRH/Dev/C1RouteAOwnerAnalyticTransform3092.lean",
    "ConnesWeilRH/Dev/C1RouteBSeedLedgerAllowance3071.lean",
    "ConnesWeilRH/Dev/C1RouteBSeedLedgerAllowanceContract3031.lean",
    "ConnesWeilRH/Dev/C1RouteBSeedD4D7Aggregate3042.lean",
    "ConnesWeilRH/Dev/C1RowBPrefixTransport2723.lean",
]


def inspect_log(log, returncode, required):
    declarations = {
        name: [a.strip() for a in axioms.split(",") if a.strip()]
        for name, axioms in re.findall(
            r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", log
        )
    }
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    unexpected = {n: a for n, a in declarations.items() if set(a) != allowed}
    missing = [n for n in required if n not in declarations]
    completed = re.search(r"Build completed successfully \((\d+) jobs\)", log)
    errors = bool(re.search(r"^error:", log, re.MULTILINE))
    sorry = "sorryAx" in log
    passed = (returncode == 0 and completed is not None
              and not errors and not sorry and not unexpected and not missing)
    return {
        "status": "PASS" if passed else "FAIL",
        "build_returncode": returncode,
        "build_jobs": int(completed.group(1)) if completed else None,
        "error_lines_present": errors,
        "sorryAx_present": sorry,
        "required_theorems": {n: declarations[n] for n in required if n in declarations},
        "all_reported_axiom_declarations": len(declarations),
        "unexpected_axioms": unexpected,
        "missing_required_theorems": missing,
    }


def self_test():
    good = ("'target' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
            "Build completed successfully (1 jobs).\n")
    cases = {
        "valid_log": inspect_log(good, 0, ["target"])["status"] == "PASS",
        "reject_missing_name": inspect_log(good, 0, ["targetExtra"])["status"] == "FAIL",
        "reject_extra_axiom": inspect_log(good.replace("Quot.sound", "Quot.sound, newAxiom"),
                                         0, ["target"])["status"] == "FAIL",
        "reject_sorry_axiom": inspect_log(good.replace("Quot.sound", "sorryAx"),
                                         0, ["target"])["status"] == "FAIL",
        "reject_error_with_footer": inspect_log(good + "error: bad\n", 0,
                                                ["target"])["status"] == "FAIL",
        "reject_nonzero_exit": inspect_log(good, 1, ["target"])["status"] == "FAIL",
        "reject_missing_footer": inspect_log(good.split("Build completed")[0],
                                              0, ["target"])["status"] == "FAIL",
    }
    if not all(cases.values()):
        raise RuntimeError(f"audit failure controls failed: {cases}")
    return cases


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    controls = self_test()
    if args.self_test:
        print(json.dumps(controls, indent=2))
        return 0
    root = Path(__file__).resolve().parents[1]
    command = ["lake", "build"] + ["ConnesWeilRH.Dev." + m for m in MODULES]
    build = subprocess.run(command, cwd=root, stdout=subprocess.PIPE,
                           stderr=subprocess.STDOUT, text=True, encoding="utf-8")
    results = root / "results"
    results.mkdir(exist_ok=True)
    (results / "3096_detector_parameter_build.log").write_text(build.stdout, encoding="utf-8")
    report = inspect_log(build.stdout, build.returncode, REQUIRED)
    report.update({
        "record": 3096,
        "modules": command[2:],
        "failure_controls": controls,
        "hash_convention": "SHA-256 of text sources with CRLF normalized to LF",
        "provenance": {
            name: hashlib.sha256((root / name).read_bytes().replace(b"\r\n", b"\n")).hexdigest()
            for name in SOURCES + ["scripts/detector_parameter_audit_3096.py"]
        },
        "scope": {
            "height": "Unit detection requires a height-dependent support/derivative budget.",
            "gap": "The actual raw factor has inverse-gap L1 cost at its opposite targets.",
            "row_b": "Fixed caps, poweredSeed transfer and rho-dependent gate duties remain open.",
            "D4_D7": "3071 arithmetic is audited; actual per-cell comparisons remain premises.",
            "RH": "No selected Weil nonnegativity or RH theorem is claimed.",
        },
    })
    (results / "3096_detector_parameter_audit.json").write_text(
        json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))
    return 0 if report["status"] == "PASS" else 1


if __name__ == "__main__":
    sys.exit(main())
