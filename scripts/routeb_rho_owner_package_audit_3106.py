#!/usr/bin/env python3
"""Audit the same-owner rho-dependent Route-B package."""

import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
MODULE = "ConnesWeilRH.Dev.C1RouteBRhoOwnerPackage3106Audit"
REQUIRED = [
    "ConnesWeilRH.Source.C1RouteBRhoOwnerPackage3106.exists_rhoOwnerPackage3106",
    "ConnesWeilRH.Source.C1RouteBRhoOwnerPackage3106.package_same_owner_test3106",
    "ConnesWeilRH.Source.C1RouteBRhoOwnerPackage3106.package_source_orbit_target3106",
    "ConnesWeilRH.Source.C1RouteBRhoOwnerPackage3106.package_support_bound3106",
    "ConnesWeilRH.Source.C1RouteBRhoOwnerPackage3106.package_height_cost3106",
    "ConnesWeilRH.Source.C1RouteBRhoOwnerPackage3106.package_inverse_gap_cost3106",
    "ConnesWeilRH.Source.C1RouteBRhoOwnerPackage3106.package_has_healthy_data3106",
]
SOURCES = [
    "ConnesWeilRH/Dev/C1RouteBRhoOwnerPackage3106.lean",
    "ConnesWeilRH/Dev/C1RouteBRhoOwnerPackage3106Audit.lean",
]


def digest(path):
    return hashlib.sha256(path.read_bytes().replace(b"\r\n", b"\n")).hexdigest()


def inspect(log, code):
    decl = {
        name: [a.strip() for a in axioms.split(",") if a.strip()]
        for name, axioms in re.findall(
            r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", log)
    }
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    missing = [name for name in REQUIRED if name not in decl]
    unexpected = {name: axioms for name, axioms in decl.items()
                  if set(axioms) != allowed}
    footer = re.search(r"Build completed successfully \((\d+) jobs?\)", log)
    errors = bool(re.search(r"^error:", log, re.MULTILINE))
    passed = code == 0 and footer is not None and not errors and "sorryAx" not in log \
        and not missing and not unexpected
    return {"status": "PASS" if passed else "FAIL", "build_returncode": code,
            "build_jobs": int(footer.group(1)) if footer else None,
            "error_lines_present": errors, "sorryAx_present": "sorryAx" in log,
            "required_theorems": {name: decl.get(name) for name in REQUIRED},
            "missing_required_theorems": missing, "unexpected_axioms": unexpected}


def main():
    run = subprocess.run(["lake", "build", MODULE], cwd=ROOT,
                         stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                         text=True, encoding="utf-8")
    report = inspect(run.stdout, run.returncode)
    report.update({
        "record": 3106,
        "module": MODULE,
        "provenance": {name: digest(ROOT / name) for name in SOURCES},
        "scope": "Same-owner rho-dependent geometry, target transport, support and necessary costs; hgate24, cardinal pins, universal caps and RH remain open.",
    })
    results = ROOT / "results"
    results.mkdir(exist_ok=True)
    (results / "3106_routeb_rho_owner_package_audit.json").write_text(
        json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: report[key] for key in
                      ("status", "build_jobs", "error_lines_present", "sorryAx_present")},
                     indent=2))
    return 0 if report["status"] == "PASS" else 1


if __name__ == "__main__":
    sys.exit(main())
