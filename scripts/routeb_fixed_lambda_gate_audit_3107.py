#!/usr/bin/env python3
"""Audit the Route-B fixed-lambda=24 gate adapter."""

import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
MODULE = "ConnesWeilRH.Dev.C1RouteBFixedLambdaGate3107Audit"
REQUIRED = [
    "ConnesWeilRH.Source.C1RouteBFixedLambdaGate3107.hgate24Predicate3107_iff_gate_qform",
    "ConnesWeilRH.Source.C1RouteBFixedLambdaGate3107.hgate24Predicate3107_iff_signed_margin",
    "ConnesWeilRH.Source.C1RouteBFixedLambdaGate3107.hgate24Predicate3107_iff_owner_gate",
    "ConnesWeilRH.Source.C1RouteBFixedLambdaGate3107.fixed_lambda24_not_implied_by_discriminant3107",
]
SOURCES = [
    "ConnesWeilRH/Dev/C1RouteBFixedLambdaGate3107.lean",
    "ConnesWeilRH/Dev/C1RouteBFixedLambdaGate3107Audit.lean",
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
                  if name in REQUIRED and set(axioms) != allowed}
    footer = re.search(r"Build completed successfully \((\d+) jobs?\)", log)
    errors = bool(re.search(r"^error:", log, re.MULTILINE))
    passed = code == 0 and footer is not None and not errors and "sorryAx" not in log \
        and not missing and not unexpected
    return {
        "status": "PASS" if passed else "FAIL",
        "build_returncode": code,
        "build_jobs": int(footer.group(1)) if footer else None,
        "error_lines_present": errors,
        "sorryAx_present": "sorryAx" in log,
        "required_theorems": {name: decl.get(name) for name in REQUIRED},
        "missing_required_theorems": missing,
        "unexpected_axioms": unexpected,
    }


def main():
    run = subprocess.run(["lake", "build", MODULE], cwd=ROOT,
                         stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                         text=True, encoding="utf-8")
    report = inspect(run.stdout, run.returncode)
    report.update({
        "record": 3107,
        "module": MODULE,
        "provenance": {name: digest(ROOT / name) for name in SOURCES},
        "scope": (
            "Fixed lambda=24 is connected to the same-owner gate matrix and "
            "semi-local gate. No signed numerical margin or RH conclusion is "
            "claimed; the formal scalar counterexample blocks the invalid "
            "existential-lambda-to-24 inference."
        ),
    })
    results = ROOT / "results"
    results.mkdir(exist_ok=True)
    (results / "3107_routeb_fixed_lambda_gate_audit.json").write_text(
        json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: report[key] for key in
                      ("status", "build_jobs", "error_lines_present",
                       "sorryAx_present")}, indent=2))
    return 0 if report["status"] == "PASS" else 1


if __name__ == "__main__":
    sys.exit(main())
