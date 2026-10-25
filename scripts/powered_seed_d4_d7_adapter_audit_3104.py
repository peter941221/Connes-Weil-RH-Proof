#!/usr/bin/env python3
"""Audit the premise-free D4/D7 poweredSeed envelope adapter."""

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
MODULE = "ConnesWeilRH.Dev.C1PoweredSeedD4D7Adapter3104Audit"
REQUIRED = [
    "ConnesWeilRH.Dev.C1PoweredSeedD4D7Adapter3104.d4d7Rungs_nonempty3104",
    "ConnesWeilRH.Dev.C1PoweredSeedD4D7Adapter3104.d4d7D_nonneg3104",
    "ConnesWeilRH.Dev.C1PoweredSeedD4D7Adapter3104.d4d7D_bound3104",
    "ConnesWeilRH.Dev.C1PoweredSeedD4D7Adapter3104.norm_cardinalSum_poweredSeed_le_d4d7_env3104",
]
ANALYTIC = {
    REQUIRED[2],
    REQUIRED[3],
}
SOURCES = [
    "ConnesWeilRH/Dev/C1PoweredSeedD4D7Adapter3104.lean",
    "ConnesWeilRH/Dev/C1PoweredSeedD4D7Adapter3104Audit.lean",
]


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes().replace(b"\r\n", b"\n")).hexdigest()


def inspect(log: str, code: int) -> dict:
    declarations = {
        name: [item.strip() for item in axioms.split(",") if item.strip()]
        for name, axioms in re.findall(
            r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", log)
    }
    required = {name: declarations.get(name) for name in REQUIRED}
    missing = [name for name, axioms in required.items() if axioms is None]
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    unexpected = {
        name: axioms for name, axioms in declarations.items()
        if not set(axioms) <= allowed
        or (name in ANALYTIC and set(axioms) != allowed)
    }
    footer = re.search(r"Build completed successfully \((\d+) jobs?\)", log)
    errors = bool(re.search(r"^error:", log, re.MULTILINE))
    passed = (code == 0 and footer is not None and not errors
              and "sorryAx" not in log and not missing and not unexpected)
    return {
        "status": "PASS" if passed else "FAIL",
        "build_returncode": code,
        "build_jobs": int(footer.group(1)) if footer else None,
        "error_lines_present": errors,
        "sorryAx_present": "sorryAx" in log,
        "required_theorems": required,
        "unexpected_axioms": unexpected,
        "missing_required_theorems": missing,
    }


def self_test() -> dict:
    good = "".join(
        f"'{name}' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
        for name in REQUIRED
    ) + "Build completed successfully (1 jobs).\n"
    cases = {
        "accept_good": inspect(good, 0)["status"] == "PASS",
        "reject_error": inspect(good + "error: bad\n", 0)["status"] == "FAIL",
        "reject_sorry": inspect(good + "sorryAx\n", 0)["status"] == "FAIL",
        "reject_exit": inspect(good, 1)["status"] == "FAIL",
    }
    if not all(cases.values()):
        raise RuntimeError(cases)
    return cases


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    controls = self_test()
    if args.self_test:
        print(json.dumps(controls, indent=2))
        return 0
    run = subprocess.run(["lake", "build", MODULE], cwd=ROOT,
                         stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                         text=True, encoding="utf-8")
    report = inspect(run.stdout, run.returncode)
    report.update({
        "record": 3104,
        "module": MODULE,
        "failure_controls": controls,
        "provenance": {name: digest(ROOT / name) for name in SOURCES},
        "scope": "Actual smoothSeed mass and D4/D7 bounds are instantiated in the poweredSeed envelope; numerical cardinal pins, carrier transfer, rho duties and RH remain open.",
    })
    results = ROOT / "results"
    results.mkdir(exist_ok=True)
    (results / "3104_powered_seed_d4_d7_adapter_audit.json").write_text(
        json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: report[key] for key in
                      ("status", "build_jobs", "error_lines_present", "sorryAx_present")},
                     indent=2))
    return 0 if report["status"] == "PASS" else 1


if __name__ == "__main__":
    sys.exit(main())
