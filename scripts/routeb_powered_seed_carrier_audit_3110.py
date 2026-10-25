#!/usr/bin/env python3
"""Audit the powered-seed Route-B carrier transport brick."""

import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
MODULE = "ConnesWeilRH.Dev.C1RouteBPoweredSeedCarrier3110Audit"
REQUIRED = [
    "ConnesWeilRH.Source.C1RouteBPoweredSeedCarrier3110.poweredSeedCarrier_target3110",
    "ConnesWeilRH.Source.C1RouteBPoweredSeedCarrier3110.poweredSeedCarrier_cc20Vanishes3110",
    "ConnesWeilRH.Source.C1RouteBPoweredSeedCarrier3110.poweredSeedCarrier_sourceTest_support3110",
    "ConnesWeilRH.Source.C1RouteBPoweredSeedCarrier3110.fourPointContradictionRowBPoweredSeed3110",
    "ConnesWeilRH.Source.C1RouteBPoweredSeedCarrier3110.poweredSeedStoredCarrierSourceTest3110",
    "ConnesWeilRH.Source.C1RouteBPoweredSeedCarrier3110.fourPointContradictionRowBPoweredSeedStored3110",
]
SOURCES = [
    "ConnesWeilRH/Dev/C1RouteBPoweredSeedCarrier3110.lean",
    "ConnesWeilRH/Dev/C1RouteBPoweredSeedCarrier3110Audit.lean",
]


def digest(path):
    return hashlib.sha256(path.read_bytes().replace(b"\r\n", b"\n")).hexdigest()


def main():
    run = subprocess.run(["lake", "build", MODULE], cwd=ROOT,
                         stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                         text=True, encoding="utf-8")
    log = run.stdout
    decl = {
        name: [a.strip() for a in axioms.split(",") if a.strip()]
        for name, axioms in re.findall(
            r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", log)
    }
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    footer = re.search(r"Build completed successfully \((\d+) jobs?\)", log)
    missing = [name for name in REQUIRED if name not in decl]
    unexpected = {name: axioms for name, axioms in decl.items()
                  if name in REQUIRED and set(axioms) != allowed}
    report = {
        "status": "PASS" if run.returncode == 0 and footer
        and not re.search(r"^error:", log, re.M)
        and "sorryAx" not in log and not missing and not unexpected else "FAIL",
        "build_returncode": run.returncode,
        "build_jobs": int(footer.group(1)) if footer else None,
        "error_lines_present": bool(re.search(r"^error:", log, re.M)),
        "sorryAx_present": "sorryAx" in log,
        "required_theorems": {name: decl.get(name) for name in REQUIRED},
        "missing_required_theorems": missing,
        "unexpected_axioms": unexpected,
        "record": 3110,
        "module": MODULE,
        "provenance": {name: digest(ROOT / name) for name in SOURCES},
        "scope": (
            "Rebuilds the row-B finite carrier at poweredSeed, proving "
            "interpolation, CC20 vanishing, support, and the contradiction "
            "interface while leaving cardinal pins, gate, and prefix explicit."
        ),
    }
    out = ROOT / "results/3110_routeb_powered_seed_carrier_audit.json"
    out.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: report[key] for key in
                      ("status", "build_jobs", "error_lines_present",
                       "sorryAx_present")}, indent=2))
    return 0 if report["status"] == "PASS" else 1


if __name__ == "__main__":
    sys.exit(main())
