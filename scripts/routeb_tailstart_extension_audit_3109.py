#!/usr/bin/env python3
"""Audit the 3109 tail-index extension and same-owner prefix transport."""

import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
MODULES = [
    "ConnesWeilRH.Dev.C1G8R0OrbitGeometryAudit",
    "ConnesWeilRH.Dev.C1RouteBPrefixOwnerTransport3108Audit",
]
REQUIRED = [
    "ConnesWeilRH.Source.C1G8R0OrbitGeometry.exists_orbitG8Geometry_of_sourceNontrivialZero_right_tailStart_ge_five",
    "ConnesWeilRH.Source.C1RouteBPrefixOwnerTransport3108.exists_rhoOwnerPackage_tailStart_ge_five3108",
    "ConnesWeilRH.Source.C1RouteBPrefixOwnerTransport3108.exists_rowBSpanPrefix_owner3108",
    "ConnesWeilRH.Source.C1RouteBPrefixOwnerTransport3108.package_rowBSpanPrefix3108",
]
SOURCES = [
    "ConnesWeilRH/Dev/C1G8R0OrbitGeometry.lean",
    "ConnesWeilRH/Dev/C1G8R0OrbitGeometryAudit.lean",
    "ConnesWeilRH/Dev/C1RouteBPrefixOwnerTransport3108.lean",
    "ConnesWeilRH/Dev/C1RouteBPrefixOwnerTransport3108Audit.lean",
]


def digest(path):
    return hashlib.sha256(path.read_bytes().replace(b"\r\n", b"\n")).hexdigest()


def main():
    logs = []
    rc = 0
    for module in MODULES:
        run = subprocess.run(["lake", "build", module], cwd=ROOT,
                             stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                             text=True, encoding="utf-8")
        logs.append(run.stdout)
        rc = rc or run.returncode
    log = "\n".join(logs)
    decl = {
        name: [a.strip() for a in axioms.split(",") if a.strip()]
        for name, axioms in re.findall(
            r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", log)
    }
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    jobs = [int(x) for x in re.findall(r"Build completed successfully \((\d+) jobs?\)", log)]
    missing = [name for name in REQUIRED if name not in decl]
    unexpected = {name: axioms for name, axioms in decl.items()
                  if name in REQUIRED and set(axioms) != allowed}
    report = {
        "status": "PASS" if rc == 0 and not re.search(r"^error:", log, re.M)
        and "sorryAx" not in log and not missing and not unexpected else "FAIL",
        "build_returncode": rc,
        "build_jobs": jobs,
        "error_lines_present": bool(re.search(r"^error:", log, re.M)),
        "sorryAx_present": "sorryAx" in log,
        "required_theorems": {name: decl.get(name) for name in REQUIRED},
        "missing_required_theorems": missing,
        "unexpected_axioms": unexpected,
        "record": 3109,
        "modules": MODULES,
        "provenance": {name: digest(ROOT / name) for name in SOURCES},
        "scope": (
            "The G8 owner construction raises its own tail index to max 5 "
            "tailStart, rebuilding the enlarged closed-ball certificate; "
            "the same owner then supplies the row-B prefix."
        ),
    }
    out = ROOT / "results/3109_routeb_tailstart_extension_audit.json"
    out.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: report[key] for key in
                      ("status", "build_returncode", "build_jobs",
                       "error_lines_present", "sorryAx_present")}, indent=2))
    return 0 if report["status"] == "PASS" else 1


if __name__ == "__main__":
    sys.exit(main())
