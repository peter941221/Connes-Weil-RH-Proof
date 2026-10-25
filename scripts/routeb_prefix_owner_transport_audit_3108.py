#!/usr/bin/env python3
"""Audit the conditional same-owner Route-B prefix transport brick."""

import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
MODULE = "ConnesWeilRH.Dev.C1RouteBPrefixOwnerTransport3108Audit"
REQUIRED = [
    "ConnesWeilRH.Source.C1RouteBPrefixOwnerTransport3108.package_hzero_prefix3108",
    "ConnesWeilRH.Source.C1RouteBPrefixOwnerTransport3108.package_rowBSpanPrefix3108",
]
SOURCES = [
    "ConnesWeilRH/Dev/C1RouteBPrefixOwnerTransport3108.lean",
    "ConnesWeilRH/Dev/C1RouteBPrefixOwnerTransport3108Audit.lean",
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
        "status": "PASS" if run.returncode == 0 and footer and
                  not re.search(r"^error:", log, re.M) and
                  "sorryAx" not in log and not missing and not unexpected
                  else "FAIL",
        "build_returncode": run.returncode,
        "build_jobs": int(footer.group(1)) if footer else None,
        "error_lines_present": bool(re.search(r"^error:", log, re.M)),
        "sorryAx_present": "sorryAx" in log,
        "required_theorems": {name: decl.get(name) for name in REQUIRED},
        "missing_required_theorems": missing,
        "unexpected_axioms": unexpected,
        "record": 3108,
        "module": MODULE,
        "provenance": {name: digest(ROOT / name) for name in SOURCES},
        "scope": (
            "Conditional same-owner hzero and row-B prefix transport under "
            "tailStart >= 5. The current OrbitG8Geometry budget does not "
            "prove that lower bound unconditionally."
        ),
    }
    (ROOT / "results/3108_routeb_prefix_owner_transport_audit.json").write_text(
        json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: report[key] for key in
                      ("status", "build_jobs", "error_lines_present",
                       "sorryAx_present")}, indent=2))
    return 0 if report["status"] == "PASS" else 1


if __name__ == "__main__":
    sys.exit(main())
