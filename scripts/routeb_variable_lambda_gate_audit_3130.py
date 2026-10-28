#!/usr/bin/env python3
"""Audit the variable-lambda same-owner gate adapter (record 3130)."""

from __future__ import annotations

import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
MODULE = "ConnesWeilRH.Dev.C1RouteBVariableLambdaGate3130Audit"
SOURCES = [
    "ConnesWeilRH/Dev/C1RouteBVariableLambdaGate3130.lean",
    "ConnesWeilRH/Dev/C1RouteBVariableLambdaGate3130Audit.lean",
]
REQUIRED = [
    "ConnesWeilRH.Source.C1RouteBVariableLambdaGate3130."
    "variableLambdaGatePredicate3130_iff_gate_qform",
    "ConnesWeilRH.Source.C1RouteBVariableLambdaGate3130."
    "variableLambdaGatePredicate3130_iff_signed_margin",
    "ConnesWeilRH.Source.C1RouteBVariableLambdaGate3130."
    "variableLambdaGatePredicate3130_iff_owner_gate",
]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes().replace(b"\r\n", b"\n")).hexdigest()


def main() -> int:
    missing = [path for path in SOURCES if not (ROOT / path).exists()]
    if missing:
        print(json.dumps({"record": 3130, "status": "FAIL", "missing": missing}, indent=2))
        return 1

    run = subprocess.run(
        ["lake", "build", MODULE],
        cwd=ROOT,
        text=True,
        encoding="utf-8",
        errors="replace",
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )
    output = run.stdout or ""
    blocks = {
        name: {part.strip() for part in axioms.split(",") if part.strip()}
        for name, axioms in re.findall(
            r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", output
        )
    }
    missing_theorems = [name for name in REQUIRED if name not in blocks]
    unexpected = {
        name: sorted(blocks[name])
        for name in REQUIRED
        if name in blocks and blocks[name] != ALLOWED
    }
    footer = re.search(r"Build completed successfully \((\d+) jobs?\)", output)
    ok = (
        run.returncode == 0
        and footer is not None
        and not missing_theorems
        and not unexpected
        and "error:" not in output
        and "sorryAx" not in output
    )
    report = {
        "record": 3130,
        "status": "PASS" if ok else "FAIL",
        "module": MODULE,
        "build_jobs": int(footer.group(1)) if footer else None,
        "returncode": run.returncode,
        "missing_theorems": missing_theorems,
        "unexpected_axioms": unexpected,
        "error_lines_present": "error:" in output,
        "sorryAx_present": "sorryAx" in output,
        "provenance": {path: digest(ROOT / path) for path in SOURCES},
        "scope": (
            "Arbitrary real lambda is connected to the same-owner gate matrix, "
            "signed margin, and owner-local semi-local gate. No numerical gate "
            "margin, owner manifest, tail budget, Producer GO, or RH claim."
        ),
    }
    out = ROOT / "results" / "3130_routeb_variable_lambda_gate_audit.json"
    out.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
