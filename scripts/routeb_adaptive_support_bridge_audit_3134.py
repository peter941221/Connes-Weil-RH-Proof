#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import json
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MODULE = "ConnesWeilRH.Dev.C1RouteBAdaptiveSupportBridge3134Audit"
THEOREMS = [
    "ConnesWeilRH.Source.C1RouteBAdaptiveSupportBridge3134.poweredFamilyOwner_support3134",
    "ConnesWeilRH.Source.C1RouteBAdaptiveSupportBridge3134.poweredFamily_gate_bridge3134",
    "ConnesWeilRH.Source.C1RouteBAdaptiveSupportBridge3134.negative_powered_owner_rejects_gate3134",
    "ConnesWeilRH.Source.C1RouteBAdaptiveSupportBridge3134.exists_eventual_powered_owner_rejects_gate3135",
]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes().replace(b"\r\n", b"\n")).hexdigest()


def main() -> int:
    run = subprocess.run(
        ["lake", "build", MODULE], cwd=ROOT, text=True,
        encoding="utf-8", errors="replace", stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT, check=False,
    )
    output = run.stdout or ""
    found = {}
    for name, axioms_text in re.findall(
        r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", output
    ):
        if name in THEOREMS:
            found[name] = {part.strip() for part in axioms_text.split(",") if part.strip()}
    footer = re.search(r"Build completed successfully \((\d+) jobs?\)", output)
    status = (
        run.returncode == 0 and footer is not None and len(found) == len(THEOREMS)
        and all(axioms == ALLOWED for axioms in found.values())
        and "error:" not in output and "sorryAx" not in output
    )
    report = {
        "record": 3134,
        "status": "PASS" if status else "FAIL",
        "module": MODULE,
        "build_jobs": int(footer.group(1)) if footer else None,
        "returncode": run.returncode,
        "theorems_found": sorted(found),
        "axioms": {name: sorted(axioms) for name, axioms in found.items()},
        "unexpected_axioms": {
            name: sorted(axioms - ALLOWED) for name, axioms in found.items()
        },
        "error_lines_present": "error:" in output,
        "sorryAx_present": "sorryAx" in output,
        "provenance": {
            "ConnesWeilRH/Dev/C1RouteBVariableLambdaGate3130.lean": digest(
                ROOT / "ConnesWeilRH/Dev/C1RouteBVariableLambdaGate3130.lean"
            ),
            "ConnesWeilRH/Dev/C1RouteBAdaptiveSupportBridge3134.lean": digest(
                ROOT / "ConnesWeilRH/Dev/C1RouteBAdaptiveSupportBridge3134.lean"
            ),
            "ConnesWeilRH/Dev/C1RouteBAdaptiveSupportBridge3134Audit.lean": digest(
                ROOT / "ConnesWeilRH/Dev/C1RouteBAdaptiveSupportBridge3134Audit.lean"
            ),
        },
        "scope": "Actual 3117 powered-owner support bridge, eventual negative-span composition, and logical gate rejection only; no numerical gate margin, Producer GO, SourceRH, or RH claim.",
    }
    out = ROOT / "results/3134_routeb_adaptive_support_bridge_audit.json"
    out.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))
    return 0 if status else 1


if __name__ == "__main__":
    raise SystemExit(main())
