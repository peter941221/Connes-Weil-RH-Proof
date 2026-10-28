#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import json
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MODULE = "ConnesWeilRH.Dev.C1RouteBAdaptiveOwnerReadback3137Audit"
THEOREMS = [
    "ConnesWeilRH.Source.C1RouteBAdaptiveOwnerReadback3137.poweredFamilyOwner_identity3137",
    "ConnesWeilRH.Source.C1RouteBAdaptiveOwnerReadback3137.poweredFamily_globalPrimeIndexSet_mem_iff3137",
    "ConnesWeilRH.Source.C1RouteBAdaptiveOwnerReadback3137.poweredFamily_globalPrimeIndexSet_selected3137",
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
            found[name] = {
                part.strip() for part in axioms_text.split(",") if part.strip()
            }
    footer = re.search(r"Build completed successfully \((\d+) jobs?\)", output)
    status = (
        run.returncode == 0 and footer is not None and len(found) == len(THEOREMS)
        and all(axioms == ALLOWED for axioms in found.values())
        and "error:" not in output and "sorryAx" not in output
    )
    report = {
        "record": 3137,
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
            "ConnesWeilRH/Dev/C1RouteBAdaptiveOwnerReadback3137.lean": digest(
                ROOT / "ConnesWeilRH/Dev/C1RouteBAdaptiveOwnerReadback3137.lean"
            ),
            "ConnesWeilRH/Dev/C1RouteBAdaptiveOwnerReadback3137Audit.lean": digest(
                ROOT / "ConnesWeilRH/Dev/C1RouteBAdaptiveOwnerReadback3137Audit.lean"
            ),
        },
        "scope": "Exact 3117 powered-owner identity and prime-power index-set readback only; no numerical manifest, gate margin, Producer GO, SourceRH, or RH claim.",
    }
    out = ROOT / "results/3137_routeb_adaptive_owner_readback_audit.json"
    out.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))
    return 0 if status else 1


if __name__ == "__main__":
    raise SystemExit(main())
