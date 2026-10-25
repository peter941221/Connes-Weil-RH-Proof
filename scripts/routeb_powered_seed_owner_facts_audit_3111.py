#!/usr/bin/env python3
"""Audit record 3111's source and Lean axiom output.

The checker is intentionally small: Lean is the proof checker, while this
script verifies that the expected declarations were printed, no error or
sorryAx was emitted, and the source files are present. It does not replace
kernel checking.
"""

from __future__ import annotations

import hashlib
import json
import re
import shlex
import subprocess
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
DEV = ROOT / "ConnesWeilRH" / "Dev"
SOURCE = DEV / "C1RouteBPoweredSeedOwnerFacts3111.lean"
AUDIT = DEV / "C1RouteBPoweredSeedOwnerFacts3111Audit.lean"
MODULE = "ConnesWeilRH.Dev.C1RouteBPoweredSeedOwnerFacts3111Audit"
EXPECTED = [
    "poweredSeedExplicitOwner_target3111",
    "poweredSeedExplicitOwner_square_zero3111",
    "poweredSeedExplicitOwner_minimal3111",
    "poweredSeedExplicitOwner_centeredOrbit_sum3111",
    "poweredSeedExplicitOwner_support3111",
]


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> int:
    missing = [str(p.relative_to(ROOT)) for p in (SOURCE, AUDIT) if not p.exists()]
    if missing:
        print(json.dumps({"status": "FAIL", "missing": missing}, indent=2))
        return 1

    import os

    verify_root = os.environ.get("RH_VERIFY_ROOT")
    if not verify_root:
        print(json.dumps({
            "status": "FAIL",
            "reason": "set RH_VERIFY_ROOT to the Linux ext4 verification mirror",
        }, indent=2))
        return 1
    proc = subprocess.run(
        ["wsl.exe", "bash", "-lc", (
            "cd " + shlex.quote(verify_root) + " && "
            "LEAN_NUM_THREADS=1 lake build " +
            "ConnesWeilRH.Dev.C1RouteBPoweredSeedOwnerFacts3111 " +
            "ConnesWeilRH.Dev.C1RouteBPoweredSeedOwnerFacts3111Audit"
        )],
        cwd=ROOT,
        text=True,
        encoding="utf-8",
        errors="replace",
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )
    output = proc.stdout or ""
    declarations = {name: name in output for name in EXPECTED}
    axiom_blocks = re.findall(
        r"depends on axioms:\s*\[([^\]]+)\]", output, flags=re.S)
    axiom_lines = ["[" + block.replace("\n", " ").strip() + "]"
                   for block in axiom_blocks]
    allowed_axioms = {"propext", "Classical.choice", "Quot.sound"}
    axiom_ok = len(axiom_blocks) == len(EXPECTED)
    if axiom_ok:
        for block in axiom_blocks:
            seen = {part.strip() for part in block.split(",")}
            axiom_ok = axiom_ok and seen == allowed_axioms
    ok = (
        proc.returncode == 0
        and all(declarations.values())
        and "error:" not in output
        and "sorryAx" not in output
        and axiom_ok
    )
    artifact = {
        "record": 3111,
        "status": "PASS" if ok else "FAIL",
        "module": MODULE,
        "source_sha256": sha256(SOURCE),
        "audit_sha256": sha256(AUDIT),
        "declarations": declarations,
        "axiom_lines": axiom_lines,
        "exit_code": proc.returncode,
        "build_footer": "Build completed successfully" in output,
    }
    out = ROOT / "results" / "3111_routeb_powered_seed_owner_facts_audit.json"
    out.write_text(json.dumps(artifact, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(artifact, indent=2))
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
