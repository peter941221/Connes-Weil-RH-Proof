"""Replay exact arithmetic invariants of the 3312 block manifest."""

from __future__ import annotations

import argparse
import json
import re
from fractions import Fraction as F
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def ceil_grid(value: F, places: int = 80) -> F:
    scale = 10**places
    numerator = value.numerator * scale
    return F(-((-numerator) // value.denominator), scale)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, default=ROOT / "results/3311_all_blocks.json")
    parser.add_argument("--manifest", type=Path, default=ROOT / "ConnesWeilRH/Dev/C1RouteARationalSignedJetBlockManifest3312.lean")
    args = parser.parse_args()
    payload = json.loads(args.input.read_text(encoding="utf-8"))
    rows = payload["rows"]
    failures: list[str] = []
    if payload.get("blocks") != 160 or len(rows) != 160:
        failures.append("expected exactly 160 block rows")
    rounded_sum = F(0)
    for expected_block, row in enumerate(rows):
        if row.get("block") != expected_block:
            failures.append(f"row {expected_block}: block index mismatch")
        source = F(row["source"])
        rounded = F(row["block_upper"])
        rounded_sum += rounded
        if rounded != ceil_grid(source):
            failures.append(f"block {expected_block}: upward rounding mismatch")
        if rounded < source:
            failures.append(f"block {expected_block}: rounded upper is inward")
    if rounded_sum != F(payload["upper_sum"]):
        failures.append("recorded upper_sum does not match row sum")
    manifest = args.manifest.read_text(encoding="utf-8")
    match = re.search(
        r"def\s+routeASignedJetRectBlockUpper3312\s*:\s*Fin\s+160\s*→\s*ℚ\s*:=\s*!\[(.*?)\]",
        manifest,
        flags=re.DOTALL,
    )
    if match is None:
        failures.append("Lean manifest vector not found")
    else:
        try:
            entries = [F(entry.strip()) for entry in match.group(1).split(",")]
        except ValueError:
            failures.append("Lean manifest contains an invalid rational literal")
        else:
            if len(entries) != 160:
                failures.append("Lean manifest must contain exactly 160 entries")
            for block, (entry, row) in enumerate(zip(entries, rows)):
                if entry != F(row["block_upper"]):
                    failures.append(f"block {block}: Lean manifest value mismatch")
    result = {
        "record": 3313,
        "status": "REPLAY_3312_MANIFEST_ARITHMETIC",
        "blocks": len(rows),
        "rounded_sum": str(rounded_sum),
        "recorded_upper_sum": payload["upper_sum"],
        "passed": not failures,
        "failures": failures,
        "arb_enclosure_proved": False,
        "rh_claim": False,
    }
    print(json.dumps(result, indent=2))
    if failures:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
