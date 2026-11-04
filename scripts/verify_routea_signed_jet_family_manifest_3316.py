"""Replay the exact arithmetic of the compact 3316 family manifest."""

from __future__ import annotations

import argparse
import json
from fractions import Fraction as F
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def ceil_grid(value: F, places: int = 80) -> F:
    scale = 10**places
    numerator = value.numerator * scale
    return F(-((-numerator) // value.denominator), scale)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("manifest", type=Path)
    args = parser.parse_args()
    payload = json.loads(args.manifest.read_text(encoding="utf-8"))
    rows = payload["rows"]
    failures: list[str] = []
    if payload.get("blocks") != 160 or len(rows) != 160:
        failures.append("expected exactly 160 block rows")
    upper_sum = F(0)
    for block, row in enumerate(rows):
        if row.get("block") != block:
            failures.append(f"block {block}: index mismatch")
        if len(row["second_family_sum"]) != 30:
            failures.append(f"block {block}: second family count mismatch")
        if len(row["fourth_family_sum"]) != 30:
            failures.append(f"block {block}: fourth family count mismatch")
        step = F(row["step"])
        endpoint = F(row["endpoint_sum"])
        second = step**3 * sum((F(value) for value in row["second_family_sum"]), F(0)) / 24
        fourth = step**5 * sum((F(value) for value in row["fourth_family_sum"]), F(0)) / 1920
        sixth = F(row["sixth_sum"])
        if second != F(row["second_sum"]):
            failures.append(f"block {block}: second sum mismatch")
        if fourth != F(row["fourth_sum"]):
            failures.append(f"block {block}: fourth sum mismatch")
        source = endpoint + second + fourth + sixth
        if source != F(row["source"]):
            failures.append(f"block {block}: source mismatch")
        if F(row["block_upper"]) != ceil_grid(source):
            failures.append(f"block {block}: upward rounding mismatch")
        if F(row["block_upper"]) < source:
            failures.append(f"block {block}: inward upper")
        if F(row["block_upper"]) > F(row["previous_3311_block_upper"]):
            failures.append(f"block {block}: family upper exceeds 3311 upper")
        upper_sum += F(row["block_upper"])
    if upper_sum != F(payload["upper_sum"]):
        failures.append("aggregate upper_sum mismatch")
    if payload.get("arb_enclosure_proved") is not False:
        failures.append("manifest must not claim Arb enclosure proof")
    result = {
        "record": 3316,
        "status": "REPLAY_3316_FAMILY_AGGREGATED_CERTIFICATE",
        "blocks": len(rows),
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
