"""3205: exact replay audit for the concrete-owner Taylor-6 JSONL."""

from __future__ import annotations

import argparse
import json
from fractions import Fraction as F
from pathlib import Path

DECIMAL_PLACES = 80
DECIMAL_SCALE = 10**DECIMAL_PLACES
RADIUS = F(65536001, 10000000)


def ceil_grid(value: F) -> F:
    numerator = value.numerator * DECIMAL_SCALE
    return F(-((-numerator) // value.denominator), DECIMAL_SCALE)


def audit(main_path: Path, cells_path: Path) -> dict:
    main = json.loads(main_path.read_text(encoding="utf-8"))
    lines = cells_path.read_text(encoding="utf-8").splitlines()
    header = json.loads(lines[0])
    expected_cells = int(main["cells"])
    if len(lines) != expected_cells + 1:
        raise ValueError("JSONL line count mismatch")
    if header.get("format") != "3204-concrete-owner-taylor6-jsonl-v1":
        raise ValueError("unexpected 3204 JSONL format")
    rows = [json.loads(line) for line in lines[1:]]
    expected_step = F(2 * RADIUS, expected_cells)
    cell_sum = F(0)
    remainder_sum = F(0)
    previous_right = None
    rounded_fields = 0
    for expected_index, row in enumerate(rows):
        if row["index"] != expected_index:
            raise ValueError(f"index mismatch at {expected_index}")
        left, right, midpoint, step = map(F, (row["left"], row["right"], row["midpoint"], row["step"]))
        if step != expected_step or right - left != expected_step:
            raise ValueError(f"step mismatch at {expected_index}")
        if midpoint != (left + right) / 2:
            raise ValueError(f"midpoint mismatch at {expected_index}")
        if previous_right is not None and left != previous_right:
            raise ValueError(f"grid discontinuity at {expected_index}")
        previous_right = right
        value_upper, second_upper, fourth_upper, sixth_upper = map(
            F, (row["value_upper"], row["second_upper"], row["fourth_upper"], row["sixth_upper"])
        )
        cell_upper = F(row["cell_upper"])
        remainder_upper = F(row["sixth_order_remainder_upper"])
        expected_cell = step * value_upper + step**3 * second_upper / 24 + step**5 * fourth_upper / 1920 + step**7 * sixth_upper / 322560
        expected_remainder = step**7 * sixth_upper / 322560
        if cell_upper != expected_cell or remainder_upper != expected_remainder:
            raise ValueError(f"Taylor formula mismatch at {expected_index}")
        for value in (value_upper, second_upper, fourth_upper, sixth_upper):
            if value != ceil_grid(value):
                raise ValueError(f"rounding grid mismatch at {expected_index}")
            rounded_fields += 1
        cell_sum += cell_upper
        remainder_sum += remainder_upper
    if previous_right != RADIUS or F(rows[0]["left"]) != -RADIUS:
        raise ValueError("grid coverage mismatch")
    if cell_sum != F(main["total_upper"]):
        raise ValueError("aggregate total mismatch")
    if remainder_sum != F(main["sixth_order_remainder_upper"]):
        raise ValueError("aggregate remainder mismatch")
    return {
        "record": 3205,
        "status": "PASS",
        "source_record": 3204,
        "cells": expected_cells,
        "formula_rows": len(rows),
        "rounded_fields": rounded_fields,
        "grid_continuous": True,
        "formula_replay_exact": True,
        "aggregate_replay_exact": True,
        "concrete_owner_source": main["coefficient_source"],
        "total_upper_negative": bool(main["total_upper_negative"]),
        "nonclaims": ["not imported into Lean", "full-line tail missing", "no producer GO", "no SourceRH", "no RH"],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--main", type=Path, default=Path("results/3204_concrete_owner_taylor6.json"))
    parser.add_argument("--cells", type=Path, default=Path("results/3204_concrete_owner_taylor6_40960.jsonl"))
    parser.add_argument("--output", type=Path, default=Path("results/3205_concrete_owner_taylor6_jsonl_audit.json"))
    args = parser.parse_args()
    result = audit(args.main, args.cells)
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()