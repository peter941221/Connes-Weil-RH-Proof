"""Replay and audit the 3238 weighted-original 40960-cell sidecar."""

from __future__ import annotations

import argparse
import json
from fractions import Fraction as F
from pathlib import Path

DECIMAL_SCALE = 10**80
RADIUS = F(65536001, 10000000)


def ceil_grid(value: F) -> F:
    numerator = value.numerator * DECIMAL_SCALE
    return F(-((-numerator) // value.denominator), DECIMAL_SCALE)


def audit(main_path: Path, cells_path: Path) -> dict:
    main = json.loads(main_path.read_text(encoding="utf-8"))
    lines = cells_path.read_text(encoding="utf-8").splitlines()
    if not lines:
        raise ValueError("cell sidecar is empty")
    header = json.loads(lines[0])
    expected_cells = int(main["cells"])
    if len(lines) != expected_cells + 1:
        raise ValueError(f"expected {expected_cells + 1} lines, got {len(lines)}")
    if header.get("format") != "3238-weighted-original-cell-upper-jsonl-v1":
        raise ValueError("unexpected JSONL format")
    if header.get("rounding") != "every serialized upper is rounded upward to the 10^-80 grid":
        raise ValueError("rounding policy is missing or changed")

    expected_step = 2 * RADIUS / expected_cells
    cell_sum = F(0)
    remainder_sum = F(0)
    previous_right = None
    minimum = None

    for expected_index, line in enumerate(lines[1:]):
        row = json.loads(line)
        if row.get("index") != expected_index:
            raise ValueError(f"index mismatch at row {expected_index}")
        left = F(row["left"])
        right = F(row["right"])
        midpoint = F(row["midpoint"])
        step = F(row["step"])
        if step != expected_step or right - left != expected_step:
            raise ValueError(f"grid step mismatch at row {expected_index}")
        if midpoint != (left + right) / 2:
            raise ValueError(f"midpoint mismatch at row {expected_index}")
        if previous_right is not None and left != previous_right:
            raise ValueError(f"grid discontinuity before row {expected_index}")
        previous_right = right

        value_upper = F(row["value_upper"])
        second_upper = F(row["second_upper"])
        fourth_upper = F(row["fourth_upper"])
        sixth_upper = F(row["sixth_upper"])
        cell_upper = F(row["cell_upper"])
        remainder_upper = F(row["sixth_order_remainder_upper"])
        expected_cell_upper = (
            step * value_upper
            + step**3 * second_upper / 24
            + step**5 * fourth_upper / 1920
            + step**7 * sixth_upper / 322560
        )
        expected_remainder_upper = step**7 * sixth_upper / 322560
        if cell_upper != expected_cell_upper:
            raise ValueError(f"cell formula mismatch at row {expected_index}")
        if remainder_upper != expected_remainder_upper:
            raise ValueError(f"remainder formula mismatch at row {expected_index}")
        for name, value in (("value_upper", value_upper), ("second_upper", second_upper),
                            ("fourth_upper", fourth_upper), ("sixth_upper", sixth_upper)):
            if value != ceil_grid(value):
                raise ValueError(f"{name} is not upward-rounded at row {expected_index}")

        cell_sum += cell_upper
        remainder_sum += remainder_upper
        if minimum is None or cell_upper < minimum[1]:
            minimum = (expected_index, cell_upper)

    if previous_right != RADIUS:
        raise ValueError("grid does not end at the owner radius")
    if F(json.loads(lines[1])["left"]) != -RADIUS:
        raise ValueError("grid does not start at the negative owner radius")
    if cell_sum != F(main["total_upper"]):
        raise ValueError("cell sum does not equal main total_upper")
    if remainder_sum != F(main["sixth_order_remainder_upper"]):
        raise ValueError("remainder sum does not equal main remainder")
    if not cell_sum < 0:
        raise ValueError("aggregate upper is not negative")

    return {
        "record": 3273,
        "status": "PASS",
        "source_record": 3238,
        "cells": expected_cells,
        "formula_rows": expected_cells,
        "grid_continuous": True,
        "formula_replay_exact": True,
        "aggregate_replay_exact": True,
        "total_upper_negative": True,
        "minimum_cell": minimum[0],
        "nonclaims": ["not imported into Lean", "full-line tail missing", "no SourceRH", "no RH"],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--main", type=Path, default=Path("results/3238_weighted_original_taylor6_40960.json"))
    parser.add_argument("--cells", type=Path, default=Path("results/3238_weighted_original_taylor6_40960.jsonl"))
    parser.add_argument("--output", type=Path, default=Path("results/3273_routea_weighted_original_jsonl_audit.json"))
    args = parser.parse_args()
    result = audit(args.main, args.cells)
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
