"""Replay and audit the 3187 Taylor-6 JSONL cell sidecar."""

from __future__ import annotations

import argparse
import json
import sys
from fractions import Fraction as F
from pathlib import Path

DECIMAL_PLACES = 80
DECIMAL_SCALE = 10**DECIMAL_PLACES
RADIUS = F(65536001, 10000000)


def ceil_grid(value: F) -> F:
    """Return the least multiple of 10^-80 which is >= value."""
    numerator = value.numerator * DECIMAL_SCALE
    denominator = value.denominator
    return F(-((-numerator) // denominator), DECIMAL_SCALE)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--main",
        type=Path,
        default=Path("results/3187_signed_taylor6_interval_40960.json"),
    )
    parser.add_argument(
        "--cells",
        type=Path,
        default=Path("results/3187_signed_taylor6_interval_40960.jsonl"),
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("results/3199_routea_taylor6_jsonl_audit.json"),
    )
    return parser.parse_args()


def audit(main_path: Path, cells_path: Path) -> dict:
    main = json.loads(main_path.read_text(encoding="utf-8"))
    lines = cells_path.read_text(encoding="utf-8").splitlines()
    if not lines:
        raise ValueError("cell sidecar is empty")

    header = json.loads(lines[0])
    expected_cells = int(main["cells"])
    if len(lines) != expected_cells + 1:
        raise ValueError(f"expected {expected_cells + 1} lines, got {len(lines)}")
    if header.get("format") != "3187-cell-upper-jsonl-v1":
        raise ValueError("unexpected JSONL format")
    if header.get("rounding") != "every serialized upper is rounded upward to the 10^-80 grid":
        raise ValueError("rounding policy is missing or changed")

    rows = [json.loads(line) for line in lines[1:]]
    expected_step = F(2 * RADIUS, expected_cells)
    cell_sum = F(0)
    remainder_sum = F(0)
    previous_right = None
    formula_rows = 0
    rounded_rows = 0

    for expected_index, row in enumerate(rows):
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
        formula_rows += 1

        for name, value in (
            ("value_upper", value_upper),
            ("second_upper", second_upper),
            ("fourth_upper", fourth_upper),
            ("sixth_upper", sixth_upper),
        ):
            if value != ceil_grid(value):
                raise ValueError(f"{name} is not on the 10^-80 grid at row {expected_index}")
            rounded_rows += 1

        cell_sum += cell_upper
        remainder_sum += remainder_upper

    if previous_right != RADIUS:
        raise ValueError("grid does not end at the owner radius")
    if F(rows[0]["left"]) != -RADIUS:
        raise ValueError("grid does not start at the negative owner radius")
    if cell_sum != F(main["total_upper"]):
        raise ValueError("cell sum does not equal main total_upper")
    if remainder_sum != F(main["sixth_order_remainder_upper"]):
        raise ValueError("remainder sum does not equal main remainder")

    return {
        "record": 3199,
        "status": "PASS",
        "source_record": 3187,
        "cells": expected_cells,
        "formula_rows": formula_rows,
        "rounded_coefficient_fields": rounded_rows,
        "decimal_places": DECIMAL_PLACES,
        "grid_continuous": True,
        "formula_replay_exact": True,
        "aggregate_replay_exact": True,
        "total_upper_negative": bool(main["total_upper_negative"]),
        "nonclaims": [
            "does not prove owner derivative readback",
            "does not import data into Lean",
            "full-line tail missing",
            "no SourceRH",
            "no RH",
        ],
    }


def main() -> None:
    args = parse_args()
    result = audit(args.main, args.cells)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, json.JSONDecodeError) as error:
        print(f"3199 AUDIT FAIL: {error}", file=sys.stderr)
        raise SystemExit(1)
