"""3294: build and replay a small-block manifest for the 3273 sidecar.

The manifest is external evidence.  It deliberately does not claim that the
Lean rational rectangle upper endpoint is dominated by these values.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from fractions import Fraction as F
from pathlib import Path


DECIMAL_SCALE = 10**80
RADIUS = F(65536001, 10000000)


def ceil_grid(value: F) -> F:
    numerator = value.numerator * DECIMAL_SCALE
    return F(-((-numerator) // value.denominator), DECIMAL_SCALE)


def parse_and_replay(main_path: Path, cells_path: Path, block_size: int) -> dict:
    main = json.loads(main_path.read_text(encoding="utf-8"))
    lines = cells_path.read_text(encoding="utf-8").splitlines()
    if not lines:
        raise ValueError("cell sidecar is empty")
    header = json.loads(lines[0])
    cells = int(main["cells"])
    if len(lines) != cells + 1:
        raise ValueError(f"expected {cells + 1} lines, got {len(lines)}")
    if header.get("format") != "3238-weighted-original-cell-upper-jsonl-v1":
        raise ValueError("unexpected JSONL format")
    if cells % block_size:
        raise ValueError("cell count must be divisible by block size")

    expected_step = 2 * RADIUS / cells
    rows: list[dict[str, F | int]] = []
    total = F(0)
    previous_right = None
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
        expected_cell_upper = (
            step * value_upper
            + step**3 * second_upper / 24
            + step**5 * fourth_upper / 1920
            + step**7 * sixth_upper / 322560
        )
        if cell_upper != expected_cell_upper:
            raise ValueError(f"cell formula mismatch at row {expected_index}")
        for name, value in (
            ("value_upper", value_upper),
            ("second_upper", second_upper),
            ("fourth_upper", fourth_upper),
            ("sixth_upper", sixth_upper),
        ):
            if value != ceil_grid(value):
                raise ValueError(f"{name} is not upward-rounded at row {expected_index}")
        rows.append({"index": expected_index, "cell_upper": cell_upper})
        total += cell_upper

    if previous_right != RADIUS or F(json.loads(lines[1])["left"]) != -RADIUS:
        raise ValueError("grid does not cover the owner radius")
    if total != F(main["total_upper"]):
        raise ValueError("cell sum does not equal main total_upper")
    if total >= 0:
        raise ValueError("aggregate upper is not negative")

    blocks = []
    for first in range(0, cells, block_size):
        block_rows = rows[first : first + block_size]
        upper = sum((row["cell_upper"] for row in block_rows), F(0))
        blocks.append(
            {
                "block": first // block_size,
                "first_index": first,
                "last_index": first + block_size - 1,
                "cell_count": len(block_rows),
                "cell_upper": str(upper),
                "cell_upper_negative": upper < 0,
                "minimum_cell": min(block_rows, key=lambda row: row["cell_upper"])["index"],
            }
        )

    return {
        "record": 3294,
        "status": "EXTERNAL_BLOCK_MANIFEST_REPLAYED_LEAN_ENDPOINT_OPEN",
        "source_record": 3273,
        "cells": cells,
        "block_size": block_size,
        "block_count": len(blocks),
        "grid_continuous": True,
        "formula_replay_exact": True,
        "aggregate_replay_exact": True,
        "total_upper": str(total),
        "total_upper_negative": total < 0,
        "blocks": blocks,
        "lean_endpoint_dominance_closed": False,
        "lean_manifest_imported": False,
        "full_line_tail_included": False,
        "producer_go": False,
        "rh_claim": False,
        "input_sha256": {
            str(main_path): hashlib.sha256(main_path.read_bytes()).hexdigest(),
            str(cells_path): hashlib.sha256(cells_path.read_bytes()).hexdigest(),
        },
        "nonclaims": [
            "JSONL values are not imported into Lean",
            "block values do not dominate ratCellValueUpper3289",
            "full-line tail is separate",
            "no SourceRH",
            "no RH",
        ],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--main", type=Path, default=Path("results/3238_weighted_original_taylor6_40960.json"))
    parser.add_argument("--cells", type=Path, default=Path("results/3238_weighted_original_taylor6_40960.jsonl"))
    parser.add_argument("--block-size", type=int, default=256)
    parser.add_argument("--output", type=Path, default=Path("results/3294_routea_weighted_original_block_manifest.json"))
    args = parser.parse_args()
    result = parse_and_replay(args.main, args.cells, args.block_size)
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: result[key] for key in ("record", "status", "cells", "block_size", "block_count", "total_upper", "total_upper_negative")}, indent=2))


if __name__ == "__main__":
    main()
