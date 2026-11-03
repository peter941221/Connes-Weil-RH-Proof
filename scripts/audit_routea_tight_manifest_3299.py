"""Audit the structural closure of the 3299 Decimal manifests.

This checks row counts, contiguous block coverage, the Taylor-6 cell formula,
and exact sums of the already serialized Decimal values.  It does not turn
those values into a Lean theorem and it does not certify directed rounding.
"""

from __future__ import annotations

import argparse
import json
from decimal import Decimal, getcontext
from fractions import Fraction as F
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
CELLS = 40960
BLOCK_SIZE = 256


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--endpoint",
        type=Path,
        default=ROOT / "results/3299_routea_tight_endpoint_manifest.json",
    )
    parser.add_argument(
        "--cells",
        type=Path,
        default=ROOT / "results/3299_routea_tight_cell_manifest.json",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=ROOT / "results/3299_routea_tight_manifest_audit.json",
    )
    args = parser.parse_args()

    endpoint = json.loads(args.endpoint.read_text(encoding="utf-8"))
    cell = json.loads(args.cells.read_text(encoding="utf-8"))
    precision = int(cell["precision_digits"])
    getcontext().prec = precision

    endpoint_rows = endpoint["rows"]
    if endpoint["cells"] != CELLS or len(endpoint_rows) != CELLS:
        raise ValueError("endpoint row count mismatch")
    for index, row in enumerate(endpoint_rows):
        if row["index"] != index:
            raise ValueError(f"endpoint index mismatch at {index}")

    rows = cell["rows"]
    if cell["cells"] != CELLS or len(rows) != CELLS:
        raise ValueError("cell row count mismatch")

    row_sum = F(0)
    for index, row in enumerate(rows):
        if row["index"] != index or row["index"] != endpoint_rows[index]["index"]:
            raise ValueError(f"cell index mismatch at {index}")
        step = F(row["step"])
        value = F(row["value_upper"])
        second = F(row["second_upper"])
        fourth = F(row["fourth_upper"])
        sixth = F(row["sixth_upper"])
        expected = (
            step * value
            + step**3 * second / 24
            + step**5 * fourth / 1920
            + step**7 * sixth / 322560
        )
        actual = F(row["cell_upper_exact_fraction"])
        if expected != actual:
            raise ValueError(f"cell formula mismatch at {index}")
        row_sum += F(actual)

    blocks = cell["blocks"]
    if len(blocks) != CELLS // BLOCK_SIZE:
        raise ValueError("block count mismatch")
    block_sum = F(0)
    negative_blocks = 0
    for block_index, block in enumerate(blocks):
        first = block_index * BLOCK_SIZE
        last = first + BLOCK_SIZE - 1
        if (
            block["block"] != block_index
            or block["first_index"] != first
            or block["last_index"] != last
            or block["cell_count"] != BLOCK_SIZE
        ):
            raise ValueError(f"block coverage mismatch at {block_index}")
        expected_fraction = sum(
            (F(rows[index]["cell_upper_exact_fraction"])
             for index in range(first, last + 1)),
            F(0),
        )
        if expected_fraction != F(block["cell_upper_exact_fraction"]):
            raise ValueError(f"block exact sum mismatch at {block_index}")
        if (expected_fraction < 0) != bool(block["cell_upper_negative"]):
            raise ValueError(f"block sign mismatch at {block_index}")
        block_sum += expected_fraction
        negative_blocks += int(expected_fraction < 0)

    serialized_total = F(cell["serialized_total_fraction"])
    if row_sum != serialized_total or block_sum != serialized_total:
        raise ValueError("serialized row/block/total sums do not close")
    if (serialized_total < 0) != bool(cell["total_upper_negative"]):
        raise ValueError("total sign mismatch")

    result = {
        "record": 3299,
        "status": "PASS",
        "cells": CELLS,
        "blocks": len(blocks),
        "formula_rows": CELLS,
        "grid_continuous": True,
        "exact_serialized_row_block_total_closure": True,
        "negative_blocks": negative_blocks,
        "total_upper": cell["total_upper"],
        "total_upper_negative": bool(cell["total_upper_negative"]),
        "lean_endpoint_dominance_closed": False,
        "lean_manifest_imported": False,
        "producer_go": False,
        "rh_claim": False,
        "nonclaims": [
            "this audit proves only artifact structure and arithmetic replay",
            "the external endpoint replay is not a Lean proof",
            "no Lean theorem or RH conclusion follows",
        ],
    }
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
