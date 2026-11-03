"""3299: attach the existing Taylor correction rows to the new endpoint.

The endpoint rows come from the 3298 real-projection replay.  The second,
fourth, and sixth derivative rows are reused from the existing 3238 sidecar;
they are independent of the endpoint replacement.  The resulting cell and
block sums mirror ``record2680CellUpper3209`` numerically, but remain external
diagnostic evidence because the endpoint rows use ordinary Decimal arithmetic.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from decimal import Decimal, getcontext
from fractions import Fraction as F
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
CELLS = 40960
BLOCK_SIZE = 256


def decimal_fraction(value: F) -> Decimal:
    return Decimal(value.numerator) / Decimal(value.denominator)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


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
        default=ROOT / "results/3238_weighted_original_taylor6_40960.jsonl",
    )
    parser.add_argument("--precision", type=int, default=100)
    parser.add_argument(
        "--output",
        type=Path,
        default=ROOT / "results/3299_routea_tight_cell_manifest.json",
    )
    args = parser.parse_args()
    getcontext().prec = args.precision

    endpoint = json.loads(args.endpoint.read_text(encoding="utf-8"))
    endpoint_rows = endpoint["rows"]
    if endpoint["cells"] != CELLS or len(endpoint_rows) != CELLS:
        raise ValueError("endpoint manifest does not contain all 40960 cells")

    lines = args.cells.read_text(encoding="utf-8").splitlines()
    if len(lines) != CELLS + 1:
        raise ValueError("Taylor sidecar row count mismatch")
    header = json.loads(lines[0])
    if header.get("format") != "3238-weighted-original-cell-upper-jsonl-v1":
        raise ValueError("unexpected Taylor sidecar format")

    rows: list[dict[str, object]] = []
    blocks: list[dict[str, object]] = []
    serialized_total = F(0)
    for index, line in enumerate(lines[1:]):
        source = json.loads(line)
        if source["index"] != index or endpoint_rows[index]["index"] != index:
            raise ValueError(f"index mismatch at row {index}")
        step_fraction = F(source["step"])
        endpoint_value = endpoint_rows[index].get(
            "value_upper_decimal", endpoint_rows[index]["value_upper"]
        )
        value_upper_fraction = F(endpoint_value)
        second_upper_fraction = F(source["second_upper"])
        fourth_upper_fraction = F(source["fourth_upper"])
        sixth_upper_fraction = F(source["sixth_upper"])
        cell_upper_fraction = (
            step_fraction * value_upper_fraction
            + step_fraction**3 * second_upper_fraction / 24
            + step_fraction**5 * fourth_upper_fraction / 1920
            + step_fraction**7 * sixth_upper_fraction / 322560
        )
        cell_upper = decimal_fraction(cell_upper_fraction)
        rows.append(
            {
                "index": index,
                "step": source["step"],
                "value_upper": str(value_upper_fraction),
                "second_upper": source["second_upper"],
                "fourth_upper": source["fourth_upper"],
                "sixth_upper": source["sixth_upper"],
                "cell_upper": str(cell_upper),
                "cell_upper_exact_fraction": str(cell_upper_fraction),
            }
        )
        serialized_total += cell_upper_fraction
        if (index + 1) % BLOCK_SIZE == 0:
            first = index + 1 - BLOCK_SIZE
            block_rows = rows[first : index + 1]
            block_fraction = sum(
                (F(row["cell_upper_exact_fraction"]) for row in block_rows), F(0)
            )
            block_upper = decimal_fraction(block_fraction)
            blocks.append(
                {
                    "block": first // BLOCK_SIZE,
                    "first_index": first,
                    "last_index": index,
                    "cell_count": BLOCK_SIZE,
                    "cell_upper": str(block_upper),
                    "cell_upper_exact_fraction": str(block_fraction),
                    "cell_upper_negative": block_upper < 0,
                }
            )

    result = {
        "record": 3299,
        "status": "DIAGNOSTIC_TIGHT_CELL_MANIFEST_NOT_CERTIFIED",
        "cells": CELLS,
        "block_size": BLOCK_SIZE,
        "block_count": len(blocks),
        "precision_digits": args.precision,
        "formula": "record2680CellUpper3209 mirror",
        "endpoint_source": str(args.endpoint),
        "derivative_source": str(args.cells),
        "grid_continuous": True,
        "all_cells_replayed": len(rows) == CELLS,
        "blocks": blocks,
        "total_upper": str(decimal_fraction(serialized_total)),
        "serialized_total_fraction": str(serialized_total),
        "total_upper_negative": serialized_total < 0,
        "lean_endpoint_dominance_closed": False,
        "lean_manifest_imported": False,
        "full_line_tail_included": False,
        "producer_go": False,
        "rh_claim": False,
        "input_sha256": {
            str(args.endpoint): sha256(args.endpoint),
            str(args.cells): sha256(args.cells),
        },
        "rows": rows,
        "nonclaims": [
            "endpoint arithmetic is Decimal ROUND_HALF_EVEN, not directed rounding",
            "the rows do not prove endpoint dominance in Lean",
            "the manifest is not a Lean theorem",
            "the full-line tail and producer bridge remain open",
        ],
    }
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(
        json.dumps(
            {
                key: result[key]
                for key in (
                    "record",
                    "status",
                    "cells",
                    "block_count",
                    "total_upper",
                    "total_upper_negative",
                )
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
