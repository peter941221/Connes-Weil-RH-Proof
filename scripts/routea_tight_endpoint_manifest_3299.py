"""3299: replay the 3298 Lean endpoint over all 40960 cells.

The evaluator follows the same construction as
``ratCellValueUpperTight3298``: each family is projected to a real interval,
the 30 family intervals are summed with their signs intact, and the resulting
interval is multiplied by the weight interval.  This artifact is diagnostic
only.  Decimal ROUND_HALF_EVEN arithmetic is not a directed-rounding proof and
the rows are not imported into Lean.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from decimal import Decimal, getcontext
from pathlib import Path

import routea_tight_real_endpoint_probe_3298 as endpoint_probe


ROOT = Path(__file__).resolve().parents[1]
CELLS = 40960
BLOCK_SIZE = 256


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--precision", type=int, default=100)
    parser.add_argument(
        "--output",
        type=Path,
        default=ROOT / "results/3299_routea_tight_endpoint_manifest.json",
    )
    args = parser.parse_args()

    getcontext().prec = args.precision
    modulations = endpoint_probe.base.parse_modulations()
    widths = endpoint_probe.base.parse_widths()
    coefficients = endpoint_probe.base.parse_coefficients()

    rows: list[dict[str, object]] = []
    blocks: list[dict[str, object]] = []
    total = Decimal(0)
    for index in range(CELLS):
        value = endpoint_probe.real_endpoint(
            index, modulations, widths, coefficients
        )
        rows.append({"index": index, "value_upper": str(value)})
        total += value
        if (index + 1) % BLOCK_SIZE == 0:
            first = index + 1 - BLOCK_SIZE
            block_rows = rows[first : index + 1]
            block_upper = sum(
                (Decimal(row["value_upper"]) for row in block_rows), Decimal(0)
            )
            blocks.append(
                {
                    "block": first // BLOCK_SIZE,
                    "first_index": first,
                    "last_index": index,
                    "cell_count": BLOCK_SIZE,
                    "endpoint_upper": str(block_upper),
                    "endpoint_upper_negative": block_upper < 0,
                }
            )

    result = {
        "record": 3299,
        "status": "DIAGNOSTIC_TIGHT_ENDPOINT_MANIFEST_NOT_CERTIFIED",
        "cells": CELLS,
        "block_size": BLOCK_SIZE,
        "block_count": len(blocks),
        "precision_digits": args.precision,
        "arithmetic": "Decimal ROUND_HALF_EVEN",
        "formula": "ratCellValueUpperTight3298 mirror",
        "grid_continuous": True,
        "all_cells_replayed": len(rows) == CELLS,
        "blocks": blocks,
        "total_upper": str(total),
        "total_upper_negative": total < 0,
        "lean_endpoint_dominance_closed": False,
        "lean_manifest_imported": False,
        "full_line_tail_included": False,
        "producer_go": False,
        "rh_claim": False,
        "input_sha256": {
            "ConnesWeilRH/Dev/C1RouteARationalTightTail3298.lean": sha256(
                ROOT / "ConnesWeilRH/Dev/C1RouteARationalTightTail3298.lean"
            ),
            "ConnesWeilRH/Dev/C1RouteARationalRealProjection3298.lean": sha256(
                ROOT / "ConnesWeilRH/Dev/C1RouteARationalRealProjection3298.lean"
            ),
            "ConnesWeilRH/Dev/C1RouteARationalTightCell3298.lean": sha256(
                ROOT / "ConnesWeilRH/Dev/C1RouteARationalTightCell3298.lean"
            ),
        },
        "rows": rows,
        "nonclaims": [
            "Decimal arithmetic is not directed rounding",
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
