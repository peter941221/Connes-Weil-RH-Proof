"""Merge and audit the eight directed endpoint chunks from Record 3300."""

from __future__ import annotations

import argparse
import hashlib
import json
from fractions import Fraction as F
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
CELLS = 40960


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--chunks",
        type=Path,
        default=ROOT / "results/3300_directed_chunks",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=ROOT / "results/3300_routea_directed_endpoint_manifest.json",
    )
    args = parser.parse_args()

    rows = []
    sources = {}
    for chunk_index in range(8):
        path = args.chunks / f"chunk_{chunk_index:03d}.json"
        payload = json.loads(path.read_text(encoding="utf-8"))
        expected_start = chunk_index * 5120
        if payload.get("start") != expected_start or payload.get("count") != 5120:
            raise ValueError(f"chunk range mismatch in {path}")
        for row in payload["rows"]:
            rows.append(row)
        sources[str(path)] = sha256(path)

    rows.sort(key=lambda row: row["index"])
    if len(rows) != CELLS:
        raise ValueError(f"expected {CELLS} rows, got {len(rows)}")
    for index, row in enumerate(rows):
        if row["index"] != index:
            raise ValueError(f"row index mismatch at {index}")
        value = F(row["value_upper"])
        if (10**80) % value.denominator != 0:
            raise ValueError(f"row {index} is not on the 10^-80 grid")

    result = {
        "record": 3300,
        "status": "DIRECTED_DECIMAL_ENDPOINT_MANIFEST_REPLAYED",
        "cells": CELLS,
        "precision_digits": 90,
        "rounding": "outward Decimal intervals, then upward 10^-80 grid",
        "formula": "ratCellValueUpperTight3298 mirror",
        "grid_continuous": True,
        "all_cells_replayed": True,
        "chunk_count": 8,
        "input_sha256": sources,
        "rows": rows,
        "lean_endpoint_dominance_closed": False,
        "lean_manifest_imported": False,
        "producer_go": False,
        "rh_claim": False,
        "nonclaims": [
            "directed Decimal replay is external evidence, not a Lean theorem",
            "the rows have not been imported into Lean",
            "the full-line tail and producer bridge remain open",
        ],
    }
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: result[key] for key in ("record", "status", "cells", "all_cells_replayed")}, indent=2))


if __name__ == "__main__":
    main()
