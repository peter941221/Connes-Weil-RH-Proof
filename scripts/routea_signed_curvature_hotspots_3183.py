"""3183: locate cells dominating the signed curvature remainder."""

from __future__ import annotations

import argparse
import json
from fractions import Fraction as F
from pathlib import Path

from flint import ctx

import routea_signed_correction_enclosure_3182 as enclosure

ROOT = Path(__file__).resolve().parents[1]


def run(cells: int, precision: int) -> dict:
    ctx.prec = precision
    families = enclosure.base.load_families()
    sigma = F(-1, 2)
    step = 2 * enclosure.base.base.RADIUS / cells
    h = enclosure.base.base.lift(step)
    left = -enclosure.base.base.RADIUS
    left_value = enclosure.signed_point_upper(families, left, sigma)
    rows = []
    for index in range(cells):
        right = -enclosure.base.base.RADIUS + (index + 1) * step
        right_value = enclosure.signed_point_upper(families, right, sigma)
        curvature = enclosure.curvature_upper(families, left, right, sigma, h)
        remainder = step ** 3 / 12 * curvature
        rows.append({
            "index": index,
            "left": str(left),
            "right": str(right),
            "curvature_upper": str(curvature),
            "remainder_upper": str(remainder),
        })
        left, left_value = right, right_value
    rows.sort(key=lambda row: float(F(row["remainder_upper"])), reverse=True)
    total = sum((F(row["remainder_upper"]) for row in rows), F(0))
    return {
        "record": 3183,
        "status": "SIGNED_CURVATURE_HOTSPOT_DIAGNOSTIC",
        "cells": cells,
        "precision_bits": precision,
        "sigma": "-1/2",
        "remainder_total": str(total),
        "top_cells": rows[:20],
        "top_1_share": float(F(rows[0]["remainder_upper"]) / total),
        "top_20_share": float(sum((F(row["remainder_upper"]) for row in rows[:20]), F(0)) / total),
        "nonclaims": ["no improved enclosure", "no Lean certificate", "no SourceRH", "no RH"],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--cells", type=int, default=2560)
    parser.add_argument("--precision", type=int, default=192)
    parser.add_argument("--output", type=Path, default=ROOT / "results/3183_signed_curvature_hotspots.json")
    args = parser.parse_args()
    result = run(args.cells, args.precision)
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({
        "record": result["record"],
        "status": result["status"],
        "remainder_total": result["remainder_total"],
        "top_1_share": result["top_1_share"],
        "top_20_share": result["top_20_share"],
        "top_cells": result["top_cells"][:5],
    }, indent=2))


if __name__ == "__main__":
    main()
