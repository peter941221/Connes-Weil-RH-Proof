"""Compare the Arb-evaluated 3310 rectangle rows with the 3309 block target."""

from __future__ import annotations

import argparse
import json
from fractions import Fraction as F
from pathlib import Path

from flint import ctx

import routea_signed_jet_rect_arb_probe_3311 as probe

ROOT = Path(__file__).resolve().parents[1]


def ceil_grid(value: F, places: int = 80) -> F:
    scale = 10**places
    numerator = value.numerator * scale
    return F(-((-numerator) // value.denominator), scale)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--block", type=int, default=0)
    parser.add_argument("--precision", type=int, default=192)
    parser.add_argument("--output", type=Path, default=ROOT / "results/3311_block0_comparison.json")
    args = parser.parse_args()
    ctx.prec = args.precision

    endpoint = json.loads(
        (ROOT / "results/3300_routea_directed_cell_manifest.json").read_text()
    )["rows"][args.block * 256:(args.block + 1) * 256]
    target = F(
        json.loads(
            (ROOT / "results/3309_routea_corrected_signed_block_manifest.json").read_text()
            )["rows"][args.block]["block_upper"]
    )
    rows = {order: [] for order in (0, 2, 4)}
    for order in rows:
        for index in range(args.block * 256, (args.block + 1) * 256):
            rows[order].append(probe.exact_upper(probe.cell_rect(index, order).re_hi))

    step = F(endpoint[0]["step"])
    block_upper = F(0)
    for index in range(256):
        block_upper += (
            step * F(endpoint[index]["value_upper"])
            + step**3 * rows[2][index] / 24
            + step**5 * rows[4][index] / 1920
            + step**7 * F(endpoint[index]["sixth_upper"]) / 322560
        )
    result = {
        "record": 3311,
        "status": "ARB_3310_RECTANGLE_BLOCK_COMPARISON",
        "block": args.block,
        "precision_bits": args.precision,
        "cells": 256,
        "target_manifest_upper": str(target),
        "rectangle_cell_upper_sum": str(block_upper),
        "rectangle_dominates_target": block_upper > target,
        "target_minus_rectangle": str(target - block_upper),
        "rectangle_cell_upper_sum_ceil_1e-80": str(ceil_grid(block_upper)),
        "target_manifest_upper_ceil_1e-80": str(ceil_grid(target)),
        "rows": {
            str(order): [str(value) for value in values]
            for order, values in rows.items()
        },
        "lean_imported": False,
        "rh_claim": False,
    }
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({
        key: result[key]
        for key in (
            "record",
            "status",
            "target_manifest_upper",
            "rectangle_cell_upper_sum",
            "rectangle_dominates_target",
            "target_minus_rectangle",
        )
    }, indent=2))


if __name__ == "__main__":
    main()
