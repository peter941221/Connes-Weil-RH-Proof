"""3267: diagnostic full-window block decomposition for the formal target.

This preserves the 3238 weighted-original evaluator but prices contiguous
family blocks separately over the full 40960-cell window. It is diagnostic:
separate block sixth-derivative envelopes can lose cancellation, so a failure
here does not refute the aggregate evaluator.
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction as F
from pathlib import Path

from flint import acb, ctx

import routea_concrete_owner_taylor6_3204 as concrete
import routea_concrete_owner_weighted_original_taylor6_3238 as original
import routea_signed_taylor6_interval_3187 as taylor

ROOT = Path(__file__).resolve().parents[1]


def run(cells: int = 40960, precision: int = 192, block_size: int = 5) -> dict:
    if cells <= 0 or block_size <= 0:
        raise ValueError("cells and block_size must be positive")
    ctx.prec = precision
    families = concrete.load_owner_families()
    sigma = F(-1, 2)
    radius = taylor.base.base.base.RADIUS
    step = 2 * radius / cells
    blocks = []
    for first in range(0, len(families), block_size):
        blocks.append(
            {
                "first_family": first,
                "last_family": min(first + block_size, len(families)) - 1,
                "families": families[first:first + block_size],
                "total": F(0),
                "remainder": F(0),
            }
        )

    for index in range(cells):
        left = -radius + index * step
        right = left + step
        midpoint = (left + right) / 2
        for block in blocks:
            value = acb(0)
            second = acb(0)
            fourth = acb(0)
            for family in block["families"]:
                jets = original.original_jets(family, midpoint, sigma, 4)
                value += family["center"] * jets[0]
                second += family["center"] * jets[2]
                fourth += family["center"] * jets[4]
            value_upper = taylor.rounded_up(
                taylor.base.base.base.exact_upper(value.real)
            )
            second_upper = taylor.rounded_up(
                taylor.base.base.base.exact_upper(second.real)
            )
            fourth_upper = taylor.rounded_up(
                taylor.base.base.base.exact_upper(fourth.real)
            )
            sixth = taylor.rounded_up(
                original.sixth_upper(block["families"], left, right, sigma)
            )
            cell_upper = (
                step * value_upper
                + step**3 * second_upper / 24
                + step**5 * fourth_upper / 1920
                + step**7 * sixth / 322560
            )
            remainder = step**7 * sixth / 322560
            block["total"] += cell_upper
            block["remainder"] += remainder

    serial_blocks = []
    for block in blocks:
        serial_blocks.append(
            {
                "first_family": block["first_family"],
                "last_family": block["last_family"],
                "total_upper": str(block["total"]),
                "total_upper_decimal": float(block["total"]),
                "sixth_order_remainder_upper": str(block["remainder"]),
                "sign": "negative" if block["total"] < 0 else "positive_or_zero",
            }
        )

    total = sum((F(block["total_upper"]) for block in serial_blocks), F(0))
    result = {
        "record": 3267,
        "status": "DIAGNOSTIC_FORMAL_WEIGHTED_ORIGINAL_FULL_WINDOW_BLOCKS",
        "cells": cells,
        "precision_bits": precision,
        "block_size": block_size,
        "sigma": str(sigma),
        "blocks": serial_blocks,
        "sum_of_block_uppers": str(total),
        "sum_of_block_uppers_decimal": float(total),
        "formal_aggregate_reference": "results/3238_weighted_original_taylor6.json",
        "owner_source": str(concrete.OWNER.relative_to(ROOT)),
        "evaluator_source": "scripts/routea_concrete_owner_weighted_original_taylor6_3238.py",
        "lean_certificate": False,
        "producer_go": False,
    }
    output = ROOT / f"results/3267_routea_original_blocks_{cells}_{block_size}.json"
    output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    return result


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--cells", type=int, default=40960)
    parser.add_argument("--precision", type=int, default=192)
    parser.add_argument("--block-size", type=int, default=5)
    args = parser.parse_args()
    print(json.dumps(run(args.cells, args.precision, args.block_size), indent=2))


if __name__ == "__main__":
    main()
