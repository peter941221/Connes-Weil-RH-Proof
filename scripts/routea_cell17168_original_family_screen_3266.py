"""3266: screen the formal weighted-original family terms at cell 17168.

This is diagnostic only. Unlike record 3244, it uses the formal weighted
original-function evaluator from record 3238 rather than the legacy
second-derivative ``jets[0]`` path.
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction as F
from pathlib import Path

from flint import ctx

import routea_concrete_owner_taylor6_3204 as concrete
import routea_concrete_owner_weighted_original_taylor6_3238 as original
import routea_signed_taylor6_interval_3187 as taylor

ROOT = Path(__file__).resolve().parents[1]


def interval_sum(terms: list[dict], first: int, last: int) -> tuple[F, F]:
    selected = terms[first:last + 1]
    upper = sum((F(item["real_upper"]) for item in selected), F(0))
    lower = sum((F(item["real_lower"]) for item in selected), F(0))
    return lower, upper


def run(precision: int = 192, index: int = 17168, block_size: int = 5) -> dict:
    if block_size <= 0:
        raise ValueError("block_size must be positive")
    ctx.prec = precision
    families = concrete.load_owner_families()
    radius = taylor.base.base.base.RADIUS
    cells = 40960
    step = 2 * radius / cells
    midpoint = -radius + (F(index) + F(1, 2)) * step
    sigma = F(-1, 2)

    terms = []
    for family_index, family in enumerate(families):
        jets = original.original_jets(family, midpoint, sigma, 4)
        term = family["center"] * jets[0]
        real_upper = taylor.rounded_up(taylor.base.base.base.exact_upper(term.real))
        real_lower = -taylor.base.base.base.exact_upper(-term.real)
        terms.append(
            {
                "family": family_index,
                "real_lower": str(real_lower),
                "real_upper": str(real_upper),
                "real_upper_decimal": float(real_upper),
            }
        )

    blocks = []
    for first in range(0, len(terms), block_size):
        last = min(first + block_size, len(terms)) - 1
        lower, upper = interval_sum(terms, first, last)
        blocks.append(
            {
                "first_family": first,
                "last_family": last,
                "real_lower": str(lower),
                "real_upper": str(upper),
                "real_upper_decimal": float(upper),
                "sign": "negative" if upper < 0 else "positive_or_zero",
            }
        )

    negative_intervals = []
    for first in range(len(terms)):
        for last in range(first, len(terms)):
            lower, upper = interval_sum(terms, first, last)
            if upper < 0:
                negative_intervals.append(
                    {
                        "first_family": first,
                        "last_family": last,
                        "width": last - first + 1,
                        "real_lower": str(lower),
                        "real_upper": str(upper),
                        "real_upper_decimal": float(upper),
                    }
                )
    negative_intervals.sort(
        key=lambda item: (item["width"], F(item["real_upper"]))
    )

    total_lower, total_upper = interval_sum(terms, 0, len(terms) - 1)
    result = {
        "record": 3266,
        "status": "DIAGNOSTIC_FORMAL_WEIGHTED_ORIGINAL_FAMILY_SCREEN",
        "cell_index": index,
        "cells": cells,
        "precision_bits": precision,
        "block_size": block_size,
        "midpoint": str(midpoint),
        "sigma": str(sigma),
        "terms": terms,
        "blocks": blocks,
        "all_contiguous_negative_intervals": negative_intervals,
        "total_lower": str(total_lower),
        "total_upper": str(total_upper),
        "total_upper_decimal": float(total_upper),
        "owner_source": str(concrete.OWNER.relative_to(ROOT)),
        "evaluator_source": "scripts/routea_concrete_owner_weighted_original_taylor6_3238.py",
        "legacy_second_derivative_path_used": False,
        "lean_certificate": False,
        "producer_go": False,
    }
    output = ROOT / f"results/3266_routea_original_family_screen_{index}.json"
    output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    return result


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--precision", type=int, default=192)
    parser.add_argument("--index", type=int, default=17168)
    parser.add_argument("--block-size", type=int, default=5)
    args = parser.parse_args()
    print(json.dumps(run(args.precision, args.index, args.block_size), indent=2))


if __name__ == "__main__":
    main()
