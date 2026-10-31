"""3244: screen family grouping for the concrete owner at a target cell.

This is a diagnostic only. It uses the same owner and Arb evaluator as the
3204 repricing, but it does not import numerical output into Lean.
"""

from __future__ import annotations

import json
from fractions import Fraction as F
from pathlib import Path

from flint import ctx

import routea_concrete_owner_taylor6_3204 as concrete
import routea_signed_taylor6_interval_3187 as taylor

ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "results/3244_routea_family_screen.json"


def run(precision: int = 192, index: int = 17168, block_size: int = 5) -> dict:
    ctx.prec = precision
    families = concrete.load_owner_families()
    radius = taylor.base.base.base.RADIUS
    cells = 40960
    step = 2 * radius / cells
    midpoint = -radius + (F(index) + F(1, 2)) * step
    sigma = F(-1, 2)

    terms = []
    for family_index, family in enumerate(families):
        jets = taylor.base.base.jets(family, midpoint, sigma, 4)
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
        selected = terms[first:first + block_size]
        upper = sum((F(item["real_upper"]) for item in selected), F(0))
        lower = sum((F(item["real_lower"]) for item in selected), F(0))
        blocks.append(
            {
                "first_family": first,
                "last_family": first + len(selected) - 1,
                "real_lower": str(lower),
                "real_upper": str(upper),
                "real_upper_decimal": float(upper),
                "sign": "negative" if upper < 0 else "positive_or_zero",
            }
        )

    result = {
        "record": 3244,
        "status": "DIAGNOSTIC_FAMILY_SCREEN",
        "cell_index": index,
        "cells": cells,
        "precision_bits": precision,
        "block_size": block_size,
        "midpoint": str(midpoint),
        "sigma": str(sigma),
        "terms": terms,
        "blocks": blocks,
        "owner_source": str(concrete.OWNER.relative_to(ROOT)),
        "lean_certificate": False,
        "producer_go": False,
    }
    OUTPUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    return result


if __name__ == "__main__":
    print(json.dumps(run(), indent=2))
