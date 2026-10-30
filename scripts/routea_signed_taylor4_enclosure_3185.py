"""3185: fourth-order midpoint Taylor enclosure for the signed correction."""

from __future__ import annotations

import argparse
import json
from fractions import Fraction as F
from pathlib import Path

from flint import ctx

import routea_signed_correction_enclosure_3182 as base

ROOT = Path(__file__).resolve().parents[1]


def run(cells: int, precision: int) -> dict:
    ctx.prec = precision
    families = base.base.load_families()
    sigma = F(-1, 2)
    step = 2 * base.base.base.RADIUS / cells
    h = base.base.base.lift(step)
    h3 = step ** 3
    h5 = step ** 5
    integral_upper = F(0)
    fourth_upper_total = F(0)
    for index in range(cells):
        left = -base.base.base.RADIUS + index * step
        right = left + step
        midpoint = (left + right) / 2
        value = base.base.acb(0)
        value_error = base.base.arb(0)
        second = base.base.acb(0)
        second_error = base.base.arb(0)
        fourth_bound = base.base.arb(0)
        for family in families:
            jets = base.base.jets(family, midpoint, sigma, 4)
            value += family["center"] * jets[0]
            value_error += family["error"] * abs(jets[0])
            second += family["center"] * jets[2]
            second_error += family["error"] * abs(jets[2])
            fourth_bound += family["scale"] * base.base.envelope(family, left, right, sigma)
        value_upper = base.base.base.exact_upper(value.real + value_error)
        second_upper = base.base.base.exact_upper(second.real + second_error)
        fourth_upper = base.base.base.exact_upper(fourth_bound)
        integral_upper += step * value_upper + h3 / 24 * second_upper + h5 / 1920 * fourth_upper
        fourth_upper_total += h5 / 1920 * fourth_upper
    return {
        "record": 3185,
        "status": "SIGNED_TAYLOR4_INTERVAL_STYLE_ENCLOSURE",
        "cells": cells,
        "precision_bits": precision,
        "sigma": "-1/2",
        "total_upper": str(integral_upper),
        "fourth_order_remainder_upper": str(fourth_upper_total),
        "total_upper_negative": integral_upper < 0,
        "formula": "integral <= h*f(mid) + h^3*f_second(mid)/24 + h^5*sup_abs_fourth/1920",
        "nonclaims": ["not imported into Lean", "full-line tail not included", "no SourceRH", "no RH"],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--cells", type=int, default=2560)
    parser.add_argument("--precision", type=int, default=192)
    parser.add_argument("--output", type=Path, default=ROOT / "results/3185_signed_taylor4_enclosure.json")
    args = parser.parse_args()
    result = run(args.cells, args.precision)
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
