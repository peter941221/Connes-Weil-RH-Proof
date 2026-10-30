"""3184: preserve aggregate signed cancellation in the curvature budget."""

from __future__ import annotations

import argparse
import json
from fractions import Fraction as F
from pathlib import Path

from flint import ctx

import routea_signed_correction_enclosure_3182 as base

ROOT = Path(__file__).resolve().parents[1]


def aggregate_curvature_upper(families, left, right, sigma, h):
    second_center = base.base.acb(0)
    second_error = base.base.arb(0)
    third_left = base.base.acb(0)
    third_right = base.base.acb(0)
    third_left_error = base.base.arb(0)
    third_right_error = base.base.arb(0)
    fourth_bound = base.base.arb(0)
    midpoint = (left + right) / 2
    for family in families:
        left_jets = base.base.jets(family, left, sigma)
        right_jets = base.base.jets(family, right, sigma)
        midpoint_jets = base.base.jets(family, midpoint, sigma)
        second_center += family["center"] * midpoint_jets[2]
        second_error += family["error"] * abs(midpoint_jets[2])
        third_left += family["center"] * left_jets[3]
        third_right += family["center"] * right_jets[3]
        third_left_error += family["error"] * abs(left_jets[3])
        third_right_error += family["error"] * abs(right_jets[3])
        fourth_bound += family["scale"] * base.base.envelope(family, left, right, sigma)
    third_upper = max(abs(third_left) + third_left_error,
                      abs(third_right) + third_right_error)
    third_upper += h / 2 * fourth_bound
    return base.base.base.exact_upper(abs(second_center) + second_error + h / 2 * third_upper)


def run(cells: int, precision: int) -> dict:
    ctx.prec = precision
    families = base.base.load_families()
    sigma = F(-1, 2)
    step = 2 * base.base.base.RADIUS / cells
    h = base.base.base.lift(step)
    node_upper = F(0)
    remainder_upper = F(0)
    left = -base.base.base.RADIUS
    left_value = base.signed_point_upper(families, left, sigma)
    max_curvature = F(0)
    for index in range(cells):
        right = -base.base.base.RADIUS + (index + 1) * step
        right_value = base.signed_point_upper(families, right, sigma)
        curvature = aggregate_curvature_upper(families, left, right, sigma, h)
        node_upper += step / 2 * (left_value + right_value)
        remainder_upper += step ** 3 / 12 * curvature
        max_curvature = max(max_curvature, curvature)
        left, left_value = right, right_value
    total_upper = node_upper + remainder_upper
    return {
        "record": 3184,
        "status": "SIGNED_AGGREGATE_CURVATURE_DIAGNOSTIC",
        "cells": cells,
        "precision_bits": precision,
        "sigma": "-1/2",
        "node_upper": str(node_upper),
        "curvature_remainder_upper": str(remainder_upper),
        "total_upper": str(total_upper),
        "max_cell_curvature_upper": str(max_curvature),
        "total_upper_negative": total_upper < 0,
        "method": "aggregate signed third derivative plus coefficient and fourth-derivative charges",
        "nonclaims": ["diagnostic only", "no Lean certificate", "no full-line tail", "no SourceRH", "no RH"],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--cells", type=int, default=2560)
    parser.add_argument("--precision", type=int, default=192)
    parser.add_argument("--output", type=Path, default=ROOT / "results/3184_signed_aggregate_curvature.json")
    args = parser.parse_args()
    result = run(args.cells, args.precision)
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
