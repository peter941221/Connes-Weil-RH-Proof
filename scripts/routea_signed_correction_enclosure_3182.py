"""3182: interval-style signed finite-window enclosure for the correction endpoint."""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from fractions import Fraction as F
from pathlib import Path

from flint import ctx

import price_correction_second_2561 as base

ROOT = Path(__file__).resolve().parents[1]
if hasattr(sys, 'set_int_max_str_digits'):
    sys.set_int_max_str_digits(100000)


def signed_point_upper(families, x, sigma):
    value = sum((family["center"] * base.jets(family, x, sigma)[0] for family in families), base.acb(0))
    error = sum((family["error"] * abs(base.jets(family, x, sigma)[0]) for family in families), base.arb(0))
    return base.base.exact_upper(value.real + error)


def curvature_upper(families, left, right, sigma, h):
    center = base.acb(0)
    error = base.arb(0)
    third = base.arb(0)
    for family in families:
        left_jet = base.jets(family, left, sigma)
        right_jet = base.jets(family, right, sigma)
        midpoint = (left + right) / 2
        second = base.jets(family, midpoint, sigma)[2]
        center += family["center"] * second
        error += family["error"] * abs(second)
        third += family["scale"] * max(abs(left_jet[3]), abs(right_jet[3]))
        third += family["scale"] * h / 2 * base.envelope(family, left, right, sigma)
    return base.base.exact_upper(abs(center) + error + h / 2 * third)


def run(cells: int, precision: int) -> dict:
    ctx.prec = precision
    families = base.load_families()
    sigma = F(-1, 2)
    step = 2 * base.base.RADIUS / cells
    h = base.base.lift(step)
    node_upper = F(0)
    remainder_upper = F(0)
    left = -base.base.RADIUS
    left_value = signed_point_upper(families, left, sigma)
    max_curvature = F(0)
    for index in range(cells):
        right = -base.base.RADIUS + (index + 1) * step
        right_value = signed_point_upper(families, right, sigma)
        curvature = curvature_upper(families, left, right, sigma, h)
        node_upper += step / 2 * (left_value + right_value)
        remainder_upper += step ** 3 / 12 * curvature
        max_curvature = max(max_curvature, curvature)
        left, left_value = right, right_value
    total_upper = node_upper + remainder_upper
    return {
        "record": 3182,
        "status": "SIGNED_FINITE_WINDOW_INTERVAL_STYLE_ENCLOSURE",
        "cells": cells,
        "precision_bits": precision,
        "sigma": "-1/2",
        "node_upper": str(node_upper),
        "curvature_remainder_upper": str(remainder_upper),
        "total_upper": str(total_upper),
        "max_cell_curvature_upper": str(max_curvature),
        "total_upper_negative": total_upper < 0,
        "method": "Arb interval jets with endpoint/derivative envelope; signed real-part node upper",
        "nonclaims": [
            "not yet imported into Lean",
            "full-line tail not included",
            "no SourceRH",
            "no RH",
        ],
        "source_sha256": {
            "scripts/price_correction_second_2561.py": hashlib.sha256(Path(base.__file__).read_bytes()).hexdigest(),
            "results/2338_exact_interpolation_repair.json": hashlib.sha256(base.base.REPAIR.read_bytes()).hexdigest(),
            "results/2275_gap_owner_audit.json": hashlib.sha256(base.base.CAPTURE.read_bytes()).hexdigest(),
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--cells", type=int, default=2560)
    parser.add_argument("--precision", type=int, default=192)
    parser.add_argument("--output", type=Path, default=ROOT / "results/3182_signed_finite_window_enclosure.json")
    args = parser.parse_args()
    result = run(args.cells, args.precision)
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
