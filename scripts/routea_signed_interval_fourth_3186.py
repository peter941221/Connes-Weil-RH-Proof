"""3186: cell-local Arb interval bound for the aggregate fourth derivative."""

from __future__ import annotations

import argparse
import json
from fractions import Fraction as F
from math import comb
from pathlib import Path

from flint import acb, arb, ctx

import routea_signed_correction_enclosure_3182 as base

ROOT = Path(__file__).resolve().parents[1]
POLYS = base.base.POLYS


def interval_jets(family, left, right, sigma, order):
    midpoint = (left + right) / 2
    half = (right - left) / 2
    x = arb(base.base.base.lift(midpoint), base.base.base.lift(abs(half)))
    radius = base.base.base.lift(family["r"])
    u = x / radius
    q = 1 - u * u
    exponent = acb(-30 / q + base.base.base.lift(sigma) * x, family["theta"] * x)
    exponential = exponent.exp()
    bumps = [sum((c * u**p for p, c in POLYS[k].items()), arb(0)) /
             (radius**k * q**(2*k)) for k in range(order + 3)]
    lam = acb(0, family["theta"])
    raw = [sum((comb(k, j) * lam**(k-j) * bumps[j]
                for j in range(k + 1)), acb(0)) for k in range(order + 3)]
    weight_sigma = base.base.base.lift(sigma)
    return [exponential * sum((comb(k, j) * weight_sigma**(k-j) * raw[j+2]
                               for j in range(k + 1)), acb(0))
            for k in range(order + 1)]


def fourth_upper(families, left, right, sigma):
    aggregate = acb(0)
    coefficient_error = arb(0)
    fallback = arb(0)
    for family in families:
        radius = family["r"]
        if left > -radius and right < radius:
            try:
                jet = interval_jets(family, left, right, sigma, 4)[4]
            except ValueError:
                fallback += family["scale"] * base.base.envelope(family, left, right, sigma)
            else:
                if not jet.is_finite():
                    fallback += family["scale"] * base.base.envelope(family, left, right, sigma)
                    continue
                aggregate += family["center"] * jet
                coefficient_error += family["error"] * abs(jet)
        elif right <= -radius or left >= radius:
            continue
        else:
            fallback += family["scale"] * base.base.envelope(family, left, right, sigma)
    return base.base.base.exact_upper(abs(aggregate) + coefficient_error + fallback)


def run(cells: int, precision: int) -> dict:
    ctx.prec = precision
    families = base.base.load_families()
    sigma = F(-1, 2)
    step = 2 * base.base.base.RADIUS / cells
    h = base.base.base.lift(step)
    total = F(0)
    remainder = F(0)
    for index in range(cells):
        left = -base.base.base.RADIUS + index * step
        right = left + step
        midpoint = (left + right) / 2
        value = base.base.acb(0)
        value_error = base.base.arb(0)
        second = base.base.acb(0)
        second_error = base.base.arb(0)
        for family in families:
            jets = base.base.jets(family, midpoint, sigma, 2)
            value += family["center"] * jets[0]
            value_error += family["error"] * abs(jets[0])
            second += family["center"] * jets[2]
            second_error += family["error"] * abs(jets[2])
        value_upper = base.base.base.exact_upper(value.real + value_error)
        second_upper = base.base.base.exact_upper(second.real + second_error)
        fourth = fourth_upper(families, left, right, sigma)
        total += step * value_upper + step**3 / 24 * second_upper + step**5 / 1920 * fourth
        remainder += step**5 / 1920 * fourth
    return {
        "record": 3186,
        "status": "SIGNED_INTERVAL_FOURTH_DIAGNOSTIC",
        "cells": cells,
        "precision_bits": precision,
        "sigma": "-1/2",
        "total_upper": str(total),
        "fourth_remainder_upper": str(remainder),
        "total_upper_negative": total < 0,
        "method": "cell-local Arb interval aggregate fourth derivative with boundary fallback",
        "nonclaims": ["not imported into Lean", "full-line tail missing", "no SourceRH", "no RH"],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--cells", type=int, default=2560)
    parser.add_argument("--precision", type=int, default=192)
    parser.add_argument("--output", type=Path, default=ROOT / "results/3186_signed_interval_fourth.json")
    args = parser.parse_args()
    result = run(args.cells, args.precision)
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
