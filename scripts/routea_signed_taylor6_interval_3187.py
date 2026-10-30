"""3187: hybrid sixth-order Taylor enclosure with aggregate interval jets."""

from __future__ import annotations

import argparse
import json
import sys
from fractions import Fraction as F
from math import comb
from pathlib import Path

from flint import acb, arb, ctx

import routea_signed_correction_enclosure_3182 as base

ROOT = Path(__file__).resolve().parents[1]
SERIALIZATION_DECIMAL_PLACES = 80
if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(1000000)


def extend_polynomials():
    result = list(base.base.POLYS)
    while len(result) < 9:
        k = len(result) - 1
        nxt = {}
        for power, coefficient in result[-1].items():
            nxt[power + 1] = nxt.get(power + 1, 0) + (4 * k - 60) * coefficient
            nxt[power + 3] = nxt.get(power + 3, 0) - 4 * k * coefficient
            if power:
                for shift, factor in ((-1, 1), (1, -2), (3, 1)):
                    nxt[power + shift] = nxt.get(power + shift, 0) + power * coefficient * factor
        result.append({power: value for power, value in nxt.items() if value})
    return result


POLYS = extend_polynomials()


def rounded_up(value: F, decimal_places: int = SERIALIZATION_DECIMAL_PLACES) -> F:
    """Round an exact upper bound upward to a Lean-friendly decimal grid."""
    scale = 10**decimal_places
    numerator = value.numerator * scale
    denominator = value.denominator
    return F(-((-numerator) // denominator), scale)


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


def sixth_upper(families, left, right, sigma):
    aggregate = acb(0)
    coefficient_error = arb(0)
    fallback = arb(0)
    for family in families:
        radius = family["r"]
        if left > -radius and right < radius:
            try:
                jet = interval_jets(family, left, right, sigma, 6)[6]
            except ValueError:
                jet = None
            if jet is not None and jet.is_finite():
                aggregate += family["center"] * jet
                coefficient_error += family["error"] * abs(jet)
            else:
                fallback += family["scale"] * base.base.envelope(family, left, right, sigma)
        elif right <= -radius or left >= radius:
            continue
        else:
            fallback += family["scale"] * base.base.envelope(family, left, right, sigma)
    return base.base.base.exact_upper(abs(aggregate) + coefficient_error + fallback)


def run(cells: int, precision: int, cell_output: Path | None = None) -> dict:
    ctx.prec = precision
    families = base.base.load_families()
    sigma = F(-1, 2)
    step = 2 * base.base.base.RADIUS / cells
    total = F(0)
    remainder = F(0)
    cell_file = None
    if cell_output is not None:
        cell_output.parent.mkdir(parents=True, exist_ok=True)
        cell_file = cell_output.open("w", encoding="utf-8")
        cell_file.write(json.dumps({
            "format": "3187-cell-upper-jsonl-v1",
            "record": 3187,
            "status": "SIGNED_TAYLOR6_CELL_DIAGNOSTIC",
            "cells": cells,
            "precision_bits": precision,
            "sigma": str(sigma),
            "step": str(step),
            "formula": "h*f + h^3*f2/24 + h^5*f4/1920 + h^7*sup_abs_f6/322560",
            "rounding": "every serialized upper is rounded upward to the 10^-80 grid",
            "nonclaims": ["not imported into Lean", "full-line tail missing", "no SourceRH", "no RH"],
        }, sort_keys=True) + "\n")
    try:
        for index in range(cells):
            left = -base.base.base.RADIUS + index * step
            right = left + step
            midpoint = (left + right) / 2
            value = base.base.acb(0)
            value_error = base.base.arb(0)
            second = base.base.acb(0)
            second_error = base.base.arb(0)
            fourth = base.base.acb(0)
            fourth_error = base.base.arb(0)
            for family in families:
                jets = base.base.jets(family, midpoint, sigma, 4)
                value += family["center"] * jets[0]
                value_error += family["error"] * abs(jets[0])
                second += family["center"] * jets[2]
                second_error += family["error"] * abs(jets[2])
                fourth += family["center"] * jets[4]
                fourth_error += family["error"] * abs(jets[4])
            value_upper = rounded_up(base.base.base.exact_upper(value.real + value_error))
            second_upper = rounded_up(base.base.base.exact_upper(second.real + second_error))
            fourth_upper = rounded_up(base.base.base.exact_upper(fourth.real + fourth_error))
            sixth = rounded_up(sixth_upper(families, left, right, sigma))
            cell_upper = (step * value_upper + step**3 / 24 * second_upper +
                          step**5 / 1920 * fourth_upper + step**7 / 322560 * sixth)
            cell_remainder = step**7 / 322560 * sixth
            total += cell_upper
            remainder += cell_remainder
            if cell_file is not None:
                cell_file.write(json.dumps({
                    "index": index,
                    "left": str(left),
                    "right": str(right),
                    "midpoint": str(midpoint),
                    "step": str(step),
                    "value_upper": str(value_upper),
                    "second_upper": str(second_upper),
                    "fourth_upper": str(fourth_upper),
                    "sixth_upper": str(sixth),
                    "cell_upper": str(cell_upper),
                    "sixth_order_remainder_upper": str(cell_remainder),
                    "upper_semantics": "Arb enclosure rounded upward to an exact rational on the 10^-80 grid",
                }, sort_keys=True) + "\n")
    finally:
        if cell_file is not None:
            cell_file.close()
    return {
        "record": 3187,
        "status": "SIGNED_TAYLOR6_INTERVAL_DIAGNOSTIC",
        "cells": cells,
        "precision_bits": precision,
        "sigma": "-1/2",
        "total_upper": str(total),
        "sixth_order_remainder_upper": str(remainder),
        "total_upper_negative": total < 0,
        "formula": "h*f + h^3*f2/24 + h^5*f4/1920 + h^7*sup_abs_f6/322560",
        "rounding": "every serialized upper is rounded upward to the 10^-80 grid",
        "cell_output": str(cell_output) if cell_output is not None else None,
        "cell_output_format": "3187-cell-upper-jsonl-v1" if cell_output is not None else None,
        "nonclaims": ["not imported into Lean", "full-line tail missing", "no SourceRH", "no RH"],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--cells", type=int, default=2560)
    parser.add_argument("--precision", type=int, default=192)
    parser.add_argument("--output", type=Path, default=ROOT / "results/3187_signed_taylor6_interval.json")
    parser.add_argument("--cell-output", type=Path, default=None,
                        help="write one exact-rational JSONL upper record per cell")
    args = parser.parse_args()
    result = run(args.cells, args.precision, args.cell_output)
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
