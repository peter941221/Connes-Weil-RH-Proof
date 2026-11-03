"""3238: diagnostic Taylor-6 replay for the formal weighted original function."""

from __future__ import annotations

import argparse
import json
from fractions import Fraction as F
from math import comb
from pathlib import Path

from flint import acb, arb, ctx

import routea_concrete_owner_taylor6_3204 as owner

ROOT = Path(__file__).resolve().parents[1]


def original_jets(family, coordinate, sigma, order):
    if abs(coordinate) >= family["r"]:
        return [acb(0) for _ in range(order + 1)]
    x = owner.taylor.base.base.base.lift(coordinate)
    weight_sigma = owner.taylor.base.base.base.lift(sigma)
    u = x / family["radius"]
    q = 1 - u * u
    if not q > 0:
        raise ValueError("unresolved interior deficit")
    exponential = acb(-30 / q + weight_sigma * x, family["theta"] * x).exp()
    bump = [
        sum((c * u**p for p, c in owner.taylor.POLYS[k].items()), arb(0))
        / (family["radius"] ** k * q ** (2 * k))
        for k in range(order + 1)
    ]
    lam = acb(0, family["theta"])
    raw = [
        sum(
            (comb(k, j) * lam ** (k - j) * bump[j]
             for j in range(k + 1)),
            acb(0),
        )
        for k in range(order + 1)
    ]
    return [
        exponential
        * sum(
            (comb(k, j) * weight_sigma ** (k - j) * raw[j]
             for j in range(k + 1)),
            acb(0),
        )
        for k in range(order + 1)
    ]


def interval_original_jets(family, left, right, sigma, order):
    midpoint = (left + right) / 2
    half = (right - left) / 2
    x = arb(owner.taylor.base.base.base.lift(midpoint),
            owner.taylor.base.base.base.lift(abs(half)))
    radius = owner.taylor.base.base.base.lift(family["r"])
    u = x / radius
    q = 1 - u * u
    exponent = acb(-30 / q + owner.taylor.base.base.base.lift(sigma) * x,
                   family["theta"] * x)
    exponential = exponent.exp()
    bumps = [
        sum((c * u**p for p, c in owner.taylor.POLYS[k].items()), arb(0))
        / (radius**k * q**(2 * k))
        for k in range(order + 1)
    ]
    lam = acb(0, family["theta"])
    raw = [
        sum((comb(k, j) * lam**(k - j) * bumps[j]
             for j in range(k + 1)), acb(0))
        for k in range(order + 1)
    ]
    weight_sigma = owner.taylor.base.base.base.lift(sigma)
    return [
        exponential
        * sum((comb(k, j) * weight_sigma**(k - j) * raw[j]
               for j in range(k + 1)), acb(0))
        for k in range(order + 1)
    ]


def sixth_upper(families, left, right, sigma):
    aggregate = acb(0)
    fallback = arb(0)
    for family in families:
        if left > -family["r"] and right < family["r"]:
            jet = interval_original_jets(family, left, right, sigma, 6)[6]
            if jet.is_finite():
                aggregate += family["center"] * jet
            else:
                fallback += family["scale"] * owner.taylor.base.base.envelope(
                    family, left, right, sigma
                )
        elif right <= -family["r"] or left >= family["r"]:
            continue
        else:
            fallback += family["scale"] * owner.taylor.base.base.envelope(
                family, left, right, sigma
            )
    return owner.taylor.base.base.base.exact_upper(abs(aggregate) + fallback)


def run(cells: int, precision: int, cell_output: Path | None = None) -> dict:
    ctx.prec = precision
    families = owner.load_owner_families()
    sigma = F(-1, 2)
    radius = owner.taylor.base.base.base.RADIUS
    step = 2 * radius / cells
    total = F(0)
    remainder = F(0)
    minimum = None
    cell_file = None
    if cell_output is not None:
        cell_output.parent.mkdir(parents=True, exist_ok=True)
        cell_file = cell_output.open("w", encoding="utf-8")
        cell_file.write(json.dumps({
            "format": "3238-weighted-original-cell-upper-jsonl-v1",
            "record": 3238,
            "status": "WEIGHTED_ORIGINAL_TAYLOR6_DIAGNOSTIC",
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
            left = -radius + index * step
            right = left + step
            midpoint = (left + right) / 2
            value = acb(0)
            second = acb(0)
            fourth = acb(0)
            for family in families:
                jets = original_jets(family, midpoint, sigma, 4)
                value += family["center"] * jets[0]
                second += family["center"] * jets[2]
                fourth += family["center"] * jets[4]
            value_upper = owner.taylor.rounded_up(
                owner.taylor.base.base.base.exact_upper(value.real)
            )
            second_upper = owner.taylor.rounded_up(
                owner.taylor.base.base.base.exact_upper(second.real)
            )
            fourth_upper = owner.taylor.rounded_up(
                owner.taylor.base.base.base.exact_upper(fourth.real)
            )
            sixth = owner.taylor.rounded_up(sixth_upper(families, left, right, sigma))
            cell_upper = (
                step * value_upper
                + step**3 * second_upper / 24
                + step**5 * fourth_upper / 1920
                + step**7 * sixth / 322560
            )
            remainder_upper = step**7 * sixth / 322560
            total += cell_upper
            remainder += remainder_upper
            if minimum is None or cell_upper < minimum[1]:
                minimum = (index, cell_upper, value_upper)
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
                    "sixth_order_remainder_upper": str(remainder_upper),
                    "upper_semantics": "Arb enclosure rounded upward to an exact rational on the 10^-80 grid",
                }, sort_keys=True) + "\n")
    finally:
        if cell_file is not None:
            cell_file.close()
    return {
        "record": 3238,
        "status": "WEIGHTED_ORIGINAL_TAYLOR6_DIAGNOSTIC",
        "cells": cells,
        "precision_bits": precision,
        "sigma": str(sigma),
        "total_upper": str(total),
        "sixth_order_remainder_upper": str(remainder),
        "total_upper_negative": total < 0,
        "minimum_cell": {
            "index": minimum[0],
            "cell_upper": str(minimum[1]),
            "value_upper": str(minimum[2]),
        },
        "formal_target": "weightedExternal3201 original function",
        "lean_certificate": False,
        "full_line_tail_included": False,
        "producer_go": False,
        "rh_claim": False,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--cells", type=int, default=40960)
    parser.add_argument("--precision", type=int, default=192)
    parser.add_argument(
        "--output",
        type=Path,
        default=ROOT / "results/3238_weighted_original_taylor6.json",
    )
    parser.add_argument("--cell-output", type=Path, default=None)
    args = parser.parse_args()
    result = run(args.cells, args.precision, args.cell_output)
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
