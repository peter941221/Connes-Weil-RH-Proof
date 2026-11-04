"""Exact-Fraction mirror of the 3310 family rectangles for cross-checking Arb."""

from __future__ import annotations

import argparse
import json
from fractions import Fraction as F
from math import factorial
from pathlib import Path

import routea_signed_jet_rect_manifest_3311 as exact

ROOT = Path(__file__).resolve().parents[1]


def rect_pow_nat(value: exact.Rect, exponent: int) -> exact.Rect:
    result = exact.Rect(F(1), F(1), F(0), F(0))
    for _ in range(exponent):
        result = result.mul(value)
    return result


def bump_numerator(order: int, u: F) -> F:
    values = {
        0: F(1),
        1: -60 * u,
        2: -60 + 3480 * u**2 + 180 * u**4,
        3: 10080 * u - 193680 * u**3 - 31680 * u**5 - 720 * u**7,
        4: 10080 - 1085040 * u**2 + 10189440 * u**4 + 3575520 * u**6 + 266400 * u**8 + 3600 * u**10,
        5: -2613600 * u + 92678400 * u**3 - 493207200 * u**5 - 320371200 * u**7 - 51703200 * u**9 - 2361600 * u**11 - 21600 * u**13,
        6: -2613600 + 387806400 * u**2 - 6679584000 * u**4 + 20842228800 * u**6 + 24232824000 * u**8 + 7137633600 * u**10 + 714873600 * u**12 + 22680000 * u**14 + 151200 * u**16,
    }
    return values[order]


def bump_jet_interval(order: int, radius: F, position: F) -> exact.Interval:
    if abs(position) >= radius:
        return exact.Interval(F(0), F(0))
    u = position / radius
    deficit = 1 - u**2
    factor = deficit ** (-2 * order) * bump_numerator(order, u) / radius**order
    return exact.bump_interval(radius, position).mul(
        exact.Interval(factor, factor)
    )


def family_rect(index: int, order: int, family: int) -> exact.Rect:
    center = -exact.GRID + F(2 * index + 1) * exact.GRID / exact.CELLS
    radius = exact.WIDTHS[family] ** 2
    weighted_phase = exact.weighted_phase_rect(index, family)
    lam = exact.Rect(F(-1, 2), F(-1, 2), exact.MODULATIONS[family], exact.MODULATIONS[family])
    family_rect = exact.Rect(F(0), F(0), F(0), F(0))
    for jet_index in range(order + 1):
        choose = F(factorial(order), factorial(jet_index) * factorial(order - jet_index))
        term = exact.Rect(choose, choose, F(0), F(0))
        term = term.mul(rect_pow_nat(lam, jet_index).mul(weighted_phase))
        bump = bump_jet_interval(order - jet_index, radius, center)
        term = term.mul(exact.Rect(bump.lo, bump.hi, F(0), F(0)))
        family_rect = family_rect.add(term)
    real, imag = exact.COEFFICIENTS[family]
    return exact.Rect(real, real, imag, imag).mul(family_rect)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--start", type=int, default=0)
    parser.add_argument("--cells", type=int, default=1)
    parser.add_argument("--order", type=int, default=2, choices=(0, 2, 4))
    parser.add_argument("--output", type=Path, default=ROOT / "results/3318_exact_family_probe.json")
    args = parser.parse_args()
    rows = []
    for index in range(args.start, args.start + args.cells):
        family_rows = [
            {"family": family, "re_hi": str(family_rect(index, args.order, family).re_hi)}
            for family in range(30)
        ]
        rows.append({"index": index, "families": family_rows})
    result = {
        "record": 3318,
        "status": "EXACT_FRACTION_3310_FAMILY_RECTANGLE",
        "start": args.start,
        "cells": args.cells,
        "order": args.order,
        "rows": rows,
        "lean_imported": False,
        "rh_claim": False,
    }
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"record": 3318, "start": args.start, "cells": args.cells, "order": args.order}, indent=2))


if __name__ == "__main__":
    main()
