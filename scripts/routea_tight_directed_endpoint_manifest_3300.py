"""3300: directed-rounding mirror of ``ratCellValueUpperTight3298``.

Every rational input is enclosed before use.  Decimal interval operations use
floor rounding for lower endpoints and ceiling rounding for upper endpoints.
The final endpoint is rounded upward to the 10^-80 grid.  This is still an
external replay: the resulting rows are not imported into Lean.
"""

from __future__ import annotations

import argparse
import json
import hashlib
from decimal import (ROUND_CEILING, ROUND_FLOOR, Context, Decimal, localcontext)
from fractions import Fraction as F
from pathlib import Path

import routea_rational_endpoint_decimal_probe_3297 as base


ROOT = Path(__file__).resolve().parents[1]
CELLS = 40960
BLOCK_SIZE = 256
GRID_DENOM = 10**80

Interval = tuple[Decimal, Decimal]
Rect = tuple[Decimal, Decimal, Decimal, Decimal]


class Directed:
    def __init__(self, precision: int):
        self.floor = Context(prec=precision, rounding=ROUND_FLOOR)
        self.ceil = Context(prec=precision, rounding=ROUND_CEILING)
        self.factorials = [factorial_of(index) for index in range(31)]

    def point(self, value: F) -> Interval:
        numerator = Decimal(value.numerator)
        denominator = Decimal(value.denominator)
        return (
            self.floor.divide(numerator, denominator),
            self.ceil.divide(numerator, denominator),
        )

    def add(self, left: Interval, right: Interval) -> Interval:
        return (
            self.floor.add(left[0], right[0]),
            self.ceil.add(left[1], right[1]),
        )

    def sub(self, left: Interval, right: Interval) -> Interval:
        return (
            self.floor.subtract(left[0], right[1]),
            self.ceil.subtract(left[1], right[0]),
        )

    def mul(self, left: Interval, right: Interval) -> Interval:
        lows = [
            self.floor.multiply(left[0], right[0]),
            self.floor.multiply(left[0], right[1]),
            self.floor.multiply(left[1], right[0]),
            self.floor.multiply(left[1], right[1]),
        ]
        highs = [
            self.ceil.multiply(left[0], right[0]),
            self.ceil.multiply(left[0], right[1]),
            self.ceil.multiply(left[1], right[0]),
            self.ceil.multiply(left[1], right[1]),
        ]
        return min(lows), max(highs)

    def pow(self, value: Interval, exponent: int) -> Interval:
        result = (Decimal(1), Decimal(1))
        for _ in range(exponent):
            result = self.mul(result, value)
        return result

    def div_positive(self, value: Interval, denominator: F) -> Interval:
        den = self.point(denominator)
        return (
            self.floor.divide(value[0], den[1]),
            self.ceil.divide(value[1], den[0]),
        )

    def abs(self, value: Interval) -> Interval:
        if value[0] >= 0:
            return value
        if value[1] <= 0:
            return (-value[1], -value[0])
        return (Decimal(0), max(-value[0], value[1]))

    def taylor(self, value: Interval) -> Interval:
        total = (Decimal(0), Decimal(0))
        for exponent in range(30):
            term = self.div_positive(self.pow(value, exponent), F(self.factorials[exponent], 1))
            total = self.add(total, term)
        magnitude = self.pow(self.abs(value), 30)
        error = self.mul(
            magnitude,
            self.point(F(31, self.factorials[30] * 30)),
        )
        lower = self.sub(total, error)
        upper = self.add(total, error)
        return lower[0], upper[1]


def factorial_of(value: int) -> int:
    result = 1
    for factor in range(2, value + 1):
        result *= factor
    return result


def interval_add(directed: Directed, left: Rect, right: Rect) -> Rect:
    real = directed.add((left[0], left[1]), (right[0], right[1]))
    imag = directed.add((left[2], left[3]), (right[2], right[3]))
    return (
        real[0], real[1], imag[0], imag[1]
    )


def rect_mul(directed: Directed, left: Rect, right: Rect) -> Rect:
    real = directed.sub(
        directed.mul((left[0], left[1]), (right[0], right[1])),
        directed.mul((left[2], left[3]), (right[2], right[3])),
    )
    imag = directed.add(
        directed.mul((left[0], left[1]), (right[2], right[3])),
        directed.mul((left[2], left[3]), (right[0], right[1])),
    )
    return real[0], real[1], imag[0], imag[1]


def phase_rect(directed: Directed, angle: F) -> Rect:
    scaled = directed.point(angle / 512)
    real = (Decimal(1), Decimal(1))
    imag = scaled
    for k in range(1, 13):
        real_term = directed.div_positive(
            directed.pow(scaled, 2 * k), F(factorial_of(2 * k), 1)
        )
        imag_term = directed.div_positive(
            directed.pow(scaled, 2 * k + 1), F(factorial_of(2 * k + 1), 1)
        )
        real = directed.sub(real, real_term) if k % 2 else directed.add(real, real_term)
        imag = directed.sub(imag, imag_term) if k % 2 else directed.add(imag, imag_term)
    error = directed.mul(
        directed.pow(directed.abs(scaled), 26),
        directed.point(F(27, factorial_of(26) * 26)),
    )
    error_point = (error[1], error[1])
    real_with_error = (
        directed.sub(real, error_point)[0],
        directed.add(real, error_point)[1],
    )
    imag_with_error = (
        directed.sub(imag, error_point)[0],
        directed.add(imag, error_point)[1],
    )
    return (
        real_with_error[0],
        real_with_error[1],
        imag_with_error[0],
        imag_with_error[1],
    )


def phase_pow(directed: Directed, angle: F) -> Rect:
    result = phase_rect(directed, angle)
    for _ in range(9):
        result = rect_mul(directed, result, result)
    return result


def bump(
    directed: Directed,
    radius: F,
    position: F,
    base60: Interval,
    base188: Interval,
) -> Interval:
    if not position < radius:
        return (Decimal(0), Decimal(0))
    t = F(30) - F(30, 1) / (F(1) - (position / radius) ** 2)
    if abs(t / 8) <= 1:
        power = 8
    elif F(-16) <= t:
        power = 16
    elif F(-32) <= t:
        power = 32
    elif F(-64) <= t:
        power = 64
    else:
        return (Decimal(0), base188[1])
    return directed.mul(
        base60,
        directed.pow(directed.taylor(directed.point(t / power)), power),
    )


def endpoint(
    directed: Directed,
    index: int,
    modulations: list[F],
    widths: list[F],
    coefficients: list[tuple[F, F]],
    base60: Interval,
    base188: Interval,
) -> Decimal:
    center = base.center(index)
    position = abs(center)
    aggregate = (Decimal(0), Decimal(0))
    for modulation, width, coefficient in zip(modulations, widths, coefficients):
        radius = width**2
        bump_interval = bump(directed, radius, position, base60, base188)
        if bump_interval[1] == 0:
            continue
        phase = phase_pow(directed, modulation * center)
        coefficient_re = directed.point(coefficient[0])
        coefficient_im = directed.point(coefficient[1])
        phase_re = directed.sub(
            directed.mul(coefficient_re, (phase[0], phase[1])),
            directed.mul(coefficient_im, (phase[2], phase[3])),
        )
        aggregate = directed.add(
            aggregate,
            directed.mul(bump_interval, phase_re),
        )
    weight = directed.pow(directed.taylor(directed.point(-center / 120)), 60)
    return directed.mul(weight, aggregate)[1]


def ceil_grid(value: Decimal) -> F:
    numerator, denominator = value.as_integer_ratio()
    scaled = numerator * GRID_DENOM
    return F(-((-scaled) // denominator), GRID_DENOM)


def decimal_from_fraction(value: F) -> str:
    with localcontext() as context:
        context.prec = 140
        return format(Decimal(value.numerator) / Decimal(value.denominator), "f")


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--precision", type=int, default=110)
    parser.add_argument("--start", type=int, default=0)
    parser.add_argument("--count", type=int, default=CELLS)
    parser.add_argument(
        "--output",
        type=Path,
        default=ROOT / "results/3300_routea_directed_endpoint_manifest.json",
    )
    args = parser.parse_args()
    if args.start < 0 or args.count < 0 or args.start + args.count > CELLS:
        raise ValueError("requested range is outside the 40960-cell grid")

    directed = Directed(args.precision)
    modulations = base.parse_modulations()
    widths = base.parse_widths()
    coefficients = base.parse_coefficients()
    base_interval = directed.taylor(directed.point(F(-1, 2)))
    base60 = directed.pow(base_interval, 60)
    base188 = directed.pow(base_interval, 188)
    rows: list[dict[str, object]] = []
    for index in range(args.start, args.start + args.count):
        upper = endpoint(
            directed, index, modulations, widths, coefficients, base60, base188
        )
        rounded = ceil_grid(upper)
        rows.append(
            {
                "index": index,
                "value_upper": str(rounded),
                "value_upper_decimal": decimal_from_fraction(rounded),
            }
        )

    result = {
        "record": 3300,
        "status": "DIRECTED_DECIMAL_ENDPOINT_REPLAY",
        "cells": CELLS,
        "start": args.start,
        "count": args.count,
        "precision_digits": args.precision,
        "rounding": "outward Decimal intervals, then upward 10^-80 grid",
        "formula": "ratCellValueUpperTight3298 mirror",
        "all_cells_replayed": args.start == 0 and args.count == CELLS,
        "lean_endpoint_dominance_closed": False,
        "lean_manifest_imported": False,
        "producer_go": False,
        "rh_claim": False,
        "input_sha256": {
            "ConnesWeilRH/Dev/C1RouteARationalTightTail3298.lean": sha256(
                ROOT / "ConnesWeilRH/Dev/C1RouteARationalTightTail3298.lean"
            ),
            "ConnesWeilRH/Dev/C1RouteARationalRealProjection3298.lean": sha256(
                ROOT / "ConnesWeilRH/Dev/C1RouteARationalRealProjection3298.lean"
            ),
            "ConnesWeilRH/Dev/C1RouteARationalTightCell3298.lean": sha256(
                ROOT / "ConnesWeilRH/Dev/C1RouteARationalTightCell3298.lean"
            ),
        },
        "rows": rows,
        "nonclaims": [
            "directed Decimal replay is external evidence, not a Lean theorem",
            "the rows have not been imported into Lean",
            "the full-line tail and producer bridge remain open",
        ],
    }
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(
        json.dumps(
            {
                key: result[key]
                for key in ("record", "status", "start", "count", "all_cells_replayed")
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
