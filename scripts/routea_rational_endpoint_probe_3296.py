"""3296: independent exact evaluator for the 3289 rational endpoint.

This mirrors the audited RatInterval/RatRect definitions in Lean.  It is a
diagnostic bridge only: its output is not imported into Lean by this script.
"""

from __future__ import annotations

import argparse
import json
import re
import struct
from fractions import Fraction as F
from math import factorial
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
PHASE_SOURCE = ROOT / "ConnesWeilRH/Dev/C1RouteARationalPhase3279.lean"
COEFFICIENT_SOURCE = ROOT / "ConnesWeilRH/Dev/C1RouteARepairedOwnerCorrectionM02680.lean"
STORED_WIDTH_SOURCE = ROOT / "ConnesWeilRH/Dev/C1RouteARationalCellBump3287.lean"

Interval = tuple[F, F]
Rect = tuple[F, F, F, F]


def interval_mul(left: Interval, right: Interval) -> Interval:
    values = [left[0] * right[0], left[0] * right[1], left[1] * right[0], left[1] * right[1]]
    return min(values), max(values)


def interval_add(left: Interval, right: Interval) -> Interval:
    return left[0] + right[0], left[1] + right[1]


def interval_pow(value: Interval, exponent: int) -> Interval:
    result: Interval = (F(1), F(1))
    for _ in range(exponent):
        result = interval_mul(result, value)
    return result


def rect_mul(left: Rect, right: Rect) -> Rect:
    left_re = (left[0], left[1])
    left_im = (left[2], left[3])
    right_re = (right[0], right[1])
    right_im = (right[2], right[3])
    real = interval_add(interval_mul(left_re, right_re), (-interval_mul(left_im, right_im)[1], -interval_mul(left_im, right_im)[0]))
    imag = interval_add(interval_mul(left_re, right_im), interval_mul(left_im, right_re))
    return real[0], real[1], imag[0], imag[1]


def rect_add(left: Rect, right: Rect) -> Rect:
    return left[0] + right[0], left[1] + right[1], left[2] + right[2], left[3] + right[3]


def rational_taylor_interval(x: F) -> Interval:
    total = sum((x**m / factorial(m) for m in range(30)), F(0))
    error = abs(x) ** 30 * F(31, factorial(30) * 30)
    return total - error, total + error


def phase_rect(angle: F) -> Rect:
    scaled = angle / 512
    real = sum(((-1) ** k) * scaled ** (2 * k) / factorial(2 * k) for k in range(13))
    imag = sum(((-1) ** k) * scaled ** (2 * k + 1) / factorial(2 * k + 1) for k in range(13))
    error = abs(scaled) ** 26 * F(27, factorial(26) * 26)
    return real - error, real + error, imag - error, imag + error


def phase_pow(angle: F) -> Rect:
    result = phase_rect(angle)
    for _ in range(9):
        result = rect_mul(result, result)
    return result


def parse_modulations() -> list[F]:
    source = PHASE_SOURCE.read_text(encoding="utf-8")
    body = source.split("def capturedModulationsRat3279", 1)[1].split("theorem capturedModulationsRat_cast3279", 1)[0]
    values: list[F] = []
    for token in re.findall(r"\(\((-?\d+)\s*:\s*ℚ\)\s*/\s*(\d+)\)|\(0\s*:\s*ℚ\)", body):
        if token[0]:
            values.append(F(int(token[0]), int(token[1])))
        else:
            values.append(F(0))
    if len(values) != 30:
        raise ValueError(f"expected 30 modulations, got {len(values)}")
    return values


def parse_widths() -> list[F]:
    source = STORED_WIDTH_SOURCE.read_text(encoding="utf-8")
    body = source.split("def storedWidthRat3287", 1)[1].split("theorem storedWidthRat_cast3287", 1)[0]
    values: list[F] = []
    for token in re.findall(r"\(\((\d+)\s*:\s*ℚ\)\s*/\s*(\d+)\)|\((\d+)\s*:\s*ℚ\)", body):
        if token[0]:
            values.append(F(int(token[0]), int(token[1])))
        elif token[2]:
            values.append(F(int(token[2])))
    if len(values) != 30:
        raise ValueError(f"expected 30 stored widths, got {len(values)}")
    return values


def binary64_bits_to_fraction(bits: str) -> F:
    value = struct.unpack(">d", int(bits, 16).to_bytes(8, "big"))[0]
    return F(*value.as_integer_ratio())


def parse_coefficients() -> list[tuple[F, F]]:
    source = COEFFICIENT_SOURCE.read_text(encoding="utf-8")
    body = source.split("noncomputable def record2680CorrectionCoefficient", 1)[1].split("]", 1)[0]
    values = [
        (binary64_bits_to_fraction(real), binary64_bits_to_fraction(imag))
        for real, imag in re.findall(r"⟨binary64Value2674\s+0x([0-9a-f]+),\s*binary64Value2674\s+0x([0-9a-f]+)⟩", body)
    ]
    if len(values) != 30:
        raise ValueError(f"expected 30 coefficient pairs, got {len(values)}")
    return values


def center(index: int) -> F:
    radius = F(65536001, 10000000)
    return -radius + F(2 * index + 1, 40960) * radius


def bump_interval(radius: F, position: F) -> Interval:
    if not position < radius:
        return F(0), F(0)
    t = 30 - 30 / (1 - (position / radius) ** 2)
    if abs(t / 8) <= 1:
        base = interval_pow(rational_taylor_interval(F(-1, 2)), 60)
        addend = interval_pow(rational_taylor_interval(t / 8), 8)
        return interval_mul(base, addend)
    base = interval_pow(rational_taylor_interval(F(-1, 2)), 76)
    return F(0), base[1]


def weight_interval(value: F) -> Interval:
    return interval_pow(rational_taylor_interval(-value / 120), 60)


def endpoint(index: int, modulations: list[F], widths: list[F], coefficients: list[tuple[F, F]]) -> F:
    x = center(index)
    aggregate: Rect = (F(0), F(0), F(0), F(0))
    for modulation, width, coefficient in zip(modulations, widths, coefficients):
        radius = width**2
        bump = bump_interval(radius, abs(x))
        coeff_rect: Rect = (coefficient[0], coefficient[0], coefficient[1], coefficient[1])
        bump_rect: Rect = (bump[0], bump[1], F(0), F(0))
        family = rect_mul(rect_mul(coeff_rect, bump_rect), phase_pow(modulation * x))
        aggregate = rect_add(aggregate, family)
    weight = weight_interval(x)
    weighted = rect_mul((weight[0], weight[1], F(0), F(0)), aggregate)
    return weighted[1]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--indices", type=int, nargs="+", default=[0, 16923, 40959])
    parser.add_argument("--output", type=Path, default=ROOT / "results/3296_routea_rational_endpoint_probe.json")
    args = parser.parse_args()
    modulations = parse_modulations()
    widths = parse_widths()
    coefficients = parse_coefficients()
    rows = [{"index": index, "rat_endpoint": str(endpoint(index, modulations, widths, coefficients))} for index in args.indices]
    result = {"record": 3296, "status": "DIAGNOSTIC_EXACT_RATIONAL_ENDPOINT_PROBE", "rows": rows, "lean_imported": False, "producer_go": False, "rh_claim": False}
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    for row in rows:
        print(row["index"], float(F(row["rat_endpoint"])))


if __name__ == "__main__":
    main()
