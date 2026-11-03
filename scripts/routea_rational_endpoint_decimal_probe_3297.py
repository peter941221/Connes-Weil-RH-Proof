"""3297: fast, non-certified magnitude probe for the 3289 rational endpoint.

This mirrors the 3289 construction with high-precision Decimal arithmetic.
It is intentionally not an enclosure and must not be imported into Lean.  Its
purpose is to measure whether the audited rational rectangle is plausibly close
enough to dominate the 3273 Arb value upper.
"""

from __future__ import annotations

import argparse
import json
import re
import struct
from decimal import Decimal, localcontext
from fractions import Fraction as F
from math import factorial
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
PHASE_SOURCE = ROOT / "ConnesWeilRH/Dev/C1RouteARationalPhase3279.lean"
COEFFICIENT_SOURCE = ROOT / "ConnesWeilRH/Dev/C1RouteARepairedOwnerCorrectionM02680.lean"
STORED_WIDTH_SOURCE = ROOT / "ConnesWeilRH/Dev/C1RouteARationalCellBump3287.lean"
CELLS_SOURCE = ROOT / "results/3238_weighted_original_taylor6_40960.jsonl"

Interval = tuple[Decimal, Decimal]
Rect = tuple[Decimal, Decimal, Decimal, Decimal]


def decimal_pow(value: Decimal, exponent: int) -> Decimal:
    return Decimal(1) if exponent == 0 else value ** exponent


def dfrac(value: F) -> Decimal:
    return Decimal(value.numerator) / Decimal(value.denominator)


def interval_mul(left: Interval, right: Interval) -> Interval:
    values = [left[0] * right[0], left[0] * right[1], left[1] * right[0], left[1] * right[1]]
    return min(values), max(values)


def interval_add(left: Interval, right: Interval) -> Interval:
    return left[0] + right[0], left[1] + right[1]


def interval_pow(value: Interval, exponent: int) -> Interval:
    result: Interval = (Decimal(1), Decimal(1))
    for _ in range(exponent):
        result = interval_mul(result, value)
    return result


def rect_mul(left: Rect, right: Rect) -> Rect:
    left_re, left_im = (left[0], left[1]), (left[2], left[3])
    right_re, right_im = (right[0], right[1]), (right[2], right[3])
    im_product = interval_mul(left_im, right_im)
    real = interval_add(interval_mul(left_re, right_re), (-im_product[1], -im_product[0]))
    imag = interval_add(interval_mul(left_re, right_im), interval_mul(left_im, right_re))
    return real[0], real[1], imag[0], imag[1]


def rect_add(left: Rect, right: Rect) -> Rect:
    return left[0] + right[0], left[1] + right[1], left[2] + right[2], left[3] + right[3]


def rational_taylor_interval(x: Decimal) -> Interval:
    total = sum((decimal_pow(x, m) / Decimal(factorial(m)) for m in range(30)), Decimal(0))
    error = decimal_pow(abs(x), 30) * Decimal(31) / (Decimal(factorial(30)) * Decimal(30))
    return total - error, total + error


def phase_rect(angle: Decimal) -> Rect:
    scaled = angle / Decimal(512)
    real = sum((((-1) ** k) * decimal_pow(scaled, 2 * k) / Decimal(factorial(2 * k)) for k in range(13)), Decimal(0))
    imag = sum((((-1) ** k) * decimal_pow(scaled, 2 * k + 1) / Decimal(factorial(2 * k + 1)) for k in range(13)), Decimal(0))
    error = decimal_pow(abs(scaled), 26) * Decimal(27) / (Decimal(factorial(26)) * Decimal(26))
    return real - error, real + error, imag - error, imag + error


def phase_pow(angle: Decimal) -> Rect:
    result = phase_rect(angle)
    for _ in range(9):
        result = rect_mul(result, result)
    return result


def parse_modulations() -> list[F]:
    source = PHASE_SOURCE.read_text(encoding="utf-8")
    body = source.split("def capturedModulationsRat3279", 1)[1].split("theorem capturedModulationsRat_cast3279", 1)[0]
    values: list[F] = []
    for token in re.findall(r"\(\((-?\d+)\s*:\s*ℚ\)\s*/\s*(\d+)\)|\(0\s*:\s*ℚ\)", body):
        values.append(F(int(token[0]), int(token[1])) if token[0] else F(0))
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


def bump_interval(radius: Decimal, position: Decimal) -> Interval:
    if not position < radius:
        return Decimal(0), Decimal(0)
    t = Decimal(30) - Decimal(30) / (Decimal(1) - (position / radius) ** 2)
    if abs(t / Decimal(8)) <= Decimal(1):
        base = interval_pow(rational_taylor_interval(Decimal(-1) / Decimal(2)), 60)
        addend = interval_pow(rational_taylor_interval(t / Decimal(8)), 8)
        return interval_mul(base, addend)
    base = interval_pow(rational_taylor_interval(Decimal(-1) / Decimal(2)), 76)
    return Decimal(0), base[1]


def endpoint(index: int, modulations: list[F], widths: list[F], coefficients: list[tuple[F, F]]) -> Decimal:
    x = dfrac(center(index))
    aggregate: Rect = (Decimal(0), Decimal(0), Decimal(0), Decimal(0))
    for modulation, width, coefficient in zip(modulations, widths, coefficients):
        radius = dfrac(width) ** 2
        bump = bump_interval(radius, abs(x))
        coeff_rect: Rect = (dfrac(coefficient[0]), dfrac(coefficient[0]), dfrac(coefficient[1]), dfrac(coefficient[1]))
        bump_rect: Rect = (bump[0], bump[1], Decimal(0), Decimal(0))
        family = rect_mul(rect_mul(coeff_rect, bump_rect), phase_pow(dfrac(modulation) * x))
        aggregate = rect_add(aggregate, family)
    weight = interval_pow(rational_taylor_interval(-x / Decimal(120)), 60)
    weighted = rect_mul((weight[0], weight[1], Decimal(0), Decimal(0)), aggregate)
    return weighted[1]


def parse_sidecar(index: int) -> Decimal:
    with CELLS_SOURCE.open(encoding="utf-8") as stream:
        header = next(stream)
        for row in stream:
            parsed = json.loads(row)
            if parsed["index"] == index:
                return dfrac(F(parsed["value_upper"]))
    raise ValueError(f"index {index} is absent from {CELLS_SOURCE}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--indices", type=int, nargs="+", default=[16923])
    parser.add_argument("--precision", type=int, default=100)
    parser.add_argument("--output", type=Path, default=ROOT / "results/3297_routea_decimal_endpoint_probe.json")
    args = parser.parse_args()
    with localcontext() as context:
        context.prec = args.precision
        modulations = parse_modulations()
        widths = parse_widths()
        coefficients = parse_coefficients()
        rows = []
        for index in args.indices:
            rational_upper = endpoint(index, modulations, widths, coefficients)
            arb_upper = parse_sidecar(index)
            rows.append({
                "index": index,
                "rational_upper_decimal_probe": str(rational_upper),
                "arb_value_upper": str(arb_upper),
                "rational_minus_arb": str(rational_upper - arb_upper),
                "rational_probe_dominates_arb": rational_upper >= arb_upper,
            })
    result = {
        "record": 3297,
        "status": "DIAGNOSTIC_DECIMAL_MIRROR_ENDPOINT_NOT_CERTIFIED",
        "precision_digits": args.precision,
        "rows": rows,
        "lean_imported": False,
        "exact_rational_replay": False,
        "producer_go": False,
        "rh_claim": False,
        "nonclaims": [
            "Decimal arithmetic is not directed rounding",
            "rows do not prove ratCellValueUpper3289 dominance",
            "rows do not prove any Lean theorem",
        ],
    }
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
