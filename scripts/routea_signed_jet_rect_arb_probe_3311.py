"""Arb-backed numeric probe for the order-0 3310 rectangle endpoint."""

from __future__ import annotations

import argparse
import json
from fractions import Fraction as F
from functools import reduce
from math import factorial
from pathlib import Path

from flint import arb, ctx

import routea_signed_jet_rect_manifest_3311 as exact

ROOT = Path(__file__).resolve().parents[1]


def q(value: F) -> arb:
    return arb(value.numerator) / value.denominator


class AInterval:
    def __init__(self, lo: arb, hi: arb):
        self.lo = lo
        self.hi = hi

    def add(self, other: "AInterval") -> "AInterval":
        return AInterval(self.lo + other.lo, self.hi + other.hi)

    def sub(self, other: "AInterval") -> "AInterval":
        return AInterval(self.lo - other.hi, self.hi - other.lo)

    def mul(self, other: "AInterval") -> "AInterval":
        values = [
            self.lo * other.lo,
            self.lo * other.hi,
            self.hi * other.lo,
            self.hi * other.hi,
        ]
        return AInterval(
            reduce(lambda left, right: left.min(right), values),
            reduce(lambda left, right: left.max(right), values),
        )

    def pow_nat(self, exponent: int) -> "AInterval":
        result = AInterval(arb(1), arb(1))
        for _ in range(exponent):
            result = result.mul(self)
        return result


class ARect:
    def __init__(self, re_lo: arb, re_hi: arb, im_lo: arb, im_hi: arb):
        self.re_lo = re_lo
        self.re_hi = re_hi
        self.im_lo = im_lo
        self.im_hi = im_hi

    def add(self, other: "ARect") -> "ARect":
        return ARect(
            self.re_lo + other.re_lo,
            self.re_hi + other.re_hi,
            self.im_lo + other.im_lo,
            self.im_hi + other.im_hi,
        )

    def mul(self, other: "ARect") -> "ARect":
        real = AInterval(self.re_lo, self.re_hi).mul(
            AInterval(other.re_lo, other.re_hi)
        ).sub(
            AInterval(self.im_lo, self.im_hi).mul(
                AInterval(other.im_lo, other.im_hi)
            )
        )
        imag = AInterval(self.re_lo, self.re_hi).mul(
            AInterval(other.im_lo, other.im_hi)
        ).add(
            AInterval(self.im_lo, self.im_hi).mul(
                AInterval(other.re_lo, other.re_hi)
            )
        )
        return ARect(real.lo, real.hi, imag.lo, imag.hi)

    def pow_sq(self, exponent: int) -> "ARect":
        result = self
        for _ in range(exponent):
            result = result.mul(result)
        return result


def taylor_interval(x: F) -> AInterval:
    total = sum((q(x**m / factorial(m)) for m in range(30)), arb(0))
    error = q(abs(x) ** 30 * F(31, factorial(30) * 30))
    return AInterval(total - error, total + error)


def phase_rect(angle: F) -> ARect:
    x = angle / 512
    real = sum((q((-1) ** k * x ** (2 * k) / factorial(2 * k)) for k in range(13)), arb(0))
    imag = sum((q((-1) ** k * x ** (2 * k + 1) / factorial(2 * k + 1)) for k in range(13)), arb(0))
    error = q(abs(x) ** 26 * F(27, factorial(26) * 26))
    return ARect(real - error, real + error, imag - error, imag + error)


def bump_interval(radius: F, position: F) -> AInterval:
    if abs(position) >= radius:
        return AInterval(arb(0), arb(0))
    t = F(30) - F(30) / (1 - (position / radius) ** 2)
    base = taylor_interval(F(-1, 2)).pow_nat(60)
    for denominator in (8, 16, 32, 64):
        if abs(t / denominator) <= 1:
            return base.mul(taylor_interval(t / denominator).pow_nat(denominator))
    return AInterval(arb(0), base.pow_nat(188).hi)


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


def bump_jet_interval(order: int, radius: F, position: F) -> AInterval:
    if abs(position) >= radius:
        return AInterval(arb(0), arb(0))
    u = position / radius
    deficit = 1 - u**2
    factor = deficit ** (-2 * order) * bump_numerator(order, u) / radius**order
    return bump_interval(radius, position).mul(
        AInterval(q(factor), q(factor))
    )


def cell_weight_interval(center: F) -> AInterval:
    return taylor_interval(-center / 120).pow_nat(60)


def cell_family_rects(index: int, order: int) -> list[ARect]:
    center = -exact.GRID + F(2 * index + 1) * exact.GRID / exact.CELLS
    family_rects = []
    weight = cell_weight_interval(center)
    for family in range(30):
        radius = exact.WIDTHS[family] ** 2
        weighted_phase = ARect(
            weight.lo,
            weight.hi,
            arb(0), arb(0)
        ).mul(phase_rect(exact.MODULATIONS[family] * center).pow_sq(9))
        family_rect = ARect(arb(0), arb(0), arb(0), arb(0))
        lam = ARect(q(F(-1, 2)), q(F(-1, 2)), q(exact.MODULATIONS[family]), q(exact.MODULATIONS[family]))
        for index_in_jet in range(order + 1):
            choose = q(F(factorial(order), factorial(index_in_jet) * factorial(order - index_in_jet)))
            term = ARect(choose, choose, arb(0), arb(0))
            lam_power = ARect(arb(1), arb(1), arb(0), arb(0))
            for _ in range(index_in_jet):
                lam_power = lam_power.mul(lam)
            term = term.mul(lam_power.mul(weighted_phase))
            bump = bump_jet_interval(order - index_in_jet, radius, center)
            term = term.mul(ARect(bump.lo, bump.hi, arb(0), arb(0)))
            family_rect = family_rect.add(term)
        unit = family_rect
        real, imag = exact.COEFFICIENTS[family]
        family_rects.append(ARect(q(real), q(real), q(imag), q(imag)).mul(unit))
    return family_rects


def cell_rect(index: int, order: int) -> ARect:
    result = ARect(arb(0), arb(0), arb(0), arb(0))
    for family_rect in cell_family_rects(index, order):
        result = result.add(family_rect)
    return result


def exact_upper(value: arb) -> F:
    return F(str(value.upper().fmpq()))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--start", type=int, default=0)
    parser.add_argument("--cells", type=int, default=256)
    parser.add_argument("--order", type=int, default=0, choices=(0, 2, 4))
    parser.add_argument("--precision", type=int, default=192)
    parser.add_argument("--output", type=Path, default=ROOT / "results/3311_signed_jet_rect_arb_probe.json")
    args = parser.parse_args()
    ctx.prec = args.precision
    block = ARect(arb(0), arb(0), arb(0), arb(0))
    rows = []
    for offset in range(args.cells):
        index = args.start + offset
        rect = cell_rect(index, args.order)
        block = block.add(rect)
        rows.append({"index": index, "re_hi": str(exact_upper(rect.re_hi))})
    result = {
        "record": 3311,
        "status": "ARB_SIGNED_JET_RECTANGLE_PROBE",
        "cells": args.cells,
        "start": args.start,
        "precision_bits": args.precision,
        "block_re_hi": str(exact_upper(block.re_hi)),
        "rows": rows,
        "order": args.order,
        "formula_source": "C1RouteARationalSignedJetRect3310 finite rational definitions",
        "lean_imported": False,
        "rh_claim": False,
    }
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
