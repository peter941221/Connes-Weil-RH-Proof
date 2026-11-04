"""3311 generator-side mirror for the exact order-0 signed-jet rectangles.

This mirrors the finite rational operations in
C1RouteARationalSignedJetRect3310.lean. It does not import JSON into Lean;
the output is diagnostic input for a later arithmetic mirror.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from fractions import Fraction as F
from math import factorial
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
GRID = F(65536001, 10000000)
CELLS = 40960


@dataclass(frozen=True)
class Interval:
    lo: F
    hi: F

    def add(self, other: "Interval") -> "Interval":
        return Interval(self.lo + other.lo, self.hi + other.hi)

    def sub(self, other: "Interval") -> "Interval":
        return Interval(self.lo - other.hi, self.hi - other.lo)

    def mul(self, other: "Interval") -> "Interval":
        values = [
            self.lo * other.lo,
            self.lo * other.hi,
            self.hi * other.lo,
            self.hi * other.hi,
        ]
        return Interval(min(values), max(values))

    def pow_nat(self, exponent: int) -> "Interval":
        result = Interval(F(1), F(1))
        for _ in range(exponent):
            result = result.mul(self)
        return result


@dataclass(frozen=True)
class Rect:
    re_lo: F
    re_hi: F
    im_lo: F
    im_hi: F

    def mul(self, other: "Rect") -> "Rect":
        real = Interval(self.re_lo, self.re_hi).mul(
            Interval(other.re_lo, other.re_hi)
        ).sub(
            Interval(self.im_lo, self.im_hi).mul(
                Interval(other.im_lo, other.im_hi)
            )
        )
        imag = Interval(self.re_lo, self.re_hi).mul(
            Interval(other.im_lo, other.im_hi)
        ).add(
            Interval(self.im_lo, self.im_hi).mul(
                Interval(other.re_lo, other.re_hi)
            )
        )
        return Rect(real.lo, real.hi, imag.lo, imag.hi)

    def add(self, other: "Rect") -> "Rect":
        return Rect(
            self.re_lo + other.re_lo,
            self.re_hi + other.re_hi,
            self.im_lo + other.im_lo,
            self.im_hi + other.im_hi,
        )

    def pow_sq(self, exponent: int) -> "Rect":
        result = self
        for _ in range(exponent):
            result = result.mul(result)
        return result


def taylor_interval(x: F) -> Interval:
    total = sum((x**m / factorial(m) for m in range(30)), F(0))
    error = abs(x) ** 30 * F(31, factorial(30) * 30)
    return Interval(total - error, total + error)


def parse_rat(token: str) -> F:
    token = token.strip().replace(" ", "")
    if "/" in token:
        numerator, denominator = token.split("/", 1)
        return F(int(numerator), int(denominator))
    return F(int(token), 1)


WIDTHS = [
    F(3602879701896397, 2251799813685248),
    F(517913957147607, 281474976710656),
    F(1170935903116329, 562949953421312),
    F(5224175567749775, 2251799813685248),
    F(1441151880758559, 562949953421312),
    F(3783023686991217, 2251799813685248),
    F(2),
    F(5224175567749775, 2251799813685248),
] + [F(3963167672086037, 2251799813685248)] * 22

MODULATIONS = [
    F(-5524291025718029, 140737488355328),
    F(-5524291025718029, 140737488355328),
    F(5524291025718029, 140737488355328),
    F(5524291025718029, 140737488355328),
    F(-5524291025718029, 140737488355328),
    F(0), F(0), F(0),
    F(-3978571430081297, 281474976710656),
    F(-5917178117733711, 281474976710656),
    F(-3519965277442521, 140737488355328),
    F(-3894251610461801, 140737488355328),
    F(-2140960324737725, 70368744177664),
    F(-4635197846686455, 140737488355328),
    F(-5289784310949011, 140737488355328),
    F(-5758797740487047, 140737488355328),
    F(-3048871735671609, 70368744177664),
    F(-6756124363134027, 140737488355328),
    F(-1751261042181613, 35184372088832),
    F(-1863727500536955, 35184372088832),
    F(-7944103127967419, 140737488355328),
    F(-8352353914239387, 140737488355328),
    F(-8561311721741165, 140737488355328),
    F(-4581887954876333, 70368744177664),
    F(-4720322026636147, 70368744177664),
    F(-152934154702833, 2199023255552),
    F(-316954711375437, 4398046511104),
    F(-665905501606627, 8796093022208),
    F(-2714292757716727, 35184372088832),
    F(-2791435723263659, 35184372088832),
]


COEFFICIENTS = [
    (F(154748600460917856), F(547294041600492928)),
    (F(-16893393365854146), F(-61022602065145272)),
    (F(-7594331149237015, 4722366482869645213696), F(-4980651426915535, 4722366482869645213696)),
    (F(1506482213850027, 1180591620717411303424), F(2105182302449157, 2361183241434822606848)),
    (F(-6001732121601251, 32), F(-6739580861423611, 128)),
    (F(-8035822621139103, 16777216), F(-3706465436495659, 33554432)),
    (F(8659345823902623, 16777216), F(5329435093097697, 33554432)),
    (F(-8799795496746605, 67108864), F(-4030981273773709, 67108864)),
    (F(8198345580650221, 1024), F(-4094629821214087, 4096)),
    (F(-2675246145081299, 8), F(-6402666417123273, 32)),
    (F(1115471846981971), F(1182623679274190)),
    (F(-8310745849367121, 4), F(-3059348960228800)),
    (F(6233840243725327, 2), F(6434209244546258)),
    (F(-7758284617457383, 2), F(-10647871733206262)),
    (F(-67333053192280792), F(-238224149232671232)),
    (F(-64872694791849192), F(-229730466687250496)),
    (F(-7275746902562599, 2), F(-11646143011542928)),
    (F(3733994751592563, 8), F(-361528924707101)),
    (F(-7051125893987565, 16), F(4739619428859271, 8)),
    (F(1778564341863133, 8), F(-8190929561456687, 32)),
    (F(-5305280227662199, 32), F(8058352028238841, 64)),
    (F(6835262236103691, 32), F(-1752540977409459, 16)),
    (F(-2541367224103801, 16), F(2057071061532791, 32)),
    (F(8577811785039967, 128), F(-8148613970017813, 1024)),
    (F(-8652625662566833, 128), F(3155152271974983, 32768)),
    (F(5193922816175405, 128), F(3020998339649463, 512)),
    (F(-670515828632851, 32), F(-6513013791318593, 1024)),
    (F(8948374634481325, 512), F(5037676427278393, 512)),
    (F(-7906455026530629, 512), F(-5382588758347499, 512)),
    (F(4503928286801209, 1024), F(4042639831469047, 1024)),
]


def phase_rect(angle: F) -> Rect:
    x = angle / 512
    real = sum(((-1) ** k * x ** (2 * k) / factorial(2 * k) for k in range(13)), F(0))
    imag = sum(((-1) ** k * x ** (2 * k + 1) / factorial(2 * k + 1) for k in range(13)), F(0))
    error = abs(x) ** 26 * F(27, factorial(26) * 26)
    return Rect(real - error, real + error, imag - error, imag + error)


def bump_interval(radius: F, position: F) -> Interval:
    if abs(position) >= radius:
        return Interval(F(0), F(0))
    t = F(30) - F(30) / (1 - (position / radius) ** 2)
    base = taylor_interval(F(-1, 2)).pow_nat(60)
    for denominator, threshold in ((8, F(-8)), (16, F(-16)), (32, F(-32)), (64, F(-64))):
        if abs(t / denominator) <= 1:
            return base.mul(taylor_interval(t / denominator).pow_nat(denominator))
    return Interval(F(0), base.pow_nat(188).hi)


def weighted_phase_rect(index: int, family: int) -> Rect:
    center = -GRID + F(2 * index + 1, 1) * GRID / CELLS
    weight = taylor_interval(-center / 120).pow_nat(60)
    phase = phase_rect(MODULATIONS[family] * center).pow_sq(9)
    weight_rect = Rect(weight.lo, weight.hi, F(0), F(0))
    return weight_rect.mul(phase)


def coefficient_rect(family: int) -> Rect:
    real, imag = COEFFICIENTS[family]
    return Rect(real, real, imag, imag)


def cell_rect(index: int, order: int = 0) -> Rect:
    center = -GRID + F(2 * index + 1, 1) * GRID / CELLS
    result = Rect(F(0), F(0), F(0), F(0))
    for family in range(30):
        radius = WIDTHS[family] ** 2
        bump = bump_interval(radius, center)
        phase = weighted_phase_rect(index, family)
        unit = phase.mul(Rect(bump.lo, bump.hi, F(0), F(0)))
        result = result.add(coefficient_rect(family).mul(unit))
    return result


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--block", type=int, default=0)
    parser.add_argument("--cells", type=int, default=1)
    parser.add_argument("--output", type=Path, default=ROOT / "results/3311_signed_jet_rect_manifest.json")
    args = parser.parse_args()
    if args.block != 0:
        raise SystemExit("3311 prototype only supports block 0")
    rows = []
    block = Rect(F(0), F(0), F(0), F(0))
    for offset in range(args.cells):
        rect = cell_rect(offset)
        block = block.add(rect)
        rows.append({"index": offset, "re_hi": str(rect.re_hi), "re_lo": str(rect.re_lo)})
    result = {
        "record": 3311,
        "status": "GENERATOR_SIDE_ORDER0_SIGNED_JET_RECTANGLE",
        "block": 0,
        "cells": args.cells,
        "formula": "3310 order-0 rational rectangle reHi",
        "block_re_lo": str(block.re_lo),
        "block_re_hi": str(block.re_hi),
        "rows": rows,
        "lean_imported": False,
        "rh_claim": False,
    }
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({k: result[k] for k in ("record", "status", "cells", "block_re_lo", "block_re_hi")}, indent=2))


if __name__ == "__main__":
    main()
