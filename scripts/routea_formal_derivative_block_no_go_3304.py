"""3304: screen directed blocks against the formal 3224 derivative majorant.

This is a named no-go diagnostic, not a Lean certificate.  It evaluates the
same nonnegative family envelope used by ``record2680CellDerivativeUpper3224``
and compares the resulting Taylor-6 block upper with the directed 3302 block
constant.  A positive gap means the 3302 manifest cannot be consumed through
the current formal absolute-value derivative rows.
"""

from __future__ import annotations

import argparse
import json
import re
import struct
from fractions import Fraction as F
from math import comb
from pathlib import Path

from flint import acb, arb, ctx

import routea_concrete_owner_taylor6_3204 as owner
import routea_rational_endpoint_decimal_probe_3297 as base


ROOT = Path(__file__).resolve().parents[1]
RADIUS = F(65536001, 10000000)
CELLS = 40960
BLOCK_SIZE = 256


def load_widths() -> list[F]:
    source = (ROOT / "ConnesWeilRH/Dev/C1RouteARationalCellBump3287.lean").read_text(
        encoding="utf-8"
    )
    body = source.split("def storedWidthRat3287", 1)[1].split(
        "theorem storedWidthRat_cast3287", 1
    )[0]
    values: list[F] = []
    for token in re.findall(
        r"\(\((\d+)\s*:\s*ℚ\)\s*/\s*(\d+)\)|\((\d+)\s*:\s*ℚ\)",
        body,
    ):
        if token[0]:
            values.append(F(int(token[0]), int(token[1])))
        elif token[2]:
            values.append(F(int(token[2])))
    if len(values) != 30:
        raise ValueError(f"expected 30 stored widths, got {len(values)}")
    return values


def load_owner_coefficients() -> list[tuple[F, F]]:
    source = (ROOT / "ConnesWeilRH/Dev/C1RouteARepairedOwnerCorrectionM02680.lean").read_text(
        encoding="utf-8"
    )
    body = source.split("noncomputable def record2680CorrectionCoefficient", 1)[1].split(
        "]", 1
    )[0]

    def bits_to_fraction(bits: str) -> F:
        value = struct.unpack(">d", int(bits, 16).to_bytes(8, "big"))[0]
        return F(*value.as_integer_ratio())

    values = [
        (bits_to_fraction(real), bits_to_fraction(imag))
        for real, imag in re.findall(
            r"⟨binary64Value2674\s+0x([0-9a-f]+),\s*binary64Value2674\s+0x([0-9a-f]+)⟩",
            body,
        )
    ]
    if len(values) != 30:
        raise ValueError(f"expected 30 owner coefficients, got {len(values)}")
    return values


def bump_numerator(order: int, t: arb) -> arb:
    terms: dict[int, int]
    if order == 0:
        terms = {0: 1}
    elif order == 1:
        terms = {1: 60}
    elif order == 2:
        terms = {0: 60, 2: 3480, 4: 180}
    elif order == 3:
        terms = {1: 10080, 3: 193680, 5: 31680, 7: 720}
    elif order == 4:
        terms = {0: 10080, 2: 1085040, 4: 10189440, 6: 3575520,
                 8: 266400, 10: 3600}
    elif order == 5:
        terms = {1: 2613600, 3: 92678400, 5: 493207200,
                 7: 320371200, 9: 51703200, 11: 2361600, 13: 21600}
    elif order == 6:
        terms = {0: 2613600, 2: 387806400, 4: 6679584000,
                 6: 20842228800, 8: 24232824000, 10: 7137633600,
                 12: 714873600, 14: 22680000, 16: 151200}
    else:
        return arb(0)
    return sum((coefficient * t**power for power, coefficient in terms.items()), arb(0))


def local_bump_upper(order: int, radius: F, near: F, far: F) -> arb:
    if near >= radius:
        return arb(0)
    near_q = arb(near.numerator) / near.denominator
    far_q = arb(far.numerator) / far.denominator
    radius_q = arb(radius.numerator) / radius.denominator
    deficit_inv = 1 / (1 - near_q**2)
    return (
        bump_numerator(order, far_q)
        * deficit_inv ** (2 * order)
        * (-30 * deficit_inv).exp()
        / radius_q**order
    )


def family_cell_upper(
    order: int,
    coefficient: tuple[F, F],
    modulation: F,
    radius: F,
    near: F,
    far: F,
    left: F,
    right: F,
) -> arb:
    coefficient_q = acb(
        arb(coefficient[0].numerator) / coefficient[0].denominator,
        arb(coefficient[1].numerator) / coefficient[1].denominator,
    )
    modulation_q = arb(modulation.numerator) / modulation.denominator
    sigma = arb(-1) / 2
    radius_q = arb(radius.numerator) / radius.denominator
    near_q = arb(near.numerator) / near.denominator
    far_q = arb(far.numerator) / far.denominator
    left_q = arb(left.numerator) / left.denominator
    right_q = arb(right.numerator) / right.denominator
    lambda_norm = abs(acb(sigma, modulation_q))
    weight_exp = max(sigma * left_q, sigma * right_q).exp()
    total = arb(0)
    for index in range(order + 1):
        total += (
            comb(order, index)
            * lambda_norm**index
            * local_bump_upper(order - index, radius, near, far)
        )
    return abs(coefficient_q) * weight_exp * total


def formal_derivative_upper(
    order: int,
    index: int,
    widths: list[F],
    modulations: list[F],
    coefficients: list[tuple[F, F]],
) -> arb:
    step = 2 * RADIUS / CELLS
    left = -RADIUS + index * step
    right = left + step
    near_abs = F(0) if left <= 0 <= right else min(abs(left), abs(right))
    far_abs = max(abs(left), abs(right))
    total = arb(0)
    for family, (width, modulation, coefficient) in enumerate(
        zip(widths, modulations, coefficients)
    ):
        radius = width**2
        if near_abs >= radius:
            continue
        far = min(far_abs, radius)
        near = near_abs
        total += family_cell_upper(
            order, coefficient, modulation, radius,
            near / radius, far / radius, left, right
        )
    return total


def formal_uniform_sixth(
    widths: list[F], modulations: list[F], coefficients: list[tuple[F, F]]
) -> arb:
    total = arb(0)
    for width, modulation, coefficient in zip(widths, modulations, coefficients):
        radius = width**2
        total += family_cell_upper(
            6, coefficient, modulation, radius, F(0), F(1),
            -radius, radius
        )
    return total


def load_manifest() -> tuple[list[dict], list[dict]]:
    endpoint = json.loads(
        (ROOT / "results/3300_routea_directed_endpoint_manifest.json").read_text(
            encoding="utf-8"
        )
    )
    cells = json.loads(
        (ROOT / "results/3300_routea_directed_cell_manifest.json").read_text(
            encoding="utf-8"
        )
    )
    return endpoint["rows"], cells["blocks"]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--blocks", type=int, nargs="+", default=[0, 15, 46, 67, 105])
    parser.add_argument("--precision", type=int, default=192)
    parser.add_argument(
        "--output",
        type=Path,
        default=ROOT / "results/3304_formal_derivative_block_no_go.json",
    )
    args = parser.parse_args()
    ctx.prec = args.precision
    widths = load_widths()
    modulations = base.parse_modulations()
    coefficients = load_owner_coefficients()
    endpoint_rows, manifest_blocks = load_manifest()
    sixth = formal_uniform_sixth(widths, modulations, coefficients)
    sixth_upper = owner.taylor.base.base.base.exact_upper(sixth)
    step = 2 * RADIUS / CELLS
    rows = []
    wanted = set(args.blocks)
    for block in manifest_blocks:
        block_index = int(block["block"])
        if block_index not in wanted:
            continue
        total = arb(0)
        second_upper = []
        fourth_upper = []
        for index in range(block_index * BLOCK_SIZE, (block_index + 1) * BLOCK_SIZE):
            second = formal_derivative_upper(2, index, widths, modulations, coefficients)
            fourth = formal_derivative_upper(4, index, widths, modulations, coefficients)
            second_upper.append(owner.taylor.base.base.base.exact_upper(second))
            fourth_upper.append(owner.taylor.base.base.base.exact_upper(fourth))
            endpoint = F(endpoint_rows[index]["value_upper"])
            total += (
                arb(step.numerator) / step.denominator *
                (arb(endpoint.numerator) / endpoint.denominator)
                + (arb(step.numerator) / step.denominator) ** 3 * second / 24
                + (arb(step.numerator) / step.denominator) ** 5 * fourth / 1920
                + (arb(step.numerator) / step.denominator) ** 7 * sixth / 322560
            )
        formal_upper = owner.taylor.base.base.base.exact_upper(total)
        manifest_upper = F(block["cell_upper_exact_fraction"])
        gap = formal_upper - manifest_upper
        rows.append({
            "block": block_index,
            "first_index": block["first_index"],
            "last_index": block["last_index"],
            "manifest_block_upper": str(manifest_upper),
            "formal_3224_block_upper": str(formal_upper),
            "formal_minus_manifest": str(gap),
            "formal_dominates_manifest": gap > 0,
            "formal_second_max": str(max(second_upper)),
            "formal_fourth_max": str(max(fourth_upper)),
        })
    result = {
        "record": 3304,
        "status": "FORMAL_3224_DERIVATIVE_BLOCK_NO_GO_SCREEN",
        "precision_bits": args.precision,
        "cells": CELLS,
        "block_size": BLOCK_SIZE,
        "blocks_checked": args.blocks,
        "formula": "directed tight endpoint + formal 3224 absolute derivative rows",
        "rows": rows,
        "formal_uniform_sixth_upper": str(sixth_upper),
        "lean_certificate": False,
        "producer_go": False,
        "rh_claim": False,
        "nonclaims": [
            "Arb evaluation is diagnostic only",
            "no JSON value is imported into Lean",
            "a positive gap is a no-go for the current 3302 consumer, not an RH result",
        ],
    }
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({k: result[k] for k in ("record", "status", "rows")}, indent=2))


if __name__ == "__main__":
    main()
