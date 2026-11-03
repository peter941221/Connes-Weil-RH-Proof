"""3307: diagnostic screen for the 3306 signed real jet rows.

The probe evaluates the exact record-2680 owner family sum at each cell center,
then uses abs(real(signed aggregate jet)) for the second and fourth rows. It
compares the resulting Taylor-6 block upper with the directed 3302 manifest.
This is external Arb evidence only; it is not imported into Lean.
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction as F
from pathlib import Path

from flint import acb, arb, ctx

import routea_concrete_owner_taylor6_3204 as owner
import routea_formal_derivative_block_no_go_3304 as formal
import routea_rational_endpoint_decimal_probe_3297 as base


ROOT = Path(__file__).resolve().parents[1]
RADIUS = F(65536001, 10000000)
CELLS = 40960
BLOCK_SIZE = 256


def signed_real_jet_upper(order: int, index: int, families: list[dict]) -> arb:
    step = 2 * RADIUS / CELLS
    midpoint = -RADIUS + F(2 * index + 1, 2) * step
    sigma = F(-1, 2)
    aggregate = acb(0)
    for family in families:
        if abs(midpoint) >= family["r"]:
            continue
        aggregate += family["center"] * owner.taylor.base.base.jets(
            family, midpoint, sigma, order
        )[order]
    return abs(aggregate.real)


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
    parser.add_argument("--precision", type=int, default=192)
    parser.add_argument(
        "--output",
        type=Path,
        default=ROOT / "results/3307_signed_real_jet_block_probe.json",
    )
    args = parser.parse_args()
    ctx.prec = args.precision

    families = owner.load_owner_families()
    widths = formal.load_widths()
    modulations = base.parse_modulations()
    coefficients = formal.load_owner_coefficients()
    endpoint_rows, manifest_blocks = load_manifest()
    sixth = formal.formal_uniform_sixth(widths, modulations, coefficients)
    sixth_upper = owner.taylor.base.base.base.exact_upper(sixth)
    step = 2 * RADIUS / CELLS
    rows: list[dict] = []
    total = F(0)

    for block in manifest_blocks:
        block_index = int(block["block"])
        block_total = arb(0)
        second_rows: list[F] = []
        fourth_rows: list[F] = []
        for index in range(block_index * BLOCK_SIZE, (block_index + 1) * BLOCK_SIZE):
            second = owner.taylor.rounded_up(
                owner.taylor.base.base.base.exact_upper(
                    signed_real_jet_upper(2, index, families)
                )
            )
            fourth = owner.taylor.rounded_up(
                owner.taylor.base.base.base.exact_upper(
                    signed_real_jet_upper(4, index, families)
                )
            )
            second_rows.append(second)
            fourth_rows.append(fourth)
            endpoint = F(endpoint_rows[index]["value_upper"])
            step_q = arb(step.numerator) / step.denominator
            block_total += (
                step_q * (arb(endpoint.numerator) / endpoint.denominator)
                + step_q**3 * (arb(second.numerator) / second.denominator) / 24
                + step_q**5 * (arb(fourth.numerator) / fourth.denominator) / 1920
                + step_q**7 * (arb(sixth_upper.numerator) / sixth_upper.denominator)
                / 322560
            )
        formal_upper = owner.taylor.base.base.base.exact_upper(block_total)
        manifest_upper = F(block["cell_upper_exact_fraction"])
        gap = formal_upper - manifest_upper
        total += formal_upper
        rows.append(
            {
                "block": block_index,
                "first_index": block["first_index"],
                "last_index": block["last_index"],
                "manifest_block_upper": str(manifest_upper),
                "signed_real_jet_block_upper": str(formal_upper),
                "signed_real_jet_minus_manifest": str(gap),
                "signed_real_jet_dominates_manifest": gap > 0,
                "signed_second_max": str(max(second_rows)),
                "signed_fourth_max": str(max(fourth_rows)),
            }
        )

    result = {
        "record": 3307,
        "status": "SIGNED_REAL_JET_BLOCK_PROBE",
        "precision_bits": args.precision,
        "cells": CELLS,
        "block_size": BLOCK_SIZE,
        "formula": "directed tight endpoint + 3306 abs(real(signed aggregate jet)) rows + 3220 uniform sixth norm row",
        "rows": rows,
        "block_upper_sum": str(total),
        "positive_gaps": sum(row["signed_real_jet_dominates_manifest"] for row in rows),
        "formal_uniform_sixth_upper": str(sixth_upper),
        "lean_certificate": False,
        "producer_go": False,
        "rh_claim": False,
        "nonclaims": [
            "Arb evaluation is diagnostic only",
            "no JSON value is imported into Lean",
            "the sixth row is still the 3220 absolute-value uniform bound",
            "a positive gap is a no-go for this 3306 row family, not an RH result",
        ],
    }
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(
        json.dumps(
            {
                "record": result["record"],
                "status": result["status"],
                "positive_gaps": result["positive_gaps"],
                "block_upper_sum": result["block_upper_sum"],
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
