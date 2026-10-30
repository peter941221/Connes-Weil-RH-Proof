"""3204: Taylor-6 diagnostic repriced on the concrete Lean owner."""

from __future__ import annotations

import argparse
import json
import re
import struct
from fractions import Fraction as F
from pathlib import Path

from flint import acb, arb, ctx

import routea_signed_taylor6_interval_3187 as taylor

ROOT = Path(__file__).resolve().parents[1]
OWNER = ROOT / "ConnesWeilRH/Dev/C1RouteARepairedOwnerCorrectionM02680.lean"


def binary64_fraction(bits: str) -> F:
    value = struct.unpack(">d", int(bits, 16).to_bytes(8, "big"))[0]
    return F.from_float(value)


def owner_coefficients() -> list[tuple[F, F]]:
    text = OWNER.read_text(encoding="utf-8")
    body = re.search(
        r"noncomputable def record2680CorrectionCoefficient.*?\n\nset_option maxRecDepth",
        text,
        re.DOTALL,
    )
    if body is None:
        raise ValueError("owner coefficient definition not found")
    values = [
        (binary64_fraction(real_bits), binary64_fraction(imag_bits))
        for real_bits, imag_bits in re.findall(
            r"binary64Value2674 0x([0-9a-f]+), binary64Value2674 0x([0-9a-f]+)",
            body.group(0),
        )
    ]
    if len(values) != 30:
        raise ValueError(f"expected 30 coefficients, found {len(values)}")
    return values


def load_owner_families():
    families = taylor.base.base.load_families()
    lift = taylor.base.base.base.lift
    for family, (real_value, imag_value) in zip(families, owner_coefficients()):
        family["center"] = acb(lift(real_value), lift(imag_value))
        family["error"] = arb(0)
        family["scale"] = taylor.base.base.base.upper(abs(family["center"]))
    return families


def run(cells: int, precision: int, cell_output: Path | None = None) -> dict:
    ctx.prec = precision
    families = load_owner_families()
    sigma = F(-1, 2)
    radius = taylor.base.base.base.RADIUS
    step = 2 * radius / cells
    total = F(0)
    remainder = F(0)
    cell_file = cell_output.open("w", encoding="utf-8") if cell_output is not None else None
    if cell_file is not None:
        cell_file.write(json.dumps({"format": "3204-concrete-owner-taylor6-jsonl-v1", "record": 3204, "cells": cells, "precision_bits": precision, "sigma": str(sigma), "step": str(step), "coefficient_source": str(OWNER.relative_to(ROOT))}, sort_keys=True) + "\n")
    for index in range(cells):
        left = -radius + index * step
        right = left + step
        midpoint = (left + right) / 2
        value = acb(0)
        second = acb(0)
        fourth = acb(0)
        for family in families:
            jets = taylor.base.base.jets(family, midpoint, sigma, 4)
            value += family["center"] * jets[0]
            second += family["center"] * jets[2]
            fourth += family["center"] * jets[4]
        value_upper = taylor.rounded_up(taylor.base.base.base.exact_upper(value.real))
        second_upper = taylor.rounded_up(taylor.base.base.base.exact_upper(second.real))
        fourth_upper = taylor.rounded_up(taylor.base.base.base.exact_upper(fourth.real))
        sixth = taylor.rounded_up(taylor.sixth_upper(families, left, right, sigma))
        cell_upper = (step * value_upper + step**3 / 24 * second_upper +
                      step**5 / 1920 * fourth_upper + step**7 / 322560 * sixth)
        total += cell_upper
        cell_remainder = step**7 / 322560 * sixth
        remainder += cell_remainder
        if cell_file is not None:
            cell_file.write(json.dumps({"index": index, "left": str(left), "right": str(right), "midpoint": str(midpoint), "step": str(step), "value_upper": str(value_upper), "second_upper": str(second_upper), "fourth_upper": str(fourth_upper), "sixth_upper": str(sixth), "cell_upper": str(cell_upper), "sixth_order_remainder_upper": str(cell_remainder), "upper_semantics": "exact owner binary64 coefficients; Arb upper rounded upward to 10^-80 grid"}, sort_keys=True) + "\n")
    if cell_file is not None:
        cell_file.close()
    return {
        "record": 3204,
        "status": "CONCRETE_OWNER_TAYLOR6_DIAGNOSTIC",
        "cells": cells,
        "precision_bits": precision,
        "sigma": "-1/2",
        "total_upper": str(total),
        "sixth_order_remainder_upper": str(remainder),
        "total_upper_negative": total < 0,
        "coefficient_source": str(OWNER.relative_to(ROOT)),
        "coefficient_error": "0; exact binary64 owner values",
        "lean_certificate": False,
        "full_line_tail_included": False,
        "producer_go": False,
        "rh_claim": False,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--cells", type=int, default=40960)
    parser.add_argument("--precision", type=int, default=192)
    parser.add_argument("--cell-output", type=Path, default=None)
    parser.add_argument("--output", type=Path,
                        default=ROOT / "results/3204_concrete_owner_taylor6.json")
    args = parser.parse_args()
    result = run(args.cells, args.precision, args.cell_output)
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()