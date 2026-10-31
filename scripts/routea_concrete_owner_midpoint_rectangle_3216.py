"""3216: concrete-owner midpoint rectangle at the real diagnostic coordinate."""

from __future__ import annotations

import hashlib
import json
from fractions import Fraction as F
from pathlib import Path

from flint import acb, ctx

import routea_concrete_owner_taylor6_3204 as owner

ROOT = Path(__file__).resolve().parents[1]
OWNER = ROOT / "ConnesWeilRH/Dev/C1RouteARepairedOwnerCorrectionM02680.lean"
ROW_FILE = ROOT / "results/3204_concrete_owner_taylor6_40960.jsonl"
OUTPUT = ROOT / "results/3216_routea_concrete_owner_midpoint_rectangle.json"


def exact_lower(value) -> F:
    return F(str(value.lower().fmpq()))


def exact_upper(value) -> F:
    return F(str(value.upper().fmpq()))


def floor_grid(value: F, places: int = 80) -> F:
    scale = 10**places
    numerator = value.numerator * scale
    return F(numerator // value.denominator, scale)


def ceil_grid(value: F, places: int = 80) -> F:
    scale = 10**places
    numerator = value.numerator * scale
    return F(-((-numerator) // value.denominator), scale)


def run(precision: int = 192, index: int = 0) -> dict:
    ctx.prec = precision
    rows = ROW_FILE.read_text(encoding="utf-8").splitlines()
    row = json.loads(rows[index + 1])
    midpoint = F(row["midpoint"])
    sigma = F(-1, 2)
    families = owner.load_owner_families()
    family_rectangles = []
    aggregate = acb(0)
    for family_index, family in enumerate(families):
        contribution = family["center"] * owner.taylor.base.base.jets(family, midpoint, sigma, 0)[0]
        aggregate += contribution
        family_rectangles.append(
            {
                "index": family_index,
                "reLo": str(floor_grid(exact_lower(contribution.real))),
                "reHi": str(ceil_grid(exact_upper(contribution.real))),
                "imLo": str(floor_grid(exact_lower(contribution.imag))),
                "imHi": str(ceil_grid(exact_upper(contribution.imag))),
            }
        )
    aggregate_re_lo = floor_grid(exact_lower(aggregate.real))
    aggregate_re_hi = ceil_grid(exact_upper(aggregate.real))
    result = {
        "record": 3216,
        "status": "PASS_EXTERNAL_MIDPOINT_RECTANGLE",
        "source_record": 3204,
        "cell_index": index,
        "midpoint": str(midpoint),
        "sigma": str(sigma),
        "precision_bits": precision,
        "owner_source": str(OWNER.relative_to(ROOT)),
        "owner_sha256": hashlib.sha256(OWNER.read_bytes()).hexdigest(),
        "rounding_grid": "10^-80; lower floors and upper ceilings",
        "family_rectangles": family_rectangles,
        "aggregate": {
            "reLo": str(aggregate_re_lo),
            "reHi": str(aggregate_re_hi),
            "imLo": str(floor_grid(exact_lower(aggregate.imag))),
            "imHi": str(ceil_grid(exact_upper(aggregate.imag))),
            "reHi_decimal": float(aggregate.real.upper()),
        },
        "nonzero_family_count": sum(
            any(rect[field] != "0" for field in ("reLo", "reHi", "imLo", "imHi"))
            for rect in family_rectangles
        ),
        "matches_3204_value_upper": aggregate_re_hi <= F(row["value_upper"]),
        "lean_certificate": False,
        "coordinate_transfer_closed": False,
        "producer_go": False,
        "rh_claim": False,
    }
    OUTPUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    return result


if __name__ == "__main__":
    print(json.dumps(run(), indent=2))
