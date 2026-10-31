"""3214: replay representative concrete-owner Taylor-6 cells."""

from __future__ import annotations

import hashlib
import json
from decimal import Decimal, getcontext
from fractions import Fraction as F
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MAIN = ROOT / "results/3204_concrete_owner_taylor6.json"
CELLS = ROOT / "results/3204_concrete_owner_taylor6_40960.jsonl"
OUTPUT = ROOT / "results/3214_routea_concrete_owner_representative_cells.json"


def ceil_grid(value: F, places: int = 80) -> F:
    scale = 10**places
    numerator = value.numerator * scale
    return F(-((-numerator) // value.denominator), scale)


def decimal(value: F) -> str:
    getcontext().prec = 24
    return format(Decimal(value.numerator) / Decimal(value.denominator), ".18E")


def validate(row: dict, index: int, step: F) -> None:
    if row["index"] != index:
        raise ValueError(f"index mismatch at {index}")
    left, right, midpoint, actual_step = map(
        F, (row["left"], row["right"], row["midpoint"], row["step"])
    )
    if actual_step != step or right - left != step or midpoint != (left + right) / 2:
        raise ValueError(f"geometry mismatch at {index}")
    value, second, fourth, sixth = map(
        F, (row["value_upper"], row["second_upper"], row["fourth_upper"], row["sixth_upper"])
    )
    expected = (
        step * value
        + step**3 * second / 24
        + step**5 * fourth / 1920
        + step**7 * sixth / 322560
    )
    if F(row["cell_upper"]) != expected:
        raise ValueError(f"Taylor formula mismatch at {index}")
    if F(row["sixth_order_remainder_upper"]) != step**7 * sixth / 322560:
        raise ValueError(f"remainder formula mismatch at {index}")
    if any(bound != ceil_grid(bound) for bound in (value, second, fourth, sixth)):
        raise ValueError(f"upward rounding mismatch at {index}")


def run() -> dict:
    main = json.loads(MAIN.read_text(encoding="utf-8"))
    cells = int(main["cells"])
    lines = CELLS.read_text(encoding="utf-8").splitlines()
    if len(lines) != cells + 1:
        raise ValueError("JSONL line count mismatch")
    header = json.loads(lines[0])
    if header.get("format") != "3204-concrete-owner-taylor6-jsonl-v1":
        raise ValueError("unexpected JSONL format")
    rows = [json.loads(line) for line in lines[1:]]
    step = F(header["step"])
    for index, row in enumerate(rows):
        validate(row, index, step)
    if F(rows[0]["left"]) + cells * step != F(rows[-1]["right"]):
        raise ValueError("grid endpoint mismatch")
    minimum_index = min(range(cells), key=lambda index: F(rows[index]["cell_upper"]))
    indices = (0, minimum_index, cells - 1)
    selected = []
    for index in indices:
        row = rows[index]
        selected.append(
            {
                "index": index,
                "left": row["left"],
                "right": row["right"],
                "midpoint": row["midpoint"],
                "value_upper": row["value_upper"],
                "second_upper": row["second_upper"],
                "fourth_upper": row["fourth_upper"],
                "sixth_upper": row["sixth_upper"],
                "cell_upper": row["cell_upper"],
                "cell_upper_decimal": decimal(F(row["cell_upper"])),
                "sixth_order_remainder_upper_decimal": decimal(
                    F(row["sixth_order_remainder_upper"])
                ),
            }
        )
    owner = ROOT / main["coefficient_source"].replace("\\", "/")
    result = {
        "record": 3214,
        "status": "PASS",
        "source_record": 3204,
        "cells": cells,
        "validated_rows": len(rows),
        "negative_cells": sum(F(row["cell_upper"]) < 0 for row in rows),
        "zero_cells": sum(F(row["cell_upper"]) == 0 for row in rows),
        "positive_cells": sum(F(row["cell_upper"]) > 0 for row in rows),
        "aggregate_upper": str(sum(F(row["cell_upper"]) for row in rows)),
        "representative_indices": list(indices),
        "representative_rows": selected,
        "owner_source": main["coefficient_source"],
        "owner_sha256": hashlib.sha256(owner.read_bytes()).hexdigest(),
        "formula_replay_exact": True,
        "upward_rounding_replay_exact": True,
        "lean_certificate": False,
        "full_line_tail_included": False,
        "producer_go": False,
        "rh_claim": False,
    }
    OUTPUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    return result


if __name__ == "__main__":
    print(json.dumps(run(), indent=2))
# End of record 3214.
