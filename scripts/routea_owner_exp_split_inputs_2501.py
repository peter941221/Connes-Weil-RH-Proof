"""Correct record-2501 owner/cell exponent inputs.

For an upper bound on exp(-30/(1-a^2)) over a cell, ``a`` must be the
minimum of |x/r| on that cell: zero for a cell crossing zero, otherwise the
absolute value of the nearer endpoint.  Record 2499 used the maximum endpoint
and is retained as historical input only.
"""
import json
import re
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / "ConnesWeilRH/Dev/C1RouteAOwnerPanelSample2460.lean"
OUT = ROOT / "results/2501_owner_exp_split_inputs.json"


def parse_radii():
    text = LEAN.read_text(encoding="utf-8")
    values = {}
    pattern = re.compile(r"def rad(\d+)_2460 : ℝ := \(\(([^:]+?) : ℚ\) : ℝ\)")
    for match in pattern.finditer(text):
        raw = match.group(2).strip()
        parts = raw.split("/")
        values[int(match.group(1))] = (
            Fraction(int(parts[0]), int(parts[1])) if len(parts) == 2
            else Fraction(int(parts[0])))
    if len(values) != 30:
        raise ValueError(f"expected 30 radii, found {len(values)}")
    return [values[i] for i in range(30)]


def main():
    radii = parse_radii()
    radius = Fraction(2076918743413931858457251756481,
                      316912650057057350374175801344)
    step = 2 * radius / 640
    rows = []
    local = baseline = 0
    n_max = 0
    for index in range(640):
        left = -radius + index * step
        right = left + step
        cells = []
        for family, family_radius in enumerate(radii):
            endpoint_upper = max(abs(left), abs(right))
            if endpoint_upper >= family_radius:
                cells.append({"family": family, "branch": "baseline"})
                baseline += 1
                continue
            endpoint_lower = Fraction(0) if left <= 0 <= right else min(abs(left), abs(right))
            a = endpoint_lower / family_radius
            z = Fraction(30) / (1 - a * a)
            n = z.numerator // z.denominator
            remainder = z - n
            cells.append({"family": family, "branch": "local", "n": n,
                          "remainder_numerator": str(remainder.numerator),
                          "remainder_denominator": str(remainder.denominator),
                          "a_source": "cell_min_abs_endpoint"})
            local += 1
            n_max = max(n_max, n)
        rows.append({"index": index, "families": cells})
    result = {
        "record": 2501,
        "status": "CORRECTED_EXACT_RATIONAL_OWNER_EXPONENT_SPLIT_INPUTS",
        "correction": "upper_bound_uses_minimum_cell_abs_ratio",
        "grid": {"cells": 640, "radius_numerator": str(radius.numerator),
                 "radius_denominator": str(radius.denominator)},
        "families": 30, "safe_family_cells": local,
        "baseline_family_cells": baseline, "max_local_integer_part": n_max,
        "rows": rows,
        "nonclaims": ["no Lean hcell proof", "no producer GO", "no RH"],
    }
    OUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({k: result[k] for k in (
        "record", "safe_family_cells", "baseline_family_cells",
        "max_local_integer_part")}, indent=2))


if __name__ == "__main__":
    main()
