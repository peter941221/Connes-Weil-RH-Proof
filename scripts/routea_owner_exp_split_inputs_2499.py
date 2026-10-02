"""Generate exact owner/cell exponent decompositions for record 2499.

For every safe owner family/cell, compute
    z = 30 / (1 - a^2) = n + r,  n = floor(z), 0 <= r < 1,
where ``a`` is the exact endpoint ratio used by the Lean consumer.  Unsafe
family/cell pairs are marked ``baseline`` because the hybrid definition uses
the L1 branch there.  This is input generation only; the Lean inequalities
still have to consume and verify the rational data.
"""
import json
import re
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / "ConnesWeilRH/Dev/C1RouteAOwnerPanelSample2460.lean"
OUT = ROOT / "results/2499_owner_exp_split_inputs.json"


def parse_radii():
    text = LEAN.read_text(encoding="utf-8")
    values = {}
    pattern = re.compile(
        r"def rad(\d+)_2460 : ℝ := \(\(([^:]+?) : ℚ\) : ℝ\)")
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
    safe = 0
    n_max = 0
    for index in range(640):
        left = -radius + index * step
        right = left + step
        cells = []
        for family, family_radius in enumerate(radii):
            endpoint = max(abs(left), abs(right))
            if endpoint < family_radius:
                a = endpoint / family_radius
                z = Fraction(30) / (1 - a * a)
                n = z.numerator // z.denominator
                remainder = z - n
                cells.append({"family": family, "branch": "local",
                              "n": n,
                              "remainder_numerator": str(remainder.numerator),
                              "remainder_denominator": str(remainder.denominator)})
                safe += 1
                n_max = max(n_max, n)
            else:
                cells.append({"family": family, "branch": "baseline"})
        rows.append({"index": index, "families": cells})
    result = {
        "record": 2499,
        "status": "EXACT_RATIONAL_OWNER_EXPONENT_SPLIT_INPUTS",
        "grid": {"cells": 640, "radius_numerator": str(radius.numerator),
                 "radius_denominator": str(radius.denominator)},
        "families": 30,
        "safe_family_cells": safe,
        "baseline_family_cells": 640 * 30 - safe,
        "max_local_integer_part": n_max,
        "rows": rows,
        "nonclaims": ["no Lean hcell proof", "no producer GO", "no RH"],
    }
    OUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({k: result[k] for k in (
        "record", "safe_family_cells", "baseline_family_cells",
        "max_local_integer_part")}, indent=2))


if __name__ == "__main__":
    main()
