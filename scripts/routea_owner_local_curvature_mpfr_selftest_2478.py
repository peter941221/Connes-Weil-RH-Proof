"""Self-tests for the exact-rational and per-cell bindings in 2478."""
import importlib.util
import json
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location(
    "price2478", ROOT / "scripts/routea_owner_local_curvature_mpfr_2478.py")
price = importlib.util.module_from_spec(spec)
spec.loader.exec_module(price)


def q(s):
    p = s.split("/")
    return Fraction(int(p[0]), int(p[1])) if len(p) == 2 else Fraction(int(p[0]))


def main():
    repair = json.loads(price.REPAIR.read_text())
    checked = 0
    for row in repair["coefficient_rows"]:
        re = (q(row["ideal_base_coefficient"]["real"]["lower_exact"]) +
              q(row["ideal_base_coefficient"]["real"]["upper_exact"])) / 2
        im = (q(row["ideal_base_coefficient"]["imag"]["lower_exact"]) +
              q(row["ideal_base_coefficient"]["imag"]["upper_exact"])) / 2
        target = abs(re) + abs(im)
        lo, hi = price.exact_rational_interval(target)
        assert Fraction.from_float(lo) <= target <= Fraction.from_float(hi)
        assert price.decimal_bound(target, 220, False) != price.decimal_bound(target, 220, True)
        checked += 1
    artifact = json.loads(price.OUT.read_text())
    cells_checked = 0
    for row in artifact["rows"]:
        payloads = row["cell_upper_bounds"]
        values = []
        for payload in payloads:
            value = float.fromhex(payload["hex"])
            numerator, denominator = value.as_integer_ratio()
            assert payload["numerator"] == str(numerator)
            assert payload["denominator"] == str(denominator)
            assert value >= 0.0
            values.append(Fraction(numerator, denominator))
            cells_checked += 1
        exact_remainder = Fraction.from_float(float(artifact["step"])) ** 3
        exact_remainder *= sum(values, Fraction(0))
        exact_remainder /= 12
        stored = Fraction(int(row["remainder_binary64_exact"]["numerator"]),
                          int(row["remainder_binary64_exact"]["denominator"]))
        assert stored == exact_remainder
        assert row["binding_index"] == max(range(len(values)), key=values.__getitem__)
    print({"record": 2478, "checked": checked,
           "cells_checked": cells_checked,
           "verdict": "EXACT_RATIONAL_AND_CELL_BINDINGS_REPLAYED"})


if __name__ == "__main__":
    main()
