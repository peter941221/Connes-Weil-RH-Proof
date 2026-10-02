"""Self-tests for the exact-rational coefficient binding in 2478."""
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
    print({"record": 2478, "checked": checked,
           "verdict": "EXACT_RATIONAL_BINDINGS_CONTAINED"})


if __name__ == "__main__":
    main()
