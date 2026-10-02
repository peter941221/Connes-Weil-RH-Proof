"""Price the formal 2498 negative-exp split before cell propagation."""
import importlib.util
import json
import math
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
INPUTS = ROOT / "results/2499_owner_exp_split_inputs.json"

spec = importlib.util.spec_from_file_location(
    "routea_mpfr_2500", ROOT / "scripts/routea_owner_local_curvature_mpfr_2478.py")
base = importlib.util.module_from_spec(spec)
spec.loader.exec_module(base)
mpfr = base.mpfr

E = Fraction(3678794411714424, 10**16)
ERR = Fraction(21, math.factorial(20) * 20)


def taylor20(r):
    return sum(((-r) ** k) / math.factorial(k) for k in range(20))


def main():
    artifact = json.loads(INPUTS.read_text(encoding="utf-8"))
    ratios = []
    underflow = 0
    worst = None
    for row in artifact["rows"]:
        index = row["index"]
        for item in row["families"]:
            if item["branch"] != "local":
                continue
            n = item["n"]
            r = Fraction(int(item["remainder_numerator"]),
                         int(item["remainder_denominator"]))
            split = E ** n * (taylor20(r) + ERR)
            z = Fraction(n) + r
            actual = mpfr.unary("mpfr_exp", base.exact_rational_interval(-z))[1]
            ratio = float(split) / actual
            if ratio == 0.0:
                underflow += 1
            else:
                ratios.append(ratio)
            if worst is None or ratio > worst["ratio"]:
                worst = {"ratio": ratio, "cell": index, "family": item["family"],
                         "n": n, "remainder": float(r)}
    ratios.sort()
    result = {
        "record": 2500,
        "status": "FORMAL_EXP_SPLIT_EXTERNAL_PRICE_NOT_A_CERTIFICATE",
        "samples": len(ratios),
        "binary64_underflowed_samples": underflow,
        "ratio_min": ratios[0],
        "ratio_median": ratios[len(ratios) // 2],
        "ratio_max": ratios[-1],
        "worst": worst,
        "decision": "price_split_before_weighted_curvature_propagation",
        "nonclaims": ["no hcell proof", "no producer GO", "no RH"],
    }
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
