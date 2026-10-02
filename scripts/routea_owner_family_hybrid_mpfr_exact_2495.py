"""2495: corrected directed-MPFR replay with exact owner inputs.

2491 converted the exact owner radii/modulations to binary64 before forming
the evaluator constants and used a nextafter enclosure of ``math.exp(-30)``.
This replay keeps exact rationals as directed binary64 intervals and obtains
exp(-30) from MPFR itself.  It is still an external pricing control, not a
Lean certificate.
"""
import hashlib
import importlib.util
import json
import math
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
REPAIR = ROOT / "results/2338_exact_interpolation_repair.json"
CAPTURE = ROOT / "results/2275_gap_owner_audit.json"
OLD = ROOT / "results/2491_owner_family_hybrid_mpfr.json"
OUT = ROOT / "results/2495_owner_family_hybrid_mpfr_exact.json"

spec = importlib.util.spec_from_file_location(
    "routea_mpfr_2478_exact", ROOT / "scripts/routea_owner_local_curvature_mpfr_2478.py")
base = importlib.util.module_from_spec(spec)
spec.loader.exec_module(base)
mpfr = base.mpfr

EXP_NEG30 = mpfr.unary("mpfr_exp", base.outward(-30.0))


def rat(text):
    p = text.split("/")
    return Fraction(int(p[0]), int(p[1])) if len(p) == 2 else Fraction(int(p[0]))


def iv(value):
    return base.exact_rational_interval(value)


def iv_pow(value, exponent):
    result = (1.0, 1.0)
    for _ in range(exponent):
        result = mpfr.mul(result, value)
    return result


def abs_iv(value):
    return (0.0, max(abs(value[0]), abs(value[1])))


def float_payload(value):
    value = float(value)
    numerator, denominator = value.as_integer_ratio()
    return {"hex": value.hex(), "numerator": str(numerator),
            "denominator": str(denominator)}


def bump_bound(order, radius, left, right, step):
    constants = (1, 60, 3720)
    global_bound = mpfr.mul(iv(Fraction(constants[order])),
                            mpfr.div(EXP_NEG30, iv_pow(radius, order)))
    lo = max(left[0], -radius[1] + step[1] / 1000)
    hi = min(right[1], radius[1] - step[1] / 1000)
    if lo >= hi:
        return global_bound
    x = (base.outward(lo)[0], base.outward(hi)[1])
    t = mpfr.div(x, radius)
    d = mpfr.sub(iv(Fraction(1)), mpfr.mul(t, t))
    if d[0] <= 0:
        return global_bound
    if order == 0:
        p = iv(Fraction(1))
    elif order == 1:
        p = mpfr.mul(iv(Fraction(-60)), t)
    else:
        t2 = mpfr.mul(t, t)
        t4 = mpfr.mul(t2, t2)
        p = mpfr.add(mpfr.add(iv(Fraction(-60)), mpfr.mul(iv(Fraction(3480)), t2)),
                     mpfr.mul(iv(Fraction(180)), t4))
    d2 = mpfr.mul(d, d)
    d2q = (1.0, 1.0) if order == 0 else d2
    if order == 2:
        d2q = mpfr.mul(d2, d2)
    value = mpfr.div(mpfr.mul(mpfr.unary("mpfr_exp", mpfr.div(iv(Fraction(-30)), d)),
                               abs_iv(p)),
                     mpfr.mul(d2q, iv_pow(radius, order)))
    return (min(value[0], global_bound[0]), max(value[1], global_bound[1]))


def family_l1(sigma, radius, coefficient, modulation):
    constants = (1, 60, 3720)
    mod_abs = abs_iv(modulation)
    bounds = []
    for order in range(3):
        total = (0.0, 0.0)
        for j in range(order + 1):
            factor = mpfr.mul(iv(Fraction(math.comb(order, j))),
                              iv_pow(mod_abs, j))
            bump = mpfr.mul(iv(Fraction(constants[order - j])),
                            mpfr.div(EXP_NEG30, iv_pow(radius, order - j)))
            total = mpfr.add(total, mpfr.mul(factor, bump))
        bounds.append(mpfr.mul(coefficient, total))
    weight = mpfr.unary("mpfr_exp", mpfr.mul(iv(abs(sigma)), radius))
    weighted = mpfr.add(bounds[2], mpfr.add(
        mpfr.mul(iv(Fraction(2 * abs(sigma))), bounds[1]),
        mpfr.mul(iv(Fraction(sigma * sigma)), bounds[0])))
    return mpfr.mul(weight, weighted)[1]


def directed_family(sigma, radius, modulation, coefficient, left, right, step):
    bumps = [bump_bound(order, radius, left, right, step) for order in range(3)]
    mod_abs = abs_iv(modulation)
    ext = []
    for order in range(3):
        value = (0.0, 0.0)
        for j in range(order + 1):
            term = mpfr.mul(iv(Fraction(math.comb(order, j))),
                            mpfr.mul(iv_pow(mod_abs, j), bumps[order - j]))
            value = mpfr.add(value, term)
        ext.append(value)
    weighted = mpfr.add(ext[2], mpfr.add(
        mpfr.mul(iv(Fraction(2 * abs(sigma))), ext[1]),
        mpfr.mul(iv(Fraction(sigma * sigma)), ext[0])))
    weight = mpfr.unary("mpfr_exp", mpfr.mul(iv(sigma),
                                               (left[0], right[1])))
    return mpfr.mul(coefficient, mpfr.mul(weight, weighted))[1]


def main():
    cells, subdiv = 40, 16
    repair = json.loads(REPAIR.read_text(encoding="utf-8"))
    capture = json.loads(CAPTURE.read_text(encoding="utf-8"))["owner_capture"]
    families = []
    for row, pair in zip(repair["coefficient_rows"], capture["families_hex"]):
        re = (rat(row["ideal_base_coefficient"]["real"]["lower_exact"]) +
              rat(row["ideal_base_coefficient"]["real"]["upper_exact"])) / 2
        im = (rat(row["ideal_base_coefficient"]["imag"]["lower_exact"]) +
              rat(row["ideal_base_coefficient"]["imag"]["upper_exact"])) / 2
        coefficient = iv(abs(re) + abs(im))
        width = Fraction.from_float(float.fromhex(pair[0]))
        families.append((iv(width * width), iv(Fraction.from_float(float.fromhex(pair[1]))), coefficient))
    radius = Fraction(2076918743413931858457251756481,
                      316912650057057350374175801344)
    step = 2 * radius / cells
    substep = step / subdiv
    rows = []
    for sigma in (-Fraction(1, 2), Fraction(1, 2)):
        baseline_cells, hybrid_cells = [], []
        for index in range(cells * subdiv):
            left = -radius + index * substep
            right = -radius + (index + 1) * substep
            left_iv, right_iv, step_iv = iv(left), iv(right), iv(substep)
            baseline_total = (0.0, 0.0)
            hybrid_total = (0.0, 0.0)
            for fam_radius, modulation, coefficient in families:
                baseline = family_l1(sigma, fam_radius, coefficient, modulation)
                baseline_total = mpfr.add(baseline_total, (0.0, baseline))
                if max(abs(left), abs(right)) < max(abs(fam_radius[0]), abs(fam_radius[1])):
                    interval = directed_family(sigma, fam_radius, modulation, coefficient,
                                               left_iv, right_iv, step_iv)
                    chosen = min(interval, baseline)
                else:
                    chosen = baseline
                hybrid_total = mpfr.add(hybrid_total, (0.0, chosen))
            baseline_cells.append(baseline_total[1])
            hybrid_cells.append(hybrid_total[1])
        factor = substep ** 3 / 12
        baseline = float(factor * sum((Fraction.from_float(x) for x in baseline_cells), Fraction(0)))
        hybrid = float(factor * sum((Fraction.from_float(x) for x in hybrid_cells), Fraction(0)))
        rows.append({"sigma": float(sigma), "baseline_remainder": baseline,
                     "hybrid_remainder": hybrid, "hybrid_to_baseline": hybrid / baseline,
                     "baseline_cell_upper_bounds": [float_payload(x) for x in baseline_cells],
                     "hybrid_cell_upper_bounds": [float_payload(x) for x in hybrid_cells]})
    old = json.loads(OLD.read_text(encoding="utf-8"))
    old_summary = [{"sigma": row["sigma"],
                    "baseline_remainder": row["baseline_remainder"],
                    "hybrid_remainder": row["hybrid_remainder"],
                    "hybrid_to_baseline": row["hybrid_to_baseline"]}
                   for row in old["rows"]]
    result = {"record": 2495, "status": "EXACT_INPUT_DIRECTED_MPFR_PRICE_NOT_A_LEAN_CERTIFICATE",
              "backend": {"precision_bits": mpfr.PREC, "exp_neg30": "directed MPFR"},
              "grid": {"cells": cells, "subdiv": subdiv, "effective_cells": cells * subdiv},
              "rows": rows, "old_2491_rows": old_summary,
              "repair_sha256": hashlib.sha256(REPAIR.read_bytes()).hexdigest(),
              "capture_sha256": hashlib.sha256(CAPTURE.read_bytes()).hexdigest(),
              "decision": "remove_float_owner_constants_and_math_exp_from_price",
              "nonclaims": ["no Lean literal import", "no producer GO", "no RH"]}
    OUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
