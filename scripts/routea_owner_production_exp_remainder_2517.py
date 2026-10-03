"""2517: directed-MPFR price for the 2516 production exponential remainder.

This is an external routing price only.  It reuses the exact-owner inputs and
the 640-cell production grid, evaluates the 2508 floor/Taylor upper on cells
196..443, and keeps the 2488 L1 curvature outside that range.  It is not a
Lean certificate and imports no numeric conclusion into Lean.
"""

import importlib.util
import json
import math
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
REPAIR = ROOT / "results/2338_exact_interpolation_repair.json"
CAPTURE = ROOT / "results/2275_gap_owner_audit.json"
OUT = ROOT / "results/2517_owner_production_exp_remainder.json"

spec = importlib.util.spec_from_file_location(
    "routea_mpfr_2478_exact", ROOT / "scripts/routea_owner_local_curvature_mpfr_2478.py")
base = importlib.util.module_from_spec(spec)
spec.loader.exec_module(base)
mpfr = base.mpfr


def rat(text):
    parts = text.split("/")
    return Fraction(int(parts[0]), int(parts[1])) if len(parts) == 2 else Fraction(int(parts[0]))


def iv(value):
    return base.exact_rational_interval(value)


def iv_pow(value, exponent):
    result = (1.0, 1.0)
    for _ in range(exponent):
        result = mpfr.mul(result, value)
    return result


def abs_iv(value):
    return (0.0, max(abs(value[0]), abs(value[1])))


EXP_NEG_ONE_UPPER = iv(Fraction(3678794411714424, 10_000_000_000_000_000))
TAYLOR_ERROR = iv(Fraction(21, math.factorial(20) * 20))
EXP_NEG30 = mpfr.unary("mpfr_exp", base.outward(-30.0))


def taylor20(z):
    total = (0.0, 0.0)
    for k in range(20):
        signed = iv(Fraction(-1 if k % 2 else 1))
        term = mpfr.div(mpfr.mul(signed, iv_pow(z, k)), iv(Fraction(math.factorial(k))))
        total = mpfr.add(total, term)
    return total


def production_exp_upper(a):
    z_fraction = Fraction(30, 1) / (1 - a * a)
    n = z_fraction.numerator // z_fraction.denominator
    z = iv(z_fraction)
    remainder = mpfr.sub(z, iv(Fraction(n)))
    return mpfr.mul(iv_pow(EXP_NEG_ONE_UPPER, n),
                    mpfr.add(taylor20(remainder), TAYLOR_ERROR))


def production_family(sigma, radius, modulation, coefficient, left, right):
    endpoint = max(abs(left), abs(right))
    minimum = 0 if left <= 0 <= right else min(abs(left), abs(right))
    t = mpfr.div(iv(endpoint), iv(radius))
    a = mpfr.div(iv(minimum), iv(radius))
    one = iv(Fraction(1))
    t2 = mpfr.mul(t, t)
    d = mpfr.sub(one, t2)
    d2 = mpfr.mul(d, d)
    d3 = mpfr.mul(d2, d)
    radius_iv = iv(radius)
    mod_abs = abs_iv(iv(modulation))
    slope = mpfr.add(
        mpfr.div(mpfr.mul(iv(Fraction(60)), t),
                 mpfr.mul(d2, radius_iv)), mod_abs)
    slope_core = mpfr.div(mpfr.mul(iv(Fraction(60)), t),
                          mpfr.mul(d2, radius_iv))
    second = mpfr.add(
        mpfr.div(mpfr.mul(iv(Fraction(60)),
                          mpfr.add(mpfr.div(one, d2),
                                   mpfr.div(mpfr.mul(iv(Fraction(4)), t2), d3))),
                 mpfr.mul(radius_iv, radius_iv)),
        mpfr.add(mpfr.mul(slope_core, slope_core),
                 mpfr.add(mpfr.mul(mod_abs, mod_abs),
                          mpfr.mul(iv(Fraction(2)),
                                   mpfr.mul(mod_abs, slope_core)))))
    upper = production_exp_upper(Fraction(minimum, 1) / radius)
    zero = mpfr.mul(coefficient, upper)
    first = mpfr.mul(zero, slope)
    second_bound = mpfr.mul(zero, second)
    weighted = mpfr.add(second_bound,
                        mpfr.add(mpfr.mul(iv(Fraction(2 * abs(sigma))), first),
                                 mpfr.mul(iv(sigma * sigma), zero)))
    weight = mpfr.unary("mpfr_exp", mpfr.mul(iv(abs(sigma)), iv(radius)))
    return mpfr.mul(weight, weighted)[1]


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


def main():
    capture = json.loads(CAPTURE.read_text(encoding="utf-8"))["owner_capture"]
    repair = json.loads(REPAIR.read_text(encoding="utf-8"))
    families = []
    for row, pair in zip(repair["coefficient_rows"], capture["families_hex"]):
        re = (rat(row["ideal_base_coefficient"]["real"]["lower_exact"]) +
              rat(row["ideal_base_coefficient"]["real"]["upper_exact"])) / 2
        im = (rat(row["ideal_base_coefficient"]["imag"]["lower_exact"]) +
              rat(row["ideal_base_coefficient"]["imag"]["upper_exact"])) / 2
        coefficient = iv(abs(re) + abs(im))
        width = Fraction.from_float(float.fromhex(pair[0]))
        families.append((width * width,
                         Fraction.from_float(float.fromhex(pair[1])), coefficient))
    radius = Fraction(2076918743413931858457251756481,
                      316912650057057350374175801344)
    cells = 640
    step = 2 * radius / cells
    rows = []
    for sigma in (-Fraction(1, 2), Fraction(1, 2)):
        baseline_cells, production_cells = [], []
        for index in range(cells):
            left = -radius + index * step
            right = -radius + (index + 1) * step
            baseline_total = (0.0, 0.0)
            production_total = (0.0, 0.0)
            for fam_radius, modulation, coefficient in families:
                fam_radius_iv = iv(fam_radius)
                modulation_iv = iv(modulation)
                baseline = family_l1(sigma, fam_radius_iv, coefficient, modulation_iv)
                baseline_total = mpfr.add(baseline_total, (0.0, baseline))
                if 196 <= index <= 443:
                    chosen = production_family(sigma, fam_radius, modulation,
                                                coefficient, left, right)
                else:
                    chosen = baseline
                production_total = mpfr.add(production_total, (0.0, chosen))
            baseline_cells.append(baseline_total[1])
            production_cells.append(production_total[1])
        factor = step ** 3 / 12
        baseline = float(factor * sum((Fraction.from_float(x) for x in baseline_cells), Fraction(0)))
        production = float(factor * sum((Fraction.from_float(x) for x in production_cells), Fraction(0)))
        rows.append({"sigma": float(sigma), "baseline_remainder": baseline,
                     "production_remainder": production,
                     "production_to_baseline": production / baseline,
                     "cell_upper": [float(x) for x in production_cells],
                     "cell_upper_hex": [float(x).hex() for x in production_cells],
                     "cell_upper_nextup_hex": [
                         math.nextafter(float(x), math.inf).hex()
                         for x in production_cells],
                     "cell_upper_max": float(max(production_cells)),
                     "cell_upper_max_index": production_cells.index(max(production_cells)),
                     "cell_upper_safe_max": float(max(production_cells[196:444])),
                     "cell_upper_safe_max_index": 196 + production_cells[196:444].index(
                         max(production_cells[196:444]))})
    result = {"record": 2517,
              "status": "EXTERNAL_DIRECTED_MPFR_PRICE_NOT_A_LEAN_CERTIFICATE",
              "grid": {"cells": cells, "safe_range": [196, 443]},
              "rows": rows,
              "decision": "price_2516_production_upper_against_l1_baseline",
              "nonclaims": ["no Lean literal import", "no producer GO", "no RH"]}
    OUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
