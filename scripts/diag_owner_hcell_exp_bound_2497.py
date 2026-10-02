"""Diagnostic for the first formal hcell strategy (record 2497).

Replace every local bump exponent by the uniform bound exp(-30) <= 1e-13,
then compare the resulting per-cell family sum with the corrected 2496 table.
This is a routing probe only; it is not a certificate.
"""
import importlib.util
import json
import math
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ARTIFACT = ROOT / "results/2495_owner_family_hybrid_mpfr_exact.json"
REPAIR = ROOT / "results/2338_exact_interpolation_repair.json"
CAPTURE = ROOT / "results/2275_gap_owner_audit.json"

spec = importlib.util.spec_from_file_location(
    "routea_mpfr_2497", ROOT / "scripts/routea_owner_local_curvature_mpfr_2478.py")
base = importlib.util.module_from_spec(spec)
spec.loader.exec_module(base)
mpfr = base.mpfr


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


def coarse_bump(order, radius, left, right, step):
    constants = (1, 60, 3720)
    global_bound = mpfr.mul(iv(Fraction(constants[order])),
                            mpfr.div(iv(Fraction(1, 10**13)),
                                     iv_pow(radius, order)))
    lo = max(left[0], -radius[1] + step[1] / 1000)
    hi = min(right[1], radius[1] - step[1] / 1000)
    if lo >= hi:
        return global_bound
    t = mpfr.div((base.outward(lo)[0], base.outward(hi)[1]), radius)
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
    value = mpfr.div(mpfr.mul(iv(Fraction(1, 10**13)), base.abs_iv(p)),
                     mpfr.mul(d2q, iv_pow(radius, order)))
    return (min(value[0], global_bound[0]), max(value[1], global_bound[1]))


def coarse_family(sigma, radius, modulation, coefficient, left, right, step):
    bumps = [coarse_bump(k, radius, left, right, step) for k in range(3)]
    ext = []
    for order in range(3):
        value = (0.0, 0.0)
        for j in range(order + 1):
            term = mpfr.mul(iv(Fraction(math.comb(order, j))),
                            mpfr.mul(iv_pow(base.abs_iv(modulation), j),
                                     bumps[order - j]))
            value = mpfr.add(value, term)
        ext.append(value)
    weighted = mpfr.add(ext[2], mpfr.add(
        mpfr.mul(iv(Fraction(2 * abs(sigma))), ext[1]),
        mpfr.mul(iv(Fraction(sigma * sigma)), ext[0])))
    weight = mpfr.unary("mpfr_exp", mpfr.mul(iv(sigma), (left[0], right[1])))
    return mpfr.mul(coefficient, mpfr.mul(weight, weighted))[1]


def main():
    artifact = json.loads(ARTIFACT.read_text(encoding="utf-8"))
    repair = json.loads(REPAIR.read_text(encoding="utf-8"))
    capture = json.loads(CAPTURE.read_text(encoding="utf-8"))["owner_capture"]
    families = []
    for row, pair in zip(repair["coefficient_rows"], capture["families_hex"]):
        re = (rat(row["ideal_base_coefficient"]["real"]["lower_exact"]) +
              rat(row["ideal_base_coefficient"]["real"]["upper_exact"])) / 2
        im = (rat(row["ideal_base_coefficient"]["imag"]["lower_exact"]) +
              rat(row["ideal_base_coefficient"]["imag"]["upper_exact"])) / 2
        families.append((iv(Fraction.from_float(float.fromhex(pair[0]) ** 2)),
                         iv(Fraction.from_float(float.fromhex(pair[1]))),
                         iv(abs(re) + abs(im))))
    radius = Fraction(2076918743413931851756481, 316912650057057350374175801344)
    # Use the exact radius from the replay artifact rather than the diagnostic typo above.
    radius = Fraction(2076918743413931858457251756481,
                      316912650057057350374175801344)
    substep = 2 * radius / 640
    summary = []
    for row in artifact["rows"]:
        sigma = Fraction(str(row["sigma"]))
        failures = 0
        worst = 0.0
        worst_cell = None
        for index in range(640):
            left = -radius + index * substep
            right = left + substep
            total = (0.0, 0.0)
            for fam_radius, modulation, coefficient in families:
                if max(abs(left), abs(right)) < max(fam_radius):
                    value = coarse_family(sigma, fam_radius, modulation, coefficient,
                                          iv(left), iv(right), iv(substep))
                else:
                    value = (0.0, 0.0)
                total = mpfr.add(total, (0.0, value[1] if isinstance(value, tuple) else value))
            table = float.fromhex(row["hybrid_cell_upper_bounds"][index]["hex"])
            ratio = total[1] / table if table else 0.0
            if ratio > 1:
                failures += 1
            if ratio > worst:
                worst, worst_cell = ratio, index
        summary.append({"sigma": float(sigma), "cells_over_table": failures,
                        "worst_ratio": worst, "worst_cell": worst_cell})
    print(json.dumps({"record": 2497, "uniform_exp_upper": 1e-13,
                      "summary": summary,
                      "decision": "uniform_bound_is_only_a_routing_probe"}, indent=2))


if __name__ == "__main__":
    main()
