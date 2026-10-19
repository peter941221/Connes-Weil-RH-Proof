#!/usr/bin/env python3
"""Price the existing Lean-style rational jet against one exported cell row.

This is a routing diagnostic only. It reproduces the 2738 rational-exp box
recurrence with mpmath intervals and compares its cell charge to record 3040.
It does not establish the Lean computation or all-cell containment.
"""
import json
import math
import sys
from fractions import Fraction
from pathlib import Path

import mpmath as mp

ROOT = Path(__file__).resolve().parents[1]
ARTIFACT = ROOT / "results/3040_seed_d4d7_cell_upper.json"
OUT = ROOT / "results/3070_seed_rational_box_margin.json"


def reciprocal_jet(values):
    result = [1 / values[0]]
    for order in range(len(values) - 1):
        total = sum(
            math.comb(order + 1, j + 1) * values[j + 1] * result[order - j]
            for j in range(order + 1)
        )
        result.append(-total / values[0])
    return result


def product_jet(left, right):
    return [
        sum(math.comb(order, j) * left[j] * right[order - j]
            for j in range(order + 1))
        for order in range(len(left))
    ]


def endpoint_fraction(interval, upper):
    sign, mantissa, exponent, _ = interval._mpi_[1 if upper else 0]
    value = Fraction((-1 if sign else 1) * mantissa)
    return value * (2 ** exponent if exponent >= 0 else Fraction(1, 2 ** -exponent))


def rational_exp_initial(phase, scale):
    phase_lo = phase.a
    phase_hi = phase.b
    positive_lo = -phase_lo / scale
    positive_hi = -phase_hi / scale

    def taylor(value):
        return sum(value ** j / math.factorial(j) for j in range(20))

    def tail(value):
        return value ** 20 * 21 / (math.factorial(20) * 20)

    lower = 1 / (taylor(positive_lo) + tail(positive_lo)) ** scale
    upper = 1 / (taylor(positive_hi) - tail(positive_hi)) ** scale
    result = mp.iv.mpf([lower.a, upper.b])
    return result


def rational_transition_jet(cell, order, scale):
    coordinate = [cell, mp.iv.mpf(1)] + [mp.iv.mpf(0)] * (order - 1)
    reflected = [1 - cell, -mp.iv.mpf(1)] + [mp.iv.mpf(0)] * (order - 1)
    phase = [a - b for a, b in zip(reciprocal_jet(reflected),
                                   reciprocal_jet(coordinate))]
    exponential = [rational_exp_initial(phase[0], scale)]
    for n in range(order):
        exponential.append(sum(
            math.comb(n, j) * phase[j + 1] * exponential[n - j]
            for j in range(n + 1)
        ))
    denominator = [exponential[0] + 1] + exponential[1:]
    return product_jet(exponential, reciprocal_jet(denominator))


def main():
    mp.iv.dps = 80
    data = json.loads(ARTIFACT.read_text(encoding="utf-8"))
    all_cells = sys.argv[1:] == ["--all"]
    indices = (list(range(8192)) if all_cells else
               ([int(arg) for arg in sys.argv[1:]] or
                [0, 1, 16, 256, 1024, 2048, 4096, 6144, 8191]))
    result = {"record": 3070, "indices": "all" if all_cells else indices,
              "status": "RATIONAL-BOX-ROUTING-DIAGNOSTIC"}
    if not all_cells:
        result["cells"] = {}
    max_excess = {4: (Fraction(0), None), 7: (Fraction(0), None)}
    failures = {4: 0, 7: 0}
    for index in indices:
        left_q = Fraction(8192 + 2047 * index, 33554432)
        right_q = Fraction(8192 + 2047 * (index + 1), 33554432)
        left = mp.iv.mpf(left_q.numerator) / left_q.denominator
        right = mp.iv.mpf(right_q.numerator) / right_q.denominator
        cell = mp.iv.mpf([left.a, right.b])
        coordinate = [cell, mp.iv.mpf(1)] + [mp.iv.mpf(0)] * 6
        reflected = [1 - cell, -mp.iv.mpf(1)] + [mp.iv.mpf(0)] * 6
        phase_zero = reciprocal_jet(reflected)[0] - reciprocal_jet(coordinate)[0]
        scale = max(1, int(mp.ceil(-mp.mpf(phase_zero.a))))
        if not all_cells:
            result["cells"][str(index)] = {"scale": scale, "orders": {}}
        for order in (4, 7):
            jet = rational_transition_jet(cell, order, scale)[order]
            lower_abs = abs(endpoint_fraction(jet, False))
            upper_abs = abs(endpoint_fraction(jet, True))
            jet_upper = max(lower_abs, upper_abs)
            charge = 4 * Fraction(2047, 33554432) * jet_upper
            row = data["rows"][index]
            exported = Fraction(row[str(order)]) - Fraction(data["endpoint_majorant"][str(order)]) / 8192
            excess = charge - exported
            if excess > max_excess[order][0]:
                max_excess[order] = (excess, index)
            failures[order] += excess > Fraction(1, 10**10)
            if not all_cells:
                result["cells"][str(index)]["orders"][str(order)] = {
                    "excess": mp.nstr(mp.mpf(excess.numerator) / excess.denominator, 16),
                    "passes_allowance_1e-20": excess <= Fraction(1, 10**20),
                }
    if all_cells:
        result["summary"] = {
            str(order): {
                "max_excess_cell": max_excess[order][1],
                "max_excess": mp.nstr(mp.mpf(max_excess[order][0].numerator) /
                                       max_excess[order][0].denominator, 20),
                "cells_above_1e-10": failures[order],
                "passes_uniform_allowance_2e-10":
                    max_excess[order][0] <= Fraction(2, 10**10),
            } for order in (4, 7)
        }
        result["uniform_allowance"] = "2e-10 per cell"
        result["total_allowance"] = "1.6384e-6"
        result["nonclaims"] = [
            "mpmath interval routing diagnostic only",
            "does not prove Lean rational row comparisons",
            "does not close D4/D7, row-B pins, carrier, or RH",
        ]
        OUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
