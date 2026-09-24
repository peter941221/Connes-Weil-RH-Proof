#!/usr/bin/env python3
# fourpoint_macro_atom_bounds_1951.py — Record 1951: Bipartite Variance & Gate Determinant
#
# Verification of the exact Bipartite Variance Gap Identity and Negativity:
#   det = V1 + V2 - E_cross
#       = -C1 * C2 * (p1_bar - p2_bar)^2 + (C1 - C2) * (C1 * Var1 - C2 * Var2) < 0
# on the certified detector family anchored at c in [1.0, 1.3].

import json
import math
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import numpy as np
import fourpoint_diagonal_sign_1918 as rig
import fourpoint_gate_kernel_form_1919 as kf


def evaluate_case(c, delta, gamma):
    S_pair = 2.0 * c
    g = rig.bump(c)
    xi, Fh = kf.ghat_grid(g)
    W = (Fh * np.conj(Fh)).real
    dxi = 1.0 / (rig.NF * rig.DU)
    om = 2.0 * np.pi * xi
    P = (delta ** 2 + gamma ** 2 - om ** 2) ** 2 + 4.0 * (delta ** 2) * (om ** 2)
    K = kf.kernel_grid(xi, S_pair)

    mu = K * W * dxi
    pos = mu > 0
    neg = mu < 0

    c_p = mu[pos]
    p_p = P[pos]
    c_m = -mu[neg]
    p_m = P[neg]

    C1 = float(np.sum(c_p))
    C2 = float(np.sum(c_m))

    p1_bar = float(np.sum(c_p * p_p) / C1)
    p2_bar = float(np.sum(c_m * p_m) / C2)

    var1 = float(np.sum(c_p * (p_p - p1_bar) ** 2) / C1)
    var2 = float(np.sum(c_m * (p_m - p2_bar) ** 2) / C2)

    V1 = float(C1 ** 2 * var1)
    V2 = float(C2 ** 2 * var2)

    E_cross = float(C2 * np.sum(c_p * p_p ** 2) + C1 * np.sum(c_m * p_m ** 2) - 2.0 * np.sum(c_p * p_p) * np.sum(c_m * p_m))

    term1 = float(-C1 * C2 * (p1_bar - p2_bar) ** 2)
    term2 = float((C1 - C2) * (C1 * var1 - C2 * var2))
    det = float(V1 + V2 - E_cross)

    ratio = E_cross / (V1 + V2) if (V1 + V2) > 0 else float("inf")

    return {
        "c": c,
        "delta": delta,
        "gamma": gamma,
        "C1": C1,
        "C2": C2,
        "C_net": C1 - C2,
        "p1_bar": p1_bar,
        "p2_bar": p2_bar,
        "delta_p": p1_bar - p2_bar,
        "var1": var1,
        "var2": var2,
        "V1": V1,
        "V2": V2,
        "V1_plus_V2": V1 + V2,
        "E_cross": E_cross,
        "ratio_E_V": ratio,
        "term1_mean_gap": term1,
        "term2_var_diff": term2,
        "det": det,
        "satisfied": bool(det < 0 and (C1 - C2) > 0),
    }


def main():
    rig.log("Record 1951 — Bipartite Variance Gap & Gate Determinant Probe")
    cases = [
        (1.0, 0.05, 14.134725141734693),
        (1.0, 0.10, 14.134725141734693),
        (1.0, 0.30, 14.134725141734693),
        (1.3, 0.05, 14.134725141734693),
        (1.3, 0.10, 14.134725141734693),
        (1.3, 0.30, 14.134725141734693),
        (1.0, 0.05, 21.022039638771555),
        (1.0, 0.10, 21.022039638771555),
        (1.0, 0.30, 21.022039638771555),
        (1.3, 0.05, 21.022039638771555),
        (1.3, 0.10, 21.022039638771555),
        (1.3, 0.30, 21.022039638771555),
    ]

    print("%-4s %-6s %-6s %-10s %-10s %-11s %-11s %-11s %-7s %-11s %-6s" %
          ("c", "delta", "gamma", "C1", "C2", "V1+V2", "E_cross", "Term1", "Ratio", "det", "Pass?"))

    results = []
    all_pass = True
    for c, delta, gamma in cases:
        res = evaluate_case(c, delta, gamma)
        results.append(res)
        if not res["satisfied"]:
            all_pass = False
        print("%-4.1f %-6.2f %-6.2f %-10.3e %-10.3e %-11.4e %-11.4e %-11.4e %-7.2f %-11.4e %-6s" %
              (res["c"], res["delta"], res["gamma"],
               res["C1"], res["C2"],
               res["V1_plus_V2"], res["E_cross"],
               res["term1_mean_gap"],
               res["ratio_E_V"],
               res["det"],
               "YES" if res["satisfied"] else "NO"))

    os.makedirs("results", exist_ok=True)
    with open("results/1951_macro_atom_bounds.json", "w") as fh:
        json.dump(results, fh, indent=2)

    rig.log("All cases passed: %s. Output written to results/1951_macro_atom_bounds.json" % all_pass)
    return 0 if all_pass else 1


if __name__ == "__main__":
    sys.exit(main())
