#!/usr/bin/env python3
"""Probe explicit positive lambda choices for the four-point gate.

This is a decision probe only.  It reuses the certified 1918 gate entries and
tests whether a simple owner-scale coefficient can replace the determinant
certificate on the committed class.  It does not certify an analytic bound.
"""

import json
import math
import os


CERT = "results/1918_fourpoint_diagonal_sign_certified.json"
OUT = "results/1945_fourpoint_explicit_lambda_probe.json"


def q_value(case, lam):
    d = case["cert"]["D_cert"]
    c = case["C"]["IC"]
    bsum = case["Bs"]
    return d - lam * bsum + lam * lam * c


def main():
    with open(CERT, encoding="utf-8") as fh:
        cases = json.load(fh)["cases"]

    rows = []
    for case in cases:
        re_rho, im_rho = case["rho"]
        rho_norm = math.hypot(re_rho, im_rho)
        k = 3.0 + rho_norm
        lam_vertex = case["lam_vertex"]
        lam_scale = 0.5 * k**4
        candidates = {
            "vertex": lam_vertex,
            "half_K4": lam_scale,
            "0.9_half_K4": 0.9 * lam_scale,
            "1.1_half_K4": 1.1 * lam_scale,
        }
        q = {name: q_value(case, lam) for name, lam in candidates.items()}
        best = min(q.values())
        rows.append(
            {
                "tag": case["tag"],
                "c": case["c"],
                "rho_norm": rho_norm,
                "K": k,
                "lambda": candidates,
                "Q": q,
                "all_negative": all(value < 0.0 for value in q.values()),
                "best_relative_margin": -best / max(abs(case["cert"]["D_cert"]), 1.0),
            }
        )

    summary = {}
    for name in ("vertex", "half_K4", "0.9_half_K4", "1.1_half_K4"):
        values = [row["Q"][name] for row in rows]
        summary[name] = {
            "negative_count": sum(value < 0.0 for value in values),
            "case_count": len(values),
            "max_Q": max(values),
            "min_Q": min(values),
            "min_relative_margin": min(
                -value / max(abs(row["Q"]["vertex"]), 1.0)
                for row, value in zip(rows, values)
            ),
        }

    result = {"summary": summary, "rows": rows}
    os.makedirs(os.path.dirname(OUT), exist_ok=True)
    with open(OUT, "w", encoding="utf-8") as fh:
        json.dump(result, fh, indent=2)

    print(json.dumps(summary, indent=2))
    print("wrote", OUT)


if __name__ == "__main__":
    main()
