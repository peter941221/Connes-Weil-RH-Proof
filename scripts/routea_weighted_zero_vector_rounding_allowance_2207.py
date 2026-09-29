"""Record 2207: forward-rounding allowance price for the full vector split.

This prices the floating summation and coefficient multiplication allowances
on the binding correction row of 2206. It uses absolute term sums only for
rounding error; the value-level GL-minus-S cancellation remains computed before
the allowance is added. This is a price, not a formal interval certificate.
"""
import importlib.util
import json
import math
import os
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
sp = importlib.util.spec_from_file_location(
    "v2206", ROOT / "scripts" / "routea_weighted_zero_vector_split_full_refinement_2206.py")
v = importlib.util.module_from_spec(sp)
sp.loader.exec_module(v)

OUT = ROOT / "results" / "2207_weighted_zero_vector_rounding_allowance.json"
U = np.finfo(float).eps / 2.0
NODE = 2
NSEG = 1000


def gamma_n(n):
    nu = n * U
    return nu / (1.0 - nu)


def main():
    nodes, fam, A0, _bb, b_corr = v.v.r.matrices(v.v.r.M_REF)
    coeff = np.linalg.solve(A0, b_corr)
    xw = [v.v.q.r.r59.phi_weights(a, panels=6, m=v.M) for a, _ in fam]
    gl_abs = 0.0
    simpson_abs = 0.0
    coeff_round = 0.0
    gl_terms = 0
    simpson_terms = 0
    for c, (a, theta), (X, W) in zip(coeff, fam, xw):
        z = a * (nodes[NODE] + 1j * theta)
        f = np.exp(-v.v.q.r.K / (1.0 - (X / a) ** 2) + z * X)
        gl_abs += abs(c) * float(np.sum(np.abs(W * f)))
        gl_terms += len(X)
        lo_all, hi_all = -a * (1.0 - v.DELTA), a * (1.0 - v.DELTA)
        for panel in range(v.NPAN):
            lo = lo_all + (hi_all - lo_all) * panel / v.NPAN
            hi = lo_all + (hi_all - lo_all) * (panel + 1) / v.NPAN
            xx = np.linspace(lo, hi, 2 * NSEG + 1)
            ff = np.exp(-v.v.q.r.K / (1.0 - (xx / a) ** 2) + z * xx)
            hh = (hi - lo) / (2 * NSEG)
            weights = np.ones(len(xx))
            weights[1:-1:2] = 4.0
            weights[2:-1:2] = 2.0
            simpson_abs += abs(c) * float(hh / 3.0 * np.sum(weights * np.abs(ff)))
            simpson_terms += len(xx)
        coeff_round += U * abs(c) * float(np.sum(np.abs(W * f)))
    # Two independently accumulated rules plus the outer family reduction.
    allow_gl = (gamma_n(gl_terms) + gamma_n(len(fam)) + U) * gl_abs
    allow_s = (gamma_n(simpson_terms) + gamma_n(len(fam)) + U) * simpson_abs
    result = {
        "record": 2207,
        "status": "VECTOR-SPLIT-ROUNDING-ALLOWANCE-PRICE",
        "node": NODE, "rhs": "correction", "unit_roundoff": U,
        "term_counts": {"gl": gl_terms, "simpson": simpson_terms,
                        "families": len(fam)},
        "absolute_term_sums": {"gl": gl_abs, "simpson": simpson_abs},
        "allowances": {"gl": allow_gl, "simpson": allow_s,
                       "coefficient_rounding": coeff_round,
                       "total": allow_gl + allow_s + coeff_round},
        "reference": {"vector_split_bound_2206": 7.225074000015776e-5,
                      "ratio_allowance_to_2206":
                          (allow_gl + allow_s + coeff_round) / 7.225074000015776e-5},
        "nonclaims": [
            "stored float term sums are not outward intervals",
            "no analytic transcendental allowance yet",
            "no complete-owner transfer and no RH claim",
        ],
        "provenance": {
            "script": os.fspath(Path(__file__).relative_to(ROOT)),
            "parent": "scripts/routea_weighted_zero_vector_split_full_refinement_2206.py",
        },
    }
    OUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()

