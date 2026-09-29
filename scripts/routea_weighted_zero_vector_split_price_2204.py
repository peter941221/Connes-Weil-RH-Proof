"""Record 2204: vector-aware endpoint-split quadrature price.

For each interpolation right-hand side, this prices A*c directly. The computed
GL-inner minus Simpson-inner sum is formed after multiplying by the actual
solve coefficients and summing all families, preserving matrix-level
cancellation. Only the Simpson remainder and endpoint integral terms are
charged by absolute envelopes. This is a preflight, not an outward
certificate: floating quadrature and transcendental rounding allowances are
not yet formalized.
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
s2202 = importlib.util.spec_from_file_location(
    "s2202", ROOT / "scripts" / "routea_weighted_zero_split_quadrature_price_2202.py")
q = importlib.util.module_from_spec(s2202)
s2202.loader.exec_module(q)
s2201 = importlib.util.spec_from_file_location(
    "s2201", ROOT / "scripts" / "routea_weighted_zero_solve_enclosure_preflight_2201.py")
r = importlib.util.module_from_spec(s2201)
s2201.loader.exec_module(r)

OUT = ROOT / "results" / "2204_weighted_zero_vector_split_price.json"
M = 6400
DELTA = 0.05
NPAN = 12
NSEG = 100


def family_terms(a, z, XW):
    X, W = XW
    f = np.exp(-q.r.K / (1.0 - (X / a) ** 2) + z * X)
    edge = np.abs(X / a) > 1.0 - DELTA
    gl_edge = np.sum(W[edge] * f[edge])
    gl_inner = np.sum(W[~edge] * f[~edge])
    lo_all, hi_all = -a * (1.0 - DELTA), a * (1.0 - DELTA)
    s_total = 0.0j
    err_s = 0.0
    for panel in range(NPAN):
        lo = lo_all + (hi_all - lo_all) * panel / NPAN
        hi = lo_all + (hi_all - lo_all) * (panel + 1) / NPAN
        xx = np.linspace(lo, hi, 2 * NSEG + 1)
        ff = np.exp(-q.r.K / (1.0 - (xx / a) ** 2) + z * xx)
        hh = (hi - lo) / (2 * NSEG)
        s_total += hh / 3.0 * (ff[0] + ff[-1] +
                               4.0 * np.sum(ff[1:-1:2]) +
                               2.0 * np.sum(ff[2:-1:2]))
        err_s += (hi - lo) / 180.0 * hh ** 4 * q.derivative_bound(lo, hi, a, z)
    edge_i = 2.0 * a * DELTA * math.exp(
        max(q.max_h(-a, -a * (1.0 - DELTA), a, z),
            q.max_h(a * (1.0 - DELTA), a, a, z)))
    return gl_inner, s_total, gl_edge, err_s, edge_i


def main():
    nodes, fam, A0, b_base, b_corr = r.matrices(r.M_REF)
    XW = [q.r.r59.phi_weights(a, panels=6, m=M) for a, _ in fam]
    rows = []
    for rhs, b in (("base", b_base), ("correction", b_corr)):
        coeff = np.linalg.solve(A0, b)
        worst = None
        for i, s in enumerate(nodes):
            gl_minus_s = 0.0j
            gl_edge = 0.0j
            err_s = 0.0
            edge_i = 0.0
            for c, (a, theta), xw in zip(coeff, fam, XW):
                gi, si, ge, es, ei = family_terms(a, a * (s + 1j * theta), xw)
                gl_minus_s += c * (gi - si)
                gl_edge += c * ge
                err_s += abs(c) * es
                edge_i += abs(c) * ei
            bound = abs(gl_minus_s) + err_s + abs(gl_edge) + edge_i
            record = {
                "node": i, "bound": float(bound),
                "computed_inner_difference": float(abs(gl_minus_s)),
                "simpson_remainder": float(err_s),
                "computed_edge_sum": float(abs(gl_edge)),
                "edge_integral_bound": float(edge_i),
            }
            if worst is None or bound > worst["bound"]:
                worst = record
        rows.append({"rhs": rhs, "worst": worst,
                     "coefficient_inf": float(np.max(np.abs(coeff)))})
    result = {
        "record": 2204,
        "status": "VECTOR-AWARE-ENDPOINT-SPLIT-PRICE",
        "rule": {"m_per_panel": M, "delta_u": DELTA,
                 "inner_panels": NPAN, "simpson_half_panels": NSEG},
        "rows": rows,
        "nonclaims": [
            "floating GL and Simpson sums are not outward intervals",
            "transcendental and summation allowances are not charged",
            "no complete-owner transfer and no RH claim",
        ],
        "provenance": {
            "script": os.fspath(Path(__file__).relative_to(ROOT)),
            "parents": [
                "scripts/routea_weighted_zero_split_quadrature_price_2202.py",
                "scripts/routea_weighted_zero_solve_enclosure_preflight_2201.py",
            ],
        },
    }
    OUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()

