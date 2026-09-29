"""Record 2206: vectorized full-owner NSEG=1000 split price."""
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
    "v2204", ROOT / "scripts" / "routea_weighted_zero_vector_split_price_2204.py")
v = importlib.util.module_from_spec(sp)
sp.loader.exec_module(v)

OUT = ROOT / "results" / "2206_weighted_zero_vector_split_full_refinement.json"
M = 6400
DELTA = 0.05
NPAN = 12
NSEG = 1000


def max_h_vec(lo, hi, a, z):
    out = np.empty(len(z), dtype=float)
    rz = np.real(z)
    for k in range(len(z)):
        def der(x):
            u = x / a
            q = 1.0 - u * u
            if q <= 0.0:
                return math.inf if u < 0.0 else -math.inf
            return -2.0 * v.q.r.K * u / (a * q * q) + rz[k]
        dlo, dhi = der(lo), der(hi)
        if dlo <= 0.0:
            x = lo
        elif dhi >= 0.0:
            x = hi
        else:
            l, h = lo, hi
            for _ in range(60):
                m = (l + h) / 2.0
                if der(m) > 0.0:
                    l = m
                else:
                    h = m
            x = (l + h) / 2.0
        u = x / a
        out[k] = -v.q.r.K / (1.0 - u * u) + rz[k] * x
    return out


def one_family(a, theta, nodes, coeff):
    X, W = v.q.r.r59.phi_weights(a, panels=6, m=M)
    z = a * (np.asarray(nodes, complex) + 1j * theta)
    f = np.exp(-v.q.r.K / (1.0 - (X / a) ** 2)[None, :] + z[:, None] * X[None, :])
    edge = np.abs(X / a) > 1.0 - DELTA
    gl_inner = np.sum(f[:, ~edge] * W[~edge][None, :], axis=1)
    gl_edge = np.sum(f[:, edge] * W[edge][None, :], axis=1)
    s_total = np.zeros(len(nodes), complex)
    err_s = np.zeros(len(nodes), float)
    lo_all, hi_all = -a * (1.0 - DELTA), a * (1.0 - DELTA)
    for panel in range(NPAN):
        lo = lo_all + (hi_all - lo_all) * panel / NPAN
        hi = lo_all + (hi_all - lo_all) * (panel + 1) / NPAN
        xx = np.linspace(lo, hi, 2 * NSEG + 1)
        ff = np.exp(-v.q.r.K / (1.0 - (xx / a) ** 2)[None, :] +
                    z[:, None] * xx[None, :])
        hh = (hi - lo) / (2 * NSEG)
        s_total += hh / 3.0 * (ff[:, 0] + ff[:, -1] +
                               4.0 * np.sum(ff[:, 1:-1:2], axis=1) +
                               2.0 * np.sum(ff[:, 2:-1:2], axis=1))
        umax = max(abs(lo / a), abs(hi / a))
        qmin = 1.0 - umax * umax
        h1 = np.abs(z) + 2.0 * v.q.r.K * umax / (a * qmin ** 2)
        h2 = v.q.r.K / a ** 2 * (2.0 / qmin ** 2 + 8.0 * umax ** 2 / qmin ** 3)
        h3 = v.q.r.K / a ** 3 * (24.0 * umax / qmin ** 3 +
                                 48.0 * umax ** 3 / qmin ** 4)
        h4 = v.q.r.K / a ** 4 * (24.0 / qmin ** 3 +
                                 288.0 * umax ** 2 / qmin ** 4 +
                                 384.0 * umax ** 4 / qmin ** 5)
        bell = h4 + 4.0 * h1 * h3 + 3.0 * h2 ** 2 + 6.0 * h1 ** 2 * h2 + h1 ** 4
        env = np.exp(max_h_vec(lo, hi, a, z)) * bell
        err_s += (hi - lo) / 180.0 * hh ** 4 * env
    edge_i = 2.0 * a * DELTA * np.exp(np.maximum(
        max_h_vec(-a, -a * (1.0 - DELTA), a, z),
        max_h_vec(a * (1.0 - DELTA), a, a, z)))
    return gl_inner, s_total, gl_edge, err_s, edge_i


def main():
    nodes, fam, A0, b_base, b_corr = v.r.matrices(v.r.M_REF)
    out_rows = []
    for rhs, b in (("base", b_base), ("correction", b_corr)):
        coeff = np.linalg.solve(A0, b)
        gi = np.zeros(len(nodes), complex)
        si = np.zeros(len(nodes), complex)
        ge = np.zeros(len(nodes), complex)
        es = np.zeros(len(nodes), float)
        ei = np.zeros(len(nodes), float)
        for c, (a, theta) in zip(coeff, fam):
            x = one_family(a, theta, nodes, coeff)
            gi += c * x[0]
            si += c * x[1]
            ge += c * x[2]
            es += abs(c) * x[3]
            ei += abs(c) * x[4]
        bounds = np.abs(gi - si) + es + np.abs(ge) + ei
        k = int(np.argmax(bounds))
        out_rows.append({
            "rhs": rhs, "worst_node": k, "max_bound": float(bounds[k]),
            "computed_inner_difference": float(abs(gi[k] - si[k])),
            "simpson_remainder": float(es[k]),
            "computed_edge_sum": float(abs(ge[k])),
            "edge_integral_bound": float(ei[k]),
            "coefficient_inf": float(np.max(np.abs(coeff))),
            "all_bounds_max": float(np.max(bounds)),
            "all_bounds_min": float(np.min(bounds)),
        })
    result = {
        "record": 2206,
        "status": "VECTOR-SPLIT-FULL-OWNER-REFINEMENT",
        "rule": {"m_per_panel": M, "delta_u": DELTA,
                 "inner_panels": NPAN, "simpson_half_panels": NSEG},
        "rows": out_rows,
        "nonclaims": [
            "floating GL and Simpson sums are not outward intervals",
            "transcendental and summation allowances are not charged",
            "no complete-owner transfer and no RH claim",
        ],
        "provenance": {
            "script": os.fspath(Path(__file__).relative_to(ROOT)),
            "parent": "scripts/routea_weighted_zero_vector_split_price_2204.py",
        },
    }
    OUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
