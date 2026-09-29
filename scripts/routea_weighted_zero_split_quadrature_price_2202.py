"""Record 2202: endpoint-split quadrature error price for the 2197 matrix.

The outer panels of the Gevrey bump touch |x/a|=1, so an ellipse estimate is
not applicable. This probe uses the valid split identity

  |GL-I| <= |GL-S_inner| + |S_inner-I_inner| + |GL_edge| + |I_edge|.

The inner term uses composite Simpson with an explicit fourth-derivative
envelope. The edge integral is bounded directly by length times the maximum
of the concave real exponent. The result is a price for the matrix error; it
is not yet a certificate for the full route because the transcendental input
rounding and the final interval assembly remain to be charged.
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
spec = importlib.util.spec_from_file_location(
    "r2197", ROOT / "scripts" /
    "routea_weighted_zero_direct_product_mass_screen_2197.py")
r = importlib.util.module_from_spec(spec)
spec.loader.exec_module(r)

OUT = ROOT / "results" / "2202_weighted_zero_split_quadrature_price.json"
M = 6400
DELTA = 0.05
NPAN = 12
NSEG = 20


def h_real(x, a, z):
    u = x / a
    return -r.K / (1.0 - u * u) + float(np.real(z)) * x


def max_h(lo, hi, a, z):
    """Concave maximum, with a bisection derivative root."""
    re_z = float(np.real(z))

    def der(x):
        u = x / a
        q = 1.0 - u * u
        if q <= 0.0:
            return math.inf if u < 0.0 else -math.inf
        return -2.0 * r.K * u / (a * q * q) + re_z

    dlo, dhi = der(lo), der(hi)
    if dlo <= 0.0:
        x = lo
    elif dhi >= 0.0:
        x = hi
    else:
        l, h = lo, hi
        for _ in range(70):
            m = (l + h) / 2.0
            if der(m) > 0.0:
                l = m
            else:
                h = m
        x = (l + h) / 2.0
    return h_real(x, a, z)


def derivative_bound(lo, hi, a, z):
    umax = max(abs(lo / a), abs(hi / a))
    qmin = 1.0 - umax * umax
    h1 = abs(z) + 2.0 * r.K * umax / (a * qmin ** 2)
    h2 = r.K / a ** 2 * (2.0 / qmin ** 2 + 8.0 * umax ** 2 / qmin ** 3)
    h3 = r.K / a ** 3 * (24.0 * umax / qmin ** 3 +
                          48.0 * umax ** 3 / qmin ** 4)
    h4 = r.K / a ** 4 * (24.0 / qmin ** 3 +
                          288.0 * umax ** 2 / qmin ** 4 +
                          384.0 * umax ** 4 / qmin ** 5)
    bell = h4 + 4.0 * h1 * h3 + 3.0 * h2 ** 2 + 6.0 * h1 ** 2 * h2 + h1 ** 4
    return math.exp(max_h(lo, hi, a, z)) * bell


def one_entry(a, z, XW):
    X, W = XW
    f = np.exp(-r.K / (1.0 - (X / a) ** 2) + z * X)
    edge = np.abs(X / a) > 1.0 - DELTA
    gl_edge = float(np.sum(np.abs(W[edge] * f[edge])))
    inn_lo, inn_hi = -a * (1.0 - DELTA), a * (1.0 - DELTA)
    s_total = 0.0j
    err_s = 0.0
    for j in range(NPAN):
        lo = inn_lo + (inn_hi - inn_lo) * j / NPAN
        hi = inn_lo + (inn_hi - inn_lo) * (j + 1) / NPAN
        n = NSEG
        xx = np.linspace(lo, hi, 2 * n + 1)
        ff = np.exp(-r.K / (1.0 - (xx / a) ** 2) + z * xx)
        hh = (hi - lo) / (2 * n)
        s_panel = hh / 3.0 * (ff[0] + ff[-1] +
                              4.0 * np.sum(ff[1:-1:2]) +
                              2.0 * np.sum(ff[2:-1:2]))
        s_total += s_panel
        err_s += (hi - lo) / 180.0 * hh ** 4 * derivative_bound(lo, hi, a, z)
    gl_inner = np.sum(W[~edge] * f[~edge])
    edge_integral = 2.0 * a * DELTA * math.exp(
        max(max_h(-a, -a * (1.0 - DELTA), a, z),
            max_h(a * (1.0 - DELTA), a, a, z)))
    err = abs(gl_inner - s_total) + err_s + gl_edge + edge_integral
    return float(err), float(abs(gl_inner - s_total)), float(err_s), float(gl_edge), float(edge_integral)


def main():
    nodes, _values, fam = r.owner_family()
    XW = [r.r59.phi_weights(a, panels=6, m=M) for a, _ in fam]
    max_err = 0.0
    arg = None
    rows = []
    for j, (a, theta) in enumerate(fam):
        local = 0.0
        for i, s in enumerate(nodes):
            z = a * (s + 1j * theta)
            vals = one_entry(a, z, XW[j])
            local = max(local, vals[0])
            if vals[0] > max_err:
                max_err, arg = vals[0], (i, j, float(a), float(theta))
        rows.append({"family": j, "max_entry_error": local})
    result = {
        "record": 2202,
        "status": "ENDPOINT-SPLIT-QUADRATURE-PRICE",
        "owner_nodes": len(nodes),
        "rule": {"m_per_panel": M, "panels": 6, "delta_u": DELTA,
                 "inner_panels": NPAN, "simpson_half_panels": NSEG},
        "max_matrix_entry_error_bound": max_err,
        "argmax": arg,
        "family_rows": rows,
        "nonclaims": [
            "transcendental rounding is not yet charged",
            "this is an entrywise quadrature price, not a complete interval solve",
            "no complete-owner transfer and no RH claim",
        ],
        "provenance": {"script": os.fspath(Path(__file__).relative_to(ROOT)),
                       "parent": "scripts/routea_weighted_zero_direct_product_mass_screen_2197.py"},
    }
    OUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
