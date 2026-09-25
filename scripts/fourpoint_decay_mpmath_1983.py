#!/usr/bin/env python3
# fourpoint_decay_mpmath_1983.py — record 1983 addendum (probe C resolution)
#
# The record-1983 decay probe hit an instrument floor: at k = 30 the
# Gevrey window phi = exp(-k/(1-(x/a)^2)) has mass ~ a*e^{-k} ~ 1e-13, so
# its Laplace transform sinks below the double-precision quadrature noise
# around t ~ 60, BEFORE the sqrt(t) asymptotic regime.  The flat c_eff ~ 0
# fits on [50,400] are the floor, not mathematics.
#
# Floor mechanism (two layers, both fixed here):
#   (a) float64 quadrature WEIGHTS/NODES have relative error 1e-16, and
#       the total weight mass is ~1e-13, giving an ABSOLUTE floor
#       1e-16 * 1e-13 = 1e-29 ~ e^{-67} -- exactly the flat level the
#       first mpmath attempt measured (mpmath precision was defeated by
#       float64 inputs);
#   (b) double-precision summation noise (the original probe C floor).
#
# This script computes EVERYTHING in mpmath at 80 decimals: composite
# Gauss-Legendre nodes refined by Newton on P_m (three-term recurrence),
# weights w = 2/((1-x^2) P_m'(x)^2), then
#   L_phi(i t) = int phi(x) e^{i t x} dx,  phi = exp(-k/(1-(x/a)^2)),
# for a in {2.0, 3.2}, t in {50,100,200,400}, fitted against the edge-
# saddle law  log|L| ~ -sqrt(k a t)  (NOTE: the record-1983 script's
# c_theory_saddle = sqrt(k a / 2) is a factor sqrt(2) low -- erratum).
#
# Pure diagnostic; no gate sign and no RH claim.

import json
import os

import numpy as np
from mpmath import mp

K = 30.0
DPS = 80


def leggauss_mp(m):
    """m-node Gauss-Legendre on [-1, 1] at DPS decimals."""
    mp.dps = DPS
    xs0, _ws0 = np.polynomial.legendre.leggauss(m)
    out = []
    for x0 in xs0:
        x = mp.mpf(float(x0))
        for _ in range(8):
            p0, p1 = mp.mpf(1), x
            for j in range(2, m + 1):
                p0, p1 = p1, ((2 * j - 1) * x * p1 - (j - 1) * p0) / j
            dp = m * (x * p1 - p0) / (x * x - 1)
            x = x - p1 / dp
        p0, p1 = mp.mpf(1), x
        for j in range(2, m + 1):
            p0, p1 = p1, ((2 * j - 1) * x * p1 - (j - 1) * p0) / j
        dp = m * (x * p1 - p0) / (x * x - 1)
        w = 2 / ((1 - x * x) * dp * dp)
        out.append((x, w))
    return out


def composite_nodes(a, panels=20, m=100):
    base = leggauss_mp(m)
    mp.dps = DPS
    X, W = [], []
    edges = [mp.mpf(-a) + (mp.mpf(2 * a) * j) / panels
             for j in range(panels + 1)]
    for j in range(panels):
        lo, hi = edges[j], edges[j + 1]
        half, mid = (hi - lo) / 2, (hi + lo) / 2
        for x, w in base:
            X.append(mid + half * x)
            W.append(half * w)
    return X, W


def laplace_mp(X, W, a, k, t):
    mp.dps = DPS
    total = mp.mpc(0)
    for x, w in zip(X, W):
        u = x / mp.mpf(a)
        if abs(u) < 1:
            f = mp.exp(-mp.mpf(k) / (1 - u * u))
            total += f * mp.exp(1j * mp.mpf(t) * x) * w
    return total


def main():
    out_rows = []
    for a in (2.0, 3.2):
        X, W = composite_nodes(a)
        mass = laplace_mp(X, W, a, K, 0.0)
        prof = {}
        for t in (50.0, 100.0, 200.0, 400.0):
            L = laplace_mp(X, W, a, K, t)
            prof["%.0f" % t] = float(mp.log(abs(L)))
            print("a=%.1f t=%3.0f  log|L| = %12.4f  (saddle %9.2f)"
                  % (a, t, float(mp.log(abs(L))),
                     -np.sqrt(K * a * t)), flush=True)
        c = {}
        for t1, t2 in ((50.0, 100.0), (100.0, 200.0), (200.0, 400.0)):
            y1, y2 = prof["%.0f" % t1], prof["%.0f" % t2]
            c["%g_%g" % (t1, t2)] = -(y2 - y1) / (np.sqrt(t2) - np.sqrt(t1))
        out_rows.append({
            "a": a, "log_mass": float(mp.log(abs(mass))),
            "log_abs_L": prof,
            "c_eff_sqrt": c,
            "c_saddle_pred": float(np.sqrt(K * a)),
        })
        print("a=%.1f  log mass = %.2f ; c_eff: 50-100 %+.3f  100-200 %+.3f"
              "  200-400 %+.3f  (saddle %.3f)"
              % (a, float(mp.log(abs(mass))), c["50_100"], c["100_200"],
                 c["200_400"], np.sqrt(K * a)), flush=True)
    report = {
        "record": 1983,
        "status": "DECAY_FLOOR_RESOLUTION_V2",
        "k": K, "sigma": 0.0, "dps": DPS,
        "method": "mpmath dps=80 everywhere (nodes, weights, sum); "
                  "composite GL 20 panels x 100 nodes",
        "rows": out_rows,
    }
    out = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..",
                       "results", "1983_decay_mpmath.json")
    with open(out, "w", encoding="utf-8") as stream:
        stream.write(json.dumps(report, indent=2) + "\n")
    print("wrote %s" % os.path.abspath(out), flush=True)


if __name__ == "__main__":
    main()
