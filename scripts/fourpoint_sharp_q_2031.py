#!/usr/bin/env python3
"""Record 2031: sharp weighted q-ladder for the powered-seed base (R-B1).

Object.  The contraction premise is

    ||laplaceAt base (sigma + i*t)|| <= q          for |t| >= T,

where base(s) = sum_z c_z * P(z,s) * L(s-z), L = laplaceAt poweredSeed with
L(w) = S_seed(w/2)^10 and S_seed the Laplace transform of the committed
smoothSeed.

Method.  For k >= 1, integrate by parts k times on the support [-2,2]:

    |S_seed(a + i*y)| <= W_k(a) / |a + i*y|^k,
    W_k(a) = integral_{-2}^{2} e^{a x} |smoothSeed^{(k)}(x)| dx

is the SHARP WEIGHTED mass (record 1982 used the crude e^{2|a|} * D_k with
D_k = integral |f^{(k)}|, which loses the location of the derivative mass).

Everything is high precision (mpmath, 40 digits).  The seed constants are
exact where they can be: S_seed(0) = 3, D_0 = 3, D_1 = 2, D_2 = 8.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np
from mpmath import mp, mpf, mpc, exp, factorial, binomial

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import fourpoint_actual_owner_1980 as op  # noqa: E402

mp.dps = 40

RHO = complex(0.55, 14.134725141734693)
N = 4
T_MIN = 28.0
T_MAX = 200.0
DT = 0.5
SIGMA_MAX = 1.0
Q = 2.0 ** -14
SEED0 = 3.0 ** 10          # laplaceAt poweredSeed 0, exact
K_MAX = 6
A_GRID = np.arange(-0.60, 0.6001, 0.01)


def h_deriv(u, j):
    return ((-1) ** j) * factorial(j) / u ** (j + 1) - factorial(j) / (1 - u) ** (j + 1)


def T_deriv(u, k):
    """k-th derivative of the Mathlib smoothTransition at u, exact recurrence."""
    h = h_deriv(u, 0)
    T = 1 / (1 + exp(h))
    Ts, Gs = [T], [T - T * T]
    for n in range(k):
        acc = mp.mpf(0)
        for j in range(n + 1):
            acc += binomial(n, j) * h_deriv(u, j + 1) * Gs[n - j]
        Ts.append(-acc)
        m = n + 1
        g = Ts[m]
        for j in range(m + 1):
            g -= binomial(m, j) * Ts[j] * Ts[m - j]
        Gs.append(g)
    return Ts[k]


def sign_pieces(k, n_scan=4000, eps=mpf(10) ** -13):
    """Return the sign-free subintervals of (0,1) for |T^(k)|."""
    xs = [eps + (1 - 2 * eps) * i / n_scan for i in range(n_scan + 1)]
    vals = [T_deriv(x, k) for x in xs]
    roots = []
    for i in range(n_scan):
        a, b = vals[i], vals[i + 1]
        if a * b < 0:
            lo, hi, flo = xs[i], xs[i + 1], a
            for _ in range(160):
                mid = (lo + hi) / 2
                fm = T_deriv(mid, k)
                if flo * fm <= 0:
                    hi = mid
                else:
                    lo, flo = mid, fm
            roots.append((lo + hi) / 2)
    return [eps] + roots + [1 - eps]


def nodes_weights(k, n_gl=100):
    """Gauss-Legendre nodes/weights carrying |T^(k)| on each sign piece."""
    pieces = sign_pieces(k)
    us, ws = [], []
    for p, q in zip(pieces[:-1], pieces[1:]):
        if q <= p:
            continue
        xg, wg = np.polynomial.legendre.leggauss(n_gl)
        for xi, wi in zip(xg, wg):
            u = mpf(p) + (mpf(q) - mpf(p)) * (mpf(xi) + 1) / 2
            w = mpf(wi) * (mpf(q) - mpf(p)) / 2
            us.append(u)
            ws.append(abs(T_deriv(u, k)) * w)
    return us, ws


def Wk_from_nodes(us, ws, a):
    return sum(w * exp(a * u) for u, w in zip(us, ws))


def S_seed(s):
    """Exact 3-piece Laplace transform of smoothSeedRaw."""
    def That(t):
        return mp.quad(lambda u: exp(t * u) / (1 + exp(1 / u - 1 / (1 - u))),
                       [mpf(10) ** -13, 1 - mpf(10) ** -13])
    mid = (exp(s) - exp(-s)) / s if s != 0 else mp.mpf(2)
    return exp(-2 * s) * That(s) + mid + exp(2 * s) * That(-s)


def main() -> None:
    owner, targets, radius, known = op.build_owner(RHO, N)
    active = [(z, op.target_value(RHO, z)) for z in targets
              if abs(op.target_value(RHO, z)) > 0]

    data = {}
    for k in range(1, K_MAX + 1):
        us, ws = nodes_weights(k)
        # A_k(a) = integral_0^1 e^{a u} |T^(k)(u)| du on the a-grid
        data[k] = [Wk_from_nodes(us, ws, mpf(a)) for a in A_GRID]

    def Ak_lookup(k, a):
        idx = int(np.searchsorted(A_GRID, a))
        idx = min(max(idx, 0), len(A_GRID) - 1)
        return data[k][idx]

    def Wk_lookup(k, a):
        """W_k(a) = integral_{-2}^{2} e^{a x} |f^(k)| dx
                  = e^{-2a} A_k(a) + e^{2a} A_k(-a),
        conservatively rounded outward: A_k is increasing in a, so the
        mirrored argument is looked up at its upper grid neighbour."""
        am = mpf(a)
        return exp(-2 * am) * Ak_lookup(k, float(am)) + \
            exp(2 * am) * Ak_lookup(k, float(-am))

    # exact S_seed values at the binding frequencies
    seed_exact = {"%.2f" % float(a): float(abs(S_seed(mpf(a))))
                  for a in A_GRID[::10]}

    weights = []
    for z, v in active:
        Pzz = op.node_product(owner, z, z)
        weights.append((z, abs(v / (Pzz * SEED0)), abs(z.real - 0.5) / 2.0 + 0.0))

    report = {
        "record": 2031,
        "status": "PENDING",
        "rho": [RHO.real, RHO.imag],
        "N": N,
        "owner_model": "known-zero under-approximation (record 1980 rig)",
        "T_min": T_MIN,
        "q": Q,
        "seed0_exact": SEED0,
        "derivative_ladder": {str(k): None for k in range(K_MAX + 1)},
        "S_seed_exact_samples": seed_exact,
    }

    # exact/carried ladder and the sharp weighted masses at binding |a|
    a_bind = sorted({abs((s - z.real) / 2.0)
                     for s in (0.0, SIGMA_MAX) for z, _ in active})
    report["binding_abs_a"] = a_bind
    W_bind = {}
    for k in range(1, K_MAX + 1):
        W_bind[str(k)] = [float(Wk_lookup(k, a)) for a in a_bind]
    report["W_k_at_binding_a"] = W_bind

    rows = []
    best = None
    for k in range(1, K_MAX + 1):
        peak = None
        for sig in np.arange(0.0, SIGMA_MAX + 1e-9, 0.05):
            for t in np.arange(T_MIN, T_MAX + 1e-9, DT):
                tot = 0.0
                for z, cabs, _ in weights:
                    a = (float(sig) - z.real) / 2.0
                    y = (t - z.imag) / 2.0
                    if abs(y) < 1e-12:
                        continue
                    seedb = float(Wk_lookup(k, a)) / abs(complex(a, y)) ** k
                    P = abs(op.node_product(owner, z, complex(sig, t)))
                    tot += cabs * P * seedb ** 10
                if peak is None or tot > peak[0]:
                    peak = (tot, float(sig), float(t))
        rows.append({"k": k, "bound": peak[0], "sigma": peak[1], "t": peak[2],
                     "margin_vs_q": Q / peak[0]})
        if best is None or peak[0] < best["bound"]:
            best = {"k": k, "bound": peak[0], "sigma": peak[1], "t": peak[2]}
    report["ladder_bounds"] = rows
    report["best"] = best
    report["uses_weighted_mass"] = True

    # same bound with the record-1982 style crude mass e^{2|a|} D_k
    crude = []
    D = {1: 2.0, 2: 8.0, 3: 78.728338414649157642, 4: 1266.222834348598166234,
         5: 34570.60014415144764333, 6: 1377559.323149684683145}
    for k in range(1, K_MAX + 1):
        peak = 0.0
        at = None
        for sig in np.arange(0.0, SIGMA_MAX + 1e-9, 0.05):
            for t in np.arange(T_MIN, T_MAX + 1e-9, DT):
                tot = 0.0
                for z, cabs, _ in weights:
                    a = (float(sig) - z.real) / 2.0
                    y = (t - z.imag) / 2.0
                    if abs(y) < 1e-12:
                        continue
                    seedb = np.exp(2 * abs(a)) * D[k] / abs(complex(a, y)) ** k
                    P = abs(op.node_product(owner, z, complex(sig, t)))
                    tot += cabs * P * seedb ** 10
                if tot > peak:
                    peak, at = tot, (float(sig), float(t))
        crude.append({"k": k, "bound": peak, "sigma": at[0], "t": at[1],
                      "margin_vs_q": Q / peak})
    report["crude_mass_bounds_1982_style"] = crude

    # ---------------- uniformity verification -------------------------
    def bound_at(k, sig, t):
        tot = 0.0
        for z, cabs, _ in weights:
            a = (float(sig) - z.real) / 2.0
            y = (t - z.imag) / 2.0
            if abs(y) < 1e-12:
                continue
            sb = float(Wk_lookup(k, a)) / abs(complex(a, y)) ** k
            P = abs(op.node_product(owner, z, complex(sig, t)))
            tot += cabs * P * sb ** 10
        return tot

    fine_sigma = {}
    for k in range(1, K_MAX + 1):
        sweep = [(float(s), bound_at(k, s, T_MIN))
                 for s in np.arange(0.0, SIGMA_MAX + 1e-9, 0.01)]
        top = max(sweep, key=lambda r: r[1])
        fine_sigma[str(k)] = {"max": top[1], "sigma": top[0],
                              "margin_vs_q": Q / top[1]}
    report["fine_sigma_sweep_at_T"] = fine_sigma

    tail = {}
    for k in (2, 3):
        tail[str(k)] = [{"t": t, "bound": bound_at(k, 0.0, t),
                         "ratio_to_q": bound_at(k, 0.0, t) / Q}
                        for t in (T_MIN, 30.0, 40.0, 60.0, 100.0, 200.0, 400.0,
                                  800.0)]
    report["t_tail_check"] = tail

    out = ROOT / "results" / "2031_sharp_q_ladder.json"
    out.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({k: report[k] for k in
                      ("ladder_bounds", "best", "W_k_at_binding_a",
                       "binding_abs_a")}, indent=2))


if __name__ == "__main__":
    main()
