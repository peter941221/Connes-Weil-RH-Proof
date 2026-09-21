#!/usr/bin/env python3
# tail_window_1801b.py — record 1801b surrogate diagnostic (withdrawn as a route screen)
#
# Record 1802 established that this script's Cartwright/Riemann--von Mangoldt
# cap is NOT a constraint of the committed OrbitG8Geometry constructor. Do
# not use an EMPTY verdict here to reject tailStart, an owner, or the B5
# route. The constructor selects tailStart first and then supplies arbitrary
# finite ball-zero data. This file is retained only to reproduce the stated
# surrogate-family diagnostic from record 1801.
#
# The 1801 rig measured the gate quadratic form on the geometry-preserving
# family (indefinite; G_BB sign = prime-face sign).  This addendum measures
# a surrogate family's tail profile under an additional, uncommitted
# Cartwright capacity heuristic:
#
#   floor(tS)  : zero_height_le_dyadic   2|Im rho| <= 2^(tS+1)
#   cap(tS)    : square_zero_control demands L[g^2] = 0 at all zeros in the
#                ball |z - rho| <= 2^(tS+1) + 2 + dist(2, rho).  L[g^2] is
#                Cartwright class (type a = supp radius, bounded on iR), so
#                its zero budget is n(r) <= (2a/pi) r (Levin, Lect. 9).
#                Demanded zeros ~ (2 R / pi) log((gamma+R)/2pi) by RVM.
#                Satisfiable only if  2^(tS+1) <~ 2 pi e^a - gamma - O(1).
#   budget(tS) : tail_budget_below_multiplicity
#                4 eps^2 C_mult (3/4)^tS < mult(rho)   (mult = 1, C_mult ~ 277)
#                =>  eps^2(tS) = (4/3)^tS / (4 C_mult)
#   tail(tS)   : FourthOrderSpectralTail with T = 2^(tS+1) needs
#                sup_{tau >= max(T, 2 gamma)} tau^4 |L[g^2](sigma+i tau)| < eps^2(tS)
#                (the dist-products are ~ tau^2 tau^2 on the strip).
#
# Measured here directly from the constructed owner profile F = g*⋆g:
#   - support radius a of F,
#   - S(T) := sup over sigma in {-0.5, 0, 0.5}, tau >= T of tau^4 |L[F](sigma+i tau)|
#     (tau grid: log-spaced, direct +s quadrature),
#   - the verdict: exists tS (integer) with floor <= tS <= cap and S(2^(tS+1)) < eps^2(tS).
#
# Everything is a measurement of the committed definitions; the Cartwright
# cap is paper-grade (cited) and reported alongside the measured support.

import json
import math
import os
import time

import numpy as np

T0 = time.time()


def log(msg):
    print("[%7.1fs] %s" % (time.time() - T0, msg), flush=True)


LX = 8.0
DU = 5.0e-4
N = int(round(2 * LX / DU)) + 1
XG = -LX + np.arange(N) * DU
NF = 131072
# C_mult = (xiGrowthFixedConstant + 1 + |log ||Xi(2)||| + 192)/log 2
# (C1SpectralSummability.lean:303); the +192 dominates, the other terms are
# O(1).  Numerically: C_MULT ~ 278.
C_MULT = (0.0 + 1.0 + abs(math.log(math.sqrt(2.0 * math.pi))) + 192.0) / math.log(2.0)
TAU_MAX = math.pi / DU * 0.999   # Nyquist limit of the quadrature grid


def bump(c, center=0.0):
    f = np.zeros_like(XG)
    m = np.abs(XG - center) < c
    xm = (XG[m] - center) / c
    f[m] = np.exp(-1.0 / (1.0 - xm * xm))
    return f


def l2_normalize(f):
    return f / math.sqrt(DU * float(np.sum(np.abs(f) ** 2)))


def conv_off(a, b):
    ca = a if np.iscomplexobj(a) else a.astype(complex)
    cb = b if np.iscomplexobj(b) else b.astype(complex)
    full = DU * np.fft.ifft(np.fft.fft(ca, NF) * np.fft.fft(cb, NF))
    off = (N - 1) // 2
    return full[off: off + N]


def build_owner(beta, gamma, cb, k):
    """The 1799 pinned owner (same construction, engines validated)."""
    wb = cb / gamma
    mu = np.array([-0.45, -0.15, 0.15, 0.45])
    Amat = np.array([[math.exp(m * s) for m in mu] for s in (0.5, 1.0, 1.5)])
    cvec = np.linalg.svd(Amat)[2][-1]
    base = sum(cvec[j] * bump(wb, mu[j]) for j in range(4))
    base = base / math.sqrt(DU * float(np.sum(base ** 2)))

    def lap(f, s):
        return DU * complex(np.sum(f * np.exp(s * XG)))

    nodes = [complex(beta, gamma), complex(1.0 - beta, gamma),
             complex(beta, -gamma), complex(1.0 - beta, -gamma),
             complex(beta + 0.5, gamma)]
    targets = [1.0, -1.0, 0.0, 0.0, -1.0]
    bhk = [lap(base, s) ** k for s in nodes]
    mod = np.exp(-1j * gamma * XG)
    basis = [l2_normalize(bump(w, c)) * mod
             for (w, c) in [(0.35, -0.2), (0.35, 0.2), (0.5, 0.0)]] \
          + [l2_normalize(bump(w, c)) / mod
             for (w, c) in [(0.3, -0.15), (0.3, 0.15)]]
    M = np.array([[lap(ph, s) for ph in basis] for s in nodes])
    rhs = np.array([t / b for t, b in zip(targets, bhk)])
    al = np.linalg.solve(M, rhs)
    corr = sum(al[j] * basis[j] for j in range(5))
    T = corr
    for _ in range(k):
        T = conv_off(base, T)
    A = np.exp(XG / 2.0) * T
    F = conv_off(np.conj(A[::-1]), A)
    return A, F, wb


def support_radius(F):
    m = np.max(np.abs(F))
    idx = np.where(np.abs(F) > 1e-13 * m)[0]
    return float(max(abs(XG[idx[0]]), abs(XG[idx[-1]])))


def tail_sup(F, T_lo, sigmas=(-0.5, 0.0, 0.5)):
    """S(T) = sup_{sigma, tau >= T} tau^4 |L[F](sigma + i tau)|.

    Direct +s quadrature on the grid; tau log-spaced in [T, TAU_MAX]
    (the grid Nyquist limit).  Returns (S, arg, truncated)."""
    lo = max(T_lo, 1.0)
    if lo >= TAU_MAX:
        return None, None, True
    taus = np.geomspace(lo, TAU_MAX, 400)
    best = 0.0
    arg_best = None
    for sg in sigmas:
        w = F * np.exp(sg * XG)
        for tau in taus:
            v = abs(DU * complex(np.sum(w * np.exp(1j * tau * XG))))
            s = tau ** 4 * v
            if s > best:
                best = s
                arg_best = (sg, float(tau))
    return best, arg_best, False


def main():
    log("record 1801b — tailStart window measurement (C_mult=%.1f)" % C_MULT)
    out = []
    for beta in (0.55, 0.6):
        for gamma in (14.13472514173497, 40.0):
            for (cb, k) in ((0.6, 1), (1.2, 2)):
                tag = "b%.2f g%4.1f cb%.1f k%d" % (beta, gamma, cb, k)
                _, F, _ = build_owner(beta, gamma, cb, k)
                a = support_radius(F)
                # floor: 2 gamma <= 2^(tS+1)
                tS_floor = int(math.ceil(math.log2(2.0 * gamma) - 1.0 - 1e-12))
                # cap (paper, Cartwright): 2^(tS+1) <= 2 pi e^a - gamma - 2 - dist(2, rho)
                dist2rho = abs(complex(2.0, 0.0) - complex(beta, gamma))
                cap_val = 2.0 * math.pi * math.exp(a) - gamma - 2.0 - dist2rho
                tS_cap = int(math.floor(math.log2(cap_val) - 1.0)) if cap_val > 0 else -99
                rows = []
                verdict = "EMPTY"
                for tS in range(max(tS_floor, 0), tS_cap + 1):
                    T = 2.0 ** (tS + 1)
                    eps2 = (4.0 / 3.0) ** tS / (4.0 * C_MULT)
                    S, arg, trunc = tail_sup(F, max(T, 2.0 * gamma))
                    if trunc:
                        log("%s tS=%d T=%8.0f beyond instrument (tau>T>"
                            "Nyquist %.0f)" % (tag, tS, T, TAU_MAX))
                        rows.append({"tS": tS, "T": T, "eps2": eps2,
                                     "S": None, "arg": None, "ok": None})
                        continue
                    ok = S < eps2
                    rows.append({"tS": tS, "T": T, "eps2": eps2,
                                 "S": S, "arg": arg, "ok": bool(ok)})
                    log("%s tS=%d T=%8.0f eps2=%.3e S=%.3e %s"
                        % (tag, tS, T, eps2, S, "OK" if ok else "fail"))
                    if ok:
                        verdict = "NONEMPTY at tS=%d" % tS
                if tS_cap < tS_floor:
                    verdict = "EMPTY (cap %d < floor %d)" % (tS_cap, tS_floor)
                log("%s | a=%.3f floor=%d cap=%d -> %s"
                    % (tag, a, tS_floor, tS_cap, verdict))
                out.append({"tag": tag, "a": a, "floor": tS_floor,
                            "cap": tS_cap, "cap_val": cap_val,
                            "verdict": verdict, "rows": rows})
    os.makedirs("results", exist_ok=True)
    with open("results/1801b_tail_window.json", "w") as fh:
        json.dump({"record": "1801b", "C_mult": C_MULT, "cases": out}, fh,
                  indent=1, default=float)
    log("results → results/1801b_tail_window.json")


if __name__ == "__main__":
    main()
