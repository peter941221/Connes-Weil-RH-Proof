#!/usr/bin/env python3
"""Small well-conditioned probe of D = (T^+ T) . J . GramInv and its channels.

Validates the finite construction against the PROVEN identity
J^+ . D = id  (Lean: sourceInclusionAdjoint_comp_metricCoframe, CoframeResponse:53).
Only if that holds (||J^+ D|| ~ 1) do we trust the outer-channel number.

map:  A = T . J  (n-carrier columns) ;  G = A^+ A  ;  dual = A . G^-1
      D = T^+ . dual  =  T^+ . A . G^-1        (metric coframe, CoframeResponse:43)
Run: python3 815_outer_channel_small_probe.py
"""
from __future__ import annotations
import numpy as np


def shift_op(p, dt, n, sign):
    logp = float(np.log(p)); sh = int(round(logp / dt))
    S = np.eye(n)
    for i in range(n):
        j = i + sign * sh
        if 0 <= j < n:
            S[i, j] -= p ** -0.5
    return S


def mk_T(primes, t):
    n = len(t); dt = t[1] - t[0]; T = np.eye(n)
    for p in primes:
        T = shift_op(p, dt, n, +1) @ T
    return T


def mk_Tdag(primes, t):
    n = len(t); dt = t[1] - t[0]; T = np.eye(n)
    for p in primes:
        T = shift_op(p, dt, n, -1) @ T
    return T


def main():
    primes_lists = [[2], [2, 3], [2, 3, 5]]
    for logla in [0.0, 1.0]:
        for pr in primes_lists:
            # small grid for well-conditioning
            L = 3.0; n = 60
            t = np.linspace(-L, L, n); dt = t[1]-t[0]
            car = np.where(t >= logla - 1e-12)[0]
            under = np.where(t < logla - 1e-12)[0]
            T = mk_T(pr, t); Td = mk_Tdag(pr, t)
            A = T[:, car]                    # T . J : n x car
            G = A.conj().T @ A
            # well-conditioned threshold
            u, s, vt = np.linalg.svd(G)
            keep = s > 1e-8 * np.max(s) if s.size else s > 0
            s_inv = np.where(keep, 1.0/s, 0.0)
            Ginv = vt.T @ np.diag(s_inv) @ u.conj().T
            dual = A @ Ginv                    # dual frame (n x car)
            D = Td @ dual                      # metric coframe T^+.dual (n x car)
            JD = D[car, :]                     # J^+ D (compression to carrier)
            sJ = np.linalg.norm(JD, 2)
            outer = D[under, :]                # (I - R) D = radial complement rows
            so = np.linalg.norm(outer, 2)
            condG = s[0] / (s[-1] if s[-1] > 0 else 1.0) if s.size else float('nan')
            print(f"logla={logla} pr={pr} car={len(car)} condG={condG:.1e} "
                  f"fidelity||J+D||={sJ:.4f}  ||(I-R)D||={so:.4f}")


if __name__ == "__main__":
    main()