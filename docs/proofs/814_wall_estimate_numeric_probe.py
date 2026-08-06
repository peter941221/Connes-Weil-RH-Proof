#!/usr/bin/env python3
"""Numeric probe of the transport-radial wall operator (Proof 717 / Gate 3U).

Math (see 814_wall_estimate_math_design.md):
    R     = projection onto support in [logla, oo)   (radial / Sonin)
    S     = I - R                                    (keeps t < logla)
    T     = prod_p (I - p^(-1/2) U_{logp})           (finite Euler transport)
    Tdag  = prod_p (I - p^(-1/2) U_{-logp})          (adjoint: shift LEFT)
    W     = S . Tdag . R  = (I-R) . Tdag . R         (the open metric wall)

Tdag drags radial mass from just above logla down below it; S keeps exactly that
strip.  This probe answers the 814 question numerically: does the leak ||W e_k||
square-squeeze (decaying series) on a decayed prolate-like radial basis e_k, or
does the uniform operator norm ||W|| stay above 1 for arbitrary radial input?

Run:  python3 814_wall_estimate_numeric_probe.py
"""

from __future__ import annotations

import numpy as np


def build_W_real(primes, logla, n):
    """Finite-section of W = (I-R) Tdag R on uniform grid [-L, L], n points.

    One prime factor: (I - p^-1/2 U_{-logp}) f(t) = f(t) - p^-1/2 f(t + logp),
    implemented as index shift sh = round(logp / dt).  R keeps t_i >= logla.
    """
    L = 10.0
    t = np.linspace(-L, L, n)
    dt = t[1] - t[0]
    R = np.zeros((n, n))
    for i in range(n):
        if t[i] >= logla - 1e-12:
            R[i, i] = 1.0
    Tdag = np.eye(n)
    for p in primes:
        logp = float(np.log(p))
        sh = int(round(logp / dt))
        Sf = np.eye(n)                       # single-prime factor I - p^-1/2 shift
        for i in range(n):
            j = i + sh                       # value f(t_i + logp)
            if 0 <= j < n:
                Sf[i, j] -= p ** -0.5
        Tdag = Sf @ Tdag
    W = (np.eye(n) - R) @ Tdag @ R
    return t, W


def radial_carrier(t, logla, k):
    """Normalized radial probe e_k: Gaussian centred at logla + small offset,
    width shrinking with k (Sonin/prolate near-edge squeeze)."""
    width = 0.5 / (k + 1.0) + 0.05
    e = np.exp(-((t - (logla + 0.25)) ** 2) / (2.0 * width * width))
    e = e * (t >= logla).astype(float)       # radial: supported on t >= logla
    nrm = np.sqrt(np.sum(e * e))
    return e / nrm if nrm > 0 else e


def main() -> None:
    primes_lists = [[2], [2, 3], [2, 3, 5]]
    logla_values = [0.0, 1.0]
    n = 1024
    n_basis = 6

    print("=== flat operator norm ||W|| = sigma_max((I-R) Tdag R) ===")
    for logla in logla_values:
        for primes in primes_lists:
            t, W = build_W_real(primes, logla, n)
            s = np.linalg.svd(W, compute_uv=False)
            print(f"  logla={logla}  primes={primes}:  ||W|| = {s[0]:.5f}")

    print("\n=== decay of ||W e_k|| on decayed radial carriers (k = 0..%d) ===" % (n_basis - 1))
    for logla in logla_values:
        for primes in primes_lists:
            t, W = build_W_real(primes, logla, n)
            leaks = []
            for k in range(n_basis):
                e = radial_carrier(t, logla, k)
                leaks.append(float(np.linalg.norm(W @ e)))
            print(f"  logla={logla}  primes={primes}:  "
                  + " ".join("%.4f" % v for v in leaks))


if __name__ == "__main__":
    main()