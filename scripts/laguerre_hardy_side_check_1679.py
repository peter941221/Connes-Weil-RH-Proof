#!/usr/bin/env python3
"""Laguerre obligation-1 self-consistency rig (record 1679).

The system under test (record 1679, transport chain T1-T2):

    chi_n(u) = e^{u/2} * exp(-(e^u - lambda)/2) * L_n(e^u - lambda),

the TRANSLATED Laguerre functions on (lambda, inf) pulled back by the log
map — claimed to be a complete orthonormal system of
L^2((log lambda, inf), du).  F61-permitted reading: this rig lives
entirely INSIDE the fixed ansatz family (no meet, no grid-forcing issue).
It guards transcription of the transport chain only; the evidence for
obligation 1 is the paper record.  (First-run erratum: the pure log
pull-back without the lambda-translation is an ONB of the FULL line, and
the rig correctly read max|G - I| = 1.8e+01 for it.)

Checks:
  (a) Gram matrix of {chi_n}_{n<10} == I  (orthonormality, du quadrature).
  (b) Residual trend: relative L2 residual of test vectors projected onto
      the first K sections (completeness trend toward the quadrature
      floor).
"""

import json

import numpy as np
from scipy.special import eval_laguerre

A = 1.0                 # lambda = e^-1, log lambda = -a = -1
LAM = float(np.exp(-A))
L_DOMAIN = 40.0
M_GRID = 16384
DU = (L_DOMAIN - A) / M_GRID


def chi(n, u):
    """chi_n(u) = e^{u/2} phi_n(e^u - lambda) on the half-line u >= -a.

    Masked at y = e^u - lambda > 400: there e^{-y/2} has underflowed and
    the value is exactly 0 in float64; evaluating eval_laguerre at huge y
    overflows to inf/nan instead."""
    y = np.exp(u) - LAM
    out = np.zeros_like(u)
    m = y < 400.0
    out[m] = (np.exp(0.5 * u[m]) * np.exp(-0.5 * y[m])
              * eval_laguerre(n, y[m]))
    return out


def main():
    u = -A + DU * np.arange(1, M_GRID + 1)   # strictly inside the half-line

    # (a) Gram matrix
    N = 30
    V = np.vstack([chi(n, u) for n in range(N)])
    G = DU * (V @ V.T)
    err_orth = float(np.max(np.abs(G - np.eye(N))))
    print(f"[gram] max|G - I| = {err_orth:.3e}")

    # (b) completeness trend: smooth bump AWAY from the span of {chi_n}_{n<N}
    u0, w = 2.0, 1.0
    v = np.exp(-((u - u0) / w) ** 2)
    v /= np.sqrt(DU * float(np.sum(v ** 2)))
    res = []
    for K in [4, 8, 12, 20, 30]:
        c = DU * (V[:K] @ v)
        r = v - V[:K].T @ c
        res.append((K, float(np.sqrt(DU * np.sum(r ** 2)))))
    print("[residual trend]", ", ".join(f"K={k}: {r:.3e}" for k, r in res))

    out = {"lambda": float(np.exp(-A)), "a": A, "du": DU,
           "gram_max_err": err_orth,
           "residual_trend": [{"K": k, "rel_residual": r} for k, r in res]}
    with open("laguerre_hardy_side_1679_results.json", "w") as fh:
        json.dump(out, fh, indent=1)
    print("[done] results written to laguerre_hardy_side_1679_results.json")


if __name__ == "__main__":
    main()
