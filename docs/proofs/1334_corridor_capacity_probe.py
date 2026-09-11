#!/usr/bin/env python3
"""Record 1334 - kernel confirmation + corridor capacity probe (official run).

Implements EXACTLY docs/proofs/1334_carrier_kernel_confirmation_and_corridor_
capacity_preregistration.md (committed before this run). MODEL-twin numerics
only; no claim about the formal ran P_S or hcolumn.

S1: cliff count c = #{sigma < 1e-6} vs winding |W(L)| (ratio band [0.95,1.05]).
S2: corridor capacity of the near-kernel sector:
    A_tau = (1/r) sum_k (2 + 2 cos(2 pi tau xi_k)) K_eps(xi_k) h,
    tau = log p, p in {2,3,5,7,11}; decisive cell L=48, N=8192.
Gates G0 (identity sigma_min via ||T-I||), G1 (K_full exactness + trace),
G2 (sharp cliff); breach => ABORTED-UNINFORMATIVE exit 1.  DONE 1334
sentinel + JSON only (1329 lesson: never judge by exit code alone).
"""
import json
import math
import sys
import time

import numpy as np
from scipy.special import loggamma

N = 8192
D = N // 2
LS = [32, 48, 64]
PRIMES = [2, 3, 5, 7, 11]
TAUS = [math.log(p) for p in PRIMES]
EPS = 1e-6
BUDGET_S = 580.0


def log_gamma_r(s):
    return -(s / 2) * math.log(math.pi) + loggamma(s / 2) + loggamma((s + 1) / 2)


def arg_phase(x):
    return -2 * np.imag(log_gamma_r(0.5 + 2j * math.pi * np.asarray(x)))


def scattering_phase(x):
    return np.exp(1j * arg_phase(x))


def winding_cycles(L):
    xs = np.linspace(-L, L, 200001)
    a = np.unwrap(arg_phase(xs))
    return (a[-1] - a[0]) / (2 * math.pi)


def basis_matrix(L):
    """E[k, m-1] = e_m(xi_k), the trig ONB of the trial space on the grid."""
    m = np.arange(1, D + 1)
    return np.exp(2j * math.pi * np.outer(np.arange(N), m) / N) * (
        np.where(m % 2 == 0, 1.0, -1.0))[None, :] / math.sqrt(2 * L)


def toeplitz_matrix(phi, L):
    j = np.arange(N)
    m = np.arange(1, D + 1)
    Em = np.exp(2j * math.pi * np.outer(m, j) / N) * (
        np.where(m % 2 == 0, 1.0, -1.0))[:, None] / math.sqrt(2 * L)
    Gd = np.fft.fft(Em * phi[None, :], axis=1) / N
    return (math.sqrt(2 * L) * Gd[:, 1:D + 1]).T


def main():
    t0 = time.time()
    out = {"record": 1334, "N": N, "primes": PRIMES, "gates": {}, "cells": {},
           "verdict": {"KERNEL": None, "CAPACITY": None}}
    # ---- G0 identity control at decisive cell (48, 8192) ----
    # phi=1 gives T = diag((-1)^m) in this basis (unit-modulus diagonal, not
    # the literal identity: the grid-center convention carries (-1)^m phases).
    # Witness: off-diagonal max < 1e-12 and min |diag| >= 1 - 1e-10, which
    # implies the preregistered sigma_min >= 1 - 1e-10 (a unitary diagonal).
    Lg = 48
    T1 = toeplitz_matrix(np.ones(N), Lg)
    off = np.abs(T1 - np.diag(np.diag(T1)))
    g0 = float(max(off.max(), 1.0 - np.abs(np.diag(T1)).min()))
    out["gates"]["G0_identity_offdiag_and_diag"] = g0
    print(f"G0 offdiag+|diag|dev = {g0:.2e} (need < 1e-10)", flush=True)
    del T1
    if g0 >= 1e-10:
        out["verdict"] = "ABORTED-UNINFORMATIVE"
        json.dump(out, open("1334_probe_results.json", "w"), indent=1)
        print("ABORTED-UNINFORMATIVE: G0", flush=True)
        sys.exit(1)
    # ---- main cells ----
    for L in LS:
        t1 = time.time()
        h = 2 * L / N
        xs = (np.arange(N) - D) * h
        phi = scattering_phase(xs)
        T = toeplitz_matrix(phi, L)
        U, s, Vh = np.linalg.svd(T, full_matrices=False)
        del T, U, phi
        r = int(np.sum(s < EPS))
        wl = winding_cycles(L)
        # s is DESCENDING: the r floor values are s[D-r..D-1]; the cliff is
        # between s[D-r-1] (first above floor) and s[D-r] (largest floor one).
        cell = {"winding": wl, "rank_eps": r, "ratio": r / abs(wl),
                "sigma_at_r": float(s[D - r]),
                "sigma_at_r1": float(s[D - r - 1]) if r < D else None,
                "cliff_gap": (float(s[D - r - 1] / s[D - r])
                              if 0 < r < D else None)}
        # G1: full diagonal exactness + sector trace (K carries one factor h)
        Eb = basis_matrix(L)
        Kfull = np.sum(np.abs(Eb) ** 2, axis=1) * h
        cell["G1_kfull_max_err"] = float(
            np.max(np.abs(Kfull - D * h / (2 * L))))
        V = Vh.conj().T[:, :r]
        del Vh
        K = np.sum(np.abs(Eb @ V) ** 2, axis=1) * h
        cell["trace_dev"] = abs(float(K.sum()) - r) / r
        # S2: corridor energies
        A = {}
        for p, tau in zip(PRIMES, TAUS):
            A[f"log{p}"] = float(np.sum((2 + 2 * np.cos(
                2 * math.pi * tau * xs)) * K) / r)
        cell.update({"A_tau": A, "A_max": max(A.values()),
                     "A_min": min(A.values()),
                     "k_max_over_mean": float(K.max() / (r / (2 * L))),
                     "secs": round(time.time() - t1, 1)})
        out["cells"][f"L{L}"] = cell
        cg = "inf" if cell["cliff_gap"] is None else f"{cell['cliff_gap']:.2e}"
        print(f"CELL L={L}: r={r} wind={wl:.1f} R1={cell['ratio']:.4f} "
              f"cliff_gap={cg} A=[{cell['A_min']:.3f},{cell['A_max']:.3f}] "
              f"G1err={cell['G1_kfull_max_err']:.1e} "
              f"trdev={cell['trace_dev']:.1e} ({cell['secs']}s)", flush=True)
        if cell["secs"] > BUDGET_S:
            print(f"WARN budget breach L={L}", flush=True)
        del Eb, V, K, s, xs
    # ---- G1/G2 gate + verdicts ----
    ok = all(c["G1_kfull_max_err"] < 1e-10 and c["trace_dev"] < 1e-8
             and (c["cliff_gap"] is None or c["cliff_gap"] > 10)
             for c in out["cells"].values())
    out["gates"]["G1_G2_all"] = bool(ok)
    if not ok:
        out["verdict"] = "ABORTED-UNINFORMATIVE"
        json.dump(out, open("1334_probe_results.json", "w"), indent=1)
        print("ABORTED-UNINFORMATIVE: G1/G2", flush=True)
        sys.exit(1)
    Rs = [out["cells"][f"L{L}"]["ratio"] for L in LS]
    out["verdict"]["KERNEL"] = (
        "CONFIRMED" if all(0.95 <= R <= 1.05 for R in Rs)
        else "NOT-CONFIRMED" if any(R < 0.90 or R > 1.10 for R in Rs)
        else "INCONCLUSIVE")
    dc = out["cells"]["L48"]
    out["verdict"]["CAPACITY"] = (
        "CONCENTRATES" if dc["A_max"] <= 0.30
        else "FALSIFIES" if dc["A_min"] >= 1.20
        else "INCONCLUSIVE")
    out["total_secs"] = round(time.time() - t0, 1)
    json.dump(out, open("1334_probe_results.json", "w"), indent=1)
    print("VERDICT", out["verdict"], flush=True)
    print("DONE 1334", flush=True)


if __name__ == "__main__":
    main()
