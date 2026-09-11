#!/usr/bin/env python3
"""Record 1332 - carrier nontriviality probe (official run).

Implements EXACTLY the preregistration committed at f349fbb in
docs/proofs/1332_carrier_nontriviality_and_corridor_capacity_preregistration.md
including Amendment A1 (C1 = identity witness, sigma_min >= 1-1e-10).
MODEL-twin numerics only: makes no claim about the formal ran P_S or the
Lean premise hcolumn.

Statistic: singular values of the discrete Toeplitz-type operator
    T_N : (span of positive grid modes 1..N/2) -> same space,
    T w = P_+ (phi * w),   ker T  ~  W  = { w in H^2(C+) : phi w in H^2(C-) }.
Bounded-below sigma_min => W trivial-consistent; sigma_min -> 0 => nontrivial
candidates.

Registered readouts per cell: sorted singular values, sigma_min, counts below
1e-6 / 1e-4 / 1e-2.  Controls C1 phi=1 (identity), C2 unit +shift (one edge
zero, rest 1), C3/C4 exp(+-0.1 i sin) (sigma_min >= 0.5).  Control breach =>
ABORTED-UNINFORMATIVE exit 1.  Verdict rule per prereg section 4 applied to
main cells L in {32,64} x N in {512,1024,2048,4096} only when all controls
pass.  Completion = printed 'DONE 1332' sentinel + JSON (1329 lesson: never
judge by exit code alone).
"""
import json
import math
import sys
import time

import numpy as np
from scipy.special import loggamma

PRIMES = [2, 3, 5, 7, 11]
LS = [32, 64]
NS = [512, 1024, 2048, 4096]
TOL_ID = 1e-10
TOL_C34 = 0.5
BUDGET_S = 580.0


def scattering_phase(x):
    """phi(x) = Gamma_R(1/2-2pi i x)/Gamma_R(1/2+2pi i x), |phi| = 1.

    With s = 1/2 + 2 pi i x and logGamma_R(s) = -(s/2) log pi
    + loggamma(s/2) + loggamma((s+1)/2) (all Re > 0, principal branch),
    phi = exp(-2 i Im logGamma_R(s))."""
    s = 0.5 + 2j * math.pi * x
    lg = -(s / 2) * math.log(math.pi) + loggamma(s / 2) + loggamma((s + 1) / 2)
    return np.exp(-2j * np.imag(lg))


def symbol(kind, x, L):
    if kind == "gamma":
        return scattering_phase(x)
    if kind == "one":
        return np.ones_like(x)
    if kind == "shift":
        return np.exp(2j * math.pi * x / (2 * L))
    if kind == "hs_plus":
        return np.exp(0.1j * np.sin(2 * math.pi * x))
    if kind == "hs_minus":
        return np.exp(-0.1j * np.sin(2 * math.pi * x))
    raise ValueError(kind)


def toeplitz_matrix(kind, L, N):
    """T[i, m] = sqrt(2L)/N * fft(phi * e_{m+1})_{i+1} on the periodic grid."""
    h = 2 * L / N
    x = (np.arange(N) - N // 2) * h
    phi = symbol(kind, x, L)
    d = N // 2
    j = np.arange(N)
    m = np.arange(1, d + 1)
    # e_m(x_j) = (-1)^m exp(2 pi i m j / N) / sqrt(2L)
    Em = np.exp(2j * math.pi * np.outer(m, j) / N) * (
        np.where(m % 2 == 0, 1.0, -1.0))[:, None] / math.sqrt(2 * L)
    G = Em * phi[None, :]
    Gd = np.fft.fft(G, axis=1) / N
    return (math.sqrt(2 * L) * Gd[:, 1:d + 1]).T


def sv_readout(sig_sorted):
    return {
        "sigma_min": float(sig_sorted[-1]),
        "count_lt_1e-6": int(np.sum(sig_sorted < 1e-6)),
        "count_lt_1e-4": int(np.sum(sig_sorted < 1e-4)),
        "count_lt_1e-2": int(np.sum(sig_sorted < 1e-2)),
        "sigma_first8": [float(v) for v in sig_sorted[:8]],
        "sigma_last8": [float(v) for v in sig_sorted[-8:]],
    }


def main():
    t0 = time.time()
    out = {"record": 1332, "controls": {}, "main": {}, "gates": {},
           "verdict": None, "params": {"LS": LS, "NS": NS, "PRIMES": PRIMES}}
    # ---- controls (A1) ----
    Lc, Nc = 64, 4096
    for kind, gate in (("one", "id"), ("shift", "edge"),
                       ("hs_plus", "hs"), ("hs_minus", "hs")):
        t1 = time.time()
        T = toeplitz_matrix(kind, Lc, Nc)
        sv = np.sort(np.linalg.svd(T, compute_uv=False))[::-1]
        r = sv_readout(sv)
        ok = True
        if gate == "id":
            ok = r["sigma_min"] >= 1 - TOL_ID
        elif gate == "edge":
            small = np.sum(sv < TOL_ID)
            ok = small == 1 and float(np.sort(sv)[1]) >= 1 - TOL_ID
        else:
            ok = r["sigma_min"] >= TOL_C34
        r["gate_pass"] = bool(ok)
        r["secs"] = round(time.time() - t1, 1)
        out["controls"][kind] = r
        print(f"CTRL {kind}: sigma_min={r['sigma_min']:.3e} pass={ok} "
              f"({r['secs']}s)", flush=True)
    if not all(c["gate_pass"] for c in out["controls"].values()):
        out["verdict"] = "ABORTED-UNINFORMATIVE"
        json.dump(out, open("1332_probe_results.json", "w"), indent=1)
        print("ABORTED-UNINFORMATIVE: control gate breach", flush=True)
        sys.exit(1)
    # ---- main cells ----
    for L in LS:
        for N in NS:
            t1 = time.time()
            T = toeplitz_matrix("gamma", L, N)
            sv = np.sort(np.linalg.svd(T, compute_uv=False))[::-1]
            r = sv_readout(sv)
            r["secs"] = round(time.time() - t1, 1)
            r["max_norm_err"] = float(np.max(np.abs(
                symbol("gamma", (np.arange(N) - N // 2) * (2 * L / N), L)
            )) - 1.0)
            out["main"][f"L{L}_N{N}"] = r
            print(f"CELL L={L} N={N}: sigma_min={r['sigma_min']:.3e} "
                  f"n<1e-4={r['count_lt_1e-4']} n<1e-2={r['count_lt_1e-2']} "
                  f"({r['secs']}s)", flush=True)
            if time.time() - t1 > BUDGET_S:
                print(f"WARN budget breach cell L{L} N{N}", flush=True)
    # ---- registered verdict rule ----
    big = out["main"]["L64_N4096"]["sigma_min"] < 1e-4
    mono = (out["main"]["L64_N4096"]["sigma_min"]
            < 0.5 * out["main"]["L64_N2048"]["sigma_min"])
    extra = sum(1 for v in out["main"].values() if v["sigma_min"] < 1e-4) >= 2
    if big and mono and extra:
        out["verdict"] = "NONTRIVIAL-LIKELY"
    else:
        triv = all(v["sigma_min"] >= 1e-2 for k, v in out["main"].items()
                   if int(k.split("_N")[1]) >= 2048)
        out["verdict"] = "TRIVIAL-LIKELY" if triv else "INCONCLUSIVE"
    out["total_secs"] = round(time.time() - t0, 1)
    json.dump(out, open("1332_probe_results.json", "w"), indent=1)
    print(f"VERDICT {out['verdict']}", flush=True)
    print("DONE 1332", flush=True)


if __name__ == "__main__":
    main()
