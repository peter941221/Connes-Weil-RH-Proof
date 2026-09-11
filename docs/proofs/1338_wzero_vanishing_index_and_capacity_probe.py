#!/usr/bin/env python3
"""Record 1338 - M1-prime: W_zero index cancellation + corridor capacity.

Implements EXACTLY docs/proofs/1338_wzero_index_cancellation_and_capacity_
preregistration.md (committed before this run). MODEL-twin numerics only;
no claim about the formal carrier, no vanishing, no RH statement.

Cells: flavor in {LC, LR} x L in {32, 48, 64}, N=8192 official.
  LC = the committed 1332-1334 two-gamma phase (continuity);
  LR = single-Gamma_R flavor (1337 section 6: winding ~ 2N, thinning possible).
S1: rank(E) of ±xi_n point-vanishing functionals on the near-kernel sector,
    survivor r' = r - rankE, f = r'/r vs floor f0 = 1 - 2M/r, tolerance pair
    {1e-8, 1e-6} (G3 sharpness).
S2: 1334 corridor capacity statistic A_tau recomputed on the constrained
    sector Vc = V @ null(E).
Gates G0-G6 preregistered; breach => exit 1 ABORTED-UNINFORMATIVE.
Completion judged ONLY by the "DONE 1338" sentinel (1329 law).
"""
import json
import math
import os
import sys
import time

import numpy as np
from scipy.special import loggamma

N = int(os.environ.get("P_N", 8192))
D = N // 2
LS = [32, 48, 64]
FLAVORS = ["LC", "LR"]
PRIMES = [2, 3, 5, 7, 11]
TAUS = [math.log(p) for p in PRIMES]
EPS = 1e-6
MARGIN = 3.0
TOL_RANKS = [1e-8, 1e-6]
BUDGET_S = 580.0
OUT = os.environ.get("P_OUT", "1338_probe_results.json")
# Amendment inv6: P_SMOKE=1 downgrades ONLY the resolution-limited gates
# G2 (cliff) and G3 (soft rank) to WARN (1334 precedent: both are sharp at
# N=8192, soft at 1024). Machinery gates G0/G1/G4/G5/G7 stay ABORT.
# Official runs never set P_SMOKE; there the gates abort as preregistered.
SMOKE = os.environ.get("P_SMOKE") == "1"

# Anchors for G5: verified by residual gate |zeta(1/2+i gamma)| <= 1e-3
# plus the table below (the ORIGINAL hand-typed table here contained three
# fabricated values, caught by the pre-run smoke; replaced by values
# produced by mpmath zetazero and independently verified against zeta
# residuals this session — lesson: never hand-type published constants).
FIRST10 = [14.134725, 21.022040, 25.010858, 30.424876, 32.935062,
           37.586178, 40.918719, 43.327073, 48.005151, 49.773832]
# 1334 continuity targets (N=8192 only): rank cliff counts per L.
LC_R_TARGET = {32: 387, 48: 658, 64: 952}


def log_gamma_lc(s):
    return -(s / 2) * math.log(math.pi) + loggamma(s / 2) + loggamma((s + 1) / 2)


def log_gamma_lr(s):
    return -(s / 2) * math.log(math.pi) + loggamma(s / 2)


def arg_phase(xs, flavor):
    lg = log_gamma_lc if flavor == "LC" else log_gamma_lr
    return -2 * np.imag(lg(0.5 + 2j * math.pi * np.asarray(xs)))


def winding_cycles(L, flavor):
    xs = np.linspace(-L, L, 200001)
    a = np.unwrap(arg_phase(xs, flavor))
    return (a[-1] - a[0]) / (2 * math.pi)


def basis_matrix(L):
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


def eval_trig_rows(points, L):
    """P1: evec rows (E[2M, D]); e_m(x) = (-1)^m exp(2 pi i m (x+L)/(2L))/sqrt(2L)."""
    m = np.arange(1, D + 1)
    ph = np.where(m % 2 == 0, 1.0, -1.0)[None, :]
    x = np.asarray(points)[:, None]
    return ph * np.exp(2j * math.pi * m[None, :] * (x + L) / (2 * L)) / math.sqrt(2 * L)


def eval_dirichlet2n_weights(points, L):
    """P2 (amendments inv5 + inv7): Dirichlet kernel of an ODD oversampled
    grid, M = 2N+1 points of period 2L.

    Why odd M: the kernel (1/M) sum_{|k|<=(M-1)/2} exp(2 pi i k u / P) =
    sin(pi M u / P) / (M sin(pi u / P)) reproduces the band |m| <=
    (M-1)/2 = N EXACTLY only for odd M; for even M the symmetric band sum
    is 2K+1 = M-1, not M (the second smoke G4 mismatch, ~1e-5, was this
    parity bug). The trial space modes m = 1..N/2 sit strictly interior
    to the band, and d(0) = 1 makes the coincidence mask exact.
    Deliberately implemented via a fresh kernel formula + FFT path
    (below), independent of P1's direct evec evaluation.
    """
    M = 2 * N + 1
    hs = 2 * L / M
    xs2 = -L + np.arange(M) * hs
    u = np.asarray(points)[:, None] - xs2[None, :]
    num = np.sin(math.pi * M * u / (2 * L))
    den = M * np.sin(math.pi * u / (2 * L))
    with np.errstate(divide="ignore", invalid="ignore"):
        w = np.where(np.abs(u) < 1e-14 * hs, 1.0, num / den)
    return w


def eval_grid2n(Vcols, L):
    """Sector-function values on the M = 2N+1 oversampled grid (FFT path)."""
    M = 2 * N + 1
    mm = np.arange(1, D + 1)
    A = Vcols * np.where(mm % 2 == 0, 1.0, -1.0)[:, None] / math.sqrt(2 * L)
    b = np.zeros((M, Vcols.shape[1]), dtype=complex)
    b[1:D + 1] = A
    return M * np.fft.ifft(b, axis=0)


def zeta_gammas(Tmax):
    """gammas up to Tmax + residuals |zeta(1/2+i g)| (independent witness)."""
    from mpmath import mp
    mp.dps = 25
    gs, resid, n = [], [], 1
    while True:
        g = float(mp.im(mp.zetazero(n)))
        if g > Tmax:
            return gs, resid
        gs.append(g)
        resid.append(float(abs(mp.zeta(0.5 + mp.j * mp.mpf(repr(g))))))
        n += 1


def rank_pair(sv, r, out):
    ranks = []
    for tol in TOL_RANKS:
        k = int(np.sum(sv > tol * sv[0])) if len(sv) else 0
        ranks.append(k)
    out["rankE_tolpair"] = ranks
    if abs(ranks[0] - ranks[1]) > 0.02 * r:
        return None
    return ranks[0]


def main():
    t0 = time.time()
    res = {"record": 1338, "N": N, "margin": MARGIN, "flavors": FLAVORS,
           "gates": {}, "cells": {}, "verdict": {}}
    import mpmath
    res["mpmath"] = mpmath.__version__
    gs, resid = zeta_gammas(2 * math.pi * (max(LS) - 1))
    res["zeta_gamma_first10"] = [round(g, 6) for g in gs[:10]]
    res["zeta_gammas"] = gs
    res["zeta_resid_max"] = max(resid)
    res["gates"]["G5_zero_data"] = bool(
        abs(res["zeta_resid_max"]) <= 1e-3
        and all(b > a for a, b in zip(gs, gs[1:]))
        and all(abs(a - b) < 1e-4 for a, b in zip(gs[:10], FIRST10)))
    res["n_zeros_total"] = len(gs)
    print(f"G5 zeros n={len(gs)} max|zeta|={res['zeta_resid_max']:.2e} "
          f"gate={res['gates']['G5_zero_data']}", flush=True)
    if not res["gates"]["G5_zero_data"]:
        print("ABORTED-UNINFORMATIVE: G5", flush=True)
        sys.exit(1)
    # G0 identity control at decisive cell (LC flavor, L=48)
    Lg = 48
    xs = (np.arange(N) - D) * (2 * Lg / N)
    T1 = toeplitz_matrix(np.ones(N), Lg)
    off = np.abs(T1 - np.diag(np.diag(T1)))
    g0 = float(max(off.max(), 1.0 - np.abs(np.diag(T1)).min()))
    res["gates"]["G0_identity_offdiag_and_diag"] = g0
    del T1
    print(f"G0 = {g0:.2e} (need < 1e-10)", flush=True)
    if g0 >= 1e-10:
        print("ABORTED-UNINFORMATIVE: G0", flush=True)
        sys.exit(1)
    # ---- cells ----
    for flavor in FLAVORS:
        for L in LS:
            t1 = time.time()
            h = 2 * L / N
            xs = (np.arange(N) - D) * h
            phi = np.exp(1j * arg_phase(xs, flavor))
            T = toeplitz_matrix(phi, L)
            U, s, Vh = np.linalg.svd(T, full_matrices=False)
            del T, U, phi
            r = int(np.sum(s < EPS))
            wl = winding_cycles(L, flavor)
            cell = {"flavor": flavor, "L": L, "winding": wl, "rank_eps": r,
                    "ratio": r / abs(wl),
                    "cliff_gap": (float(s[D - r - 1] / s[D - r])
                                  if 0 < r < D else None)}
            Eb = basis_matrix(L)
            Kfull = np.sum(np.abs(Eb) ** 2, axis=1) * h
            cell["G1_kfull_max_err"] = float(
                np.max(np.abs(Kfull - D * h / (2 * L))))
            V = Vh.conj().T[:, D - r:]      # near-kernel = TAIL of desc sv
            del Vh
            K = np.sum(np.abs(Eb @ V) ** 2, axis=1) * h
            cell["trace_dev"] = abs(float(K.sum()) - r) / r
            # control: corridor capacity of the CORRECTED unconstrained
            # sector = the fixed 1334 S2 (sector-defect corrigendum).
            Aunc = {f"log{p}": float(np.sum((2 + 2 * np.cos(
                2 * math.pi * tau * xs)) * K) / r)
                for p, tau in zip(PRIMES, TAUS)}
            cell["A_tau_unc"] = Aunc
            cell["Aunc_max"] = max(Aunc.values())
            cell["Aunc_min"] = min(Aunc.values())
            # constraint points
            pts = [g / (2 * math.pi) for g in gs if g / (2 * math.pi) < L - MARGIN]
            pts = sorted(set([p for p in pts] + [-p for p in pts]))
            cell["2M"] = len(pts)
            # P1 functionals: V already holds ORTHONORMAL trig coefficients
            # (columns of the D x D right-singular matrix; Eb^H Eb h = I),
            # so evaluation is directly Evals @ V.
            Vf = Eb @ V                                     # N x r grid values
            F1 = eval_trig_rows(pts, L) @ V                 # 2M x r
            # P2 cross-check (G4) on 3 sector vectors, 2N oversampled path
            idx = [0, r // 2, r - 1]
            B2 = eval_dirichlet2n_weights(np.asarray(pts), L)   # 2M x 2N
            F2 = B2 @ eval_grid2n(V[:, idx], L)                 # 2M x 3
            g4 = float(max(
                np.max(np.abs(F2[:, t] - F1[:, idx[t]])) /
                max(1e-30, np.max(np.abs(F1[:, idx[t]])))
                for t in range(3)))
            cell["G4_eval_crosscheck"] = g4
            del B2, F2
            # rank / survivors.  full_matrices=True REQUIRED (inv4): a thin
            # SVD of the 2M x r matrix returns only min(2M,r) right vectors,
            # silently truncating the null space (smoke produced a 0-column
            # "null basis" -> phantom A_tau = 0.000).
            _, sv, VhF = np.linalg.svd(F1, full_matrices=True)
            rk = rank_pair(sv, r, cell)
            if rk is None:
                cell["soft_rank"] = True
                cell["secs"] = round(time.time() - t1, 1)
                res["cells"][f"{flavor}_L{L}"] = cell
                if SMOKE:
                    print(f"CELL {flavor} L={L}: SOFT RANK -> WARN (smoke)",
                          flush=True)
                    del Eb, V, Vf, K, F1, s, xs, VhF, sv
                    continue
                print(f"CELL {flavor} L={L}: SOFT RANK -> ABORT", flush=True)
                json.dump(res, open(OUT, "w"), indent=1)
                print("ABORTED-UNINFORMATIVE: G3", flush=True)
                sys.exit(1)
            cell["r_prime"] = r - rk
            cell["f"] = (r - rk) / r
            cell["f0"] = 1 - len(pts) / r
            if cell["r_prime"] >= 3:
                Cc = VhF.conj().T[:, rk:]                   # r x r' coeffs
                Vc = Vf @ Cc                                # N x r' grid vals
                Kc = np.sum(np.abs(Vc) ** 2, axis=1) * h
                cell["trace_dev_c"] = abs(float(Kc.sum()) - cell["r_prime"]) \
                    / cell["r_prime"]
                A_tau = {}
                for p, tau in zip(PRIMES, TAUS):
                    A_tau[f"log{p}"] = float(np.sum((2 + 2 * np.cos(
                        2 * math.pi * tau * xs)) * Kc) / cell["r_prime"])
                cell["A_tau"] = A_tau
                cell["A_max"] = max(A_tau.values())
                cell["A_min"] = min(A_tau.values())
            cell["secs"] = round(time.time() - t1, 1)
            res["cells"][f"{flavor}_L{L}"] = cell
            cg = "inf" if cell["cliff_gap"] is None else f"{cell['cliff_gap']:.1e}"
            print(f"CELL {flavor} L={L}: r={r} wind={wl:.1f} 2M={len(pts)} "
                  f"rankE={rk} f={cell['f']:.3f} f0={cell['f0']:.3f} "
                  f"cliff={cg} Aunc=[{cell['Aunc_min']:.3f},"
                  f"{cell['Aunc_max']:.3f}] A=[{cell.get('A_min', -1):.3f},"
                  f"{cell.get('A_max', -1):.3f}] trk={cell.get('trace_dev_c', -1):.1e} "
                  f"G4={g4:.1e} ({cell['secs']}s)",
                  flush=True)
            if cell["secs"] > BUDGET_S:
                print(f"WARN budget breach {flavor} L={L}", flush=True)
            del Eb, V, Vf, K, F1, s, xs, VhF, sv
    # ---- gates ----
    def cell_ok(c):
        v = (c["G1_kfull_max_err"] < 1e-10 and c["trace_dev"] < 1e-8
             and c["G4_eval_crosscheck"] < 1e-9)
        # G7 (amendment inv6): constrained-sector kernel trace = r' to 1e-8
        if c.get("trace_dev_c") is not None:
            v = v and c["trace_dev_c"] < 1e-8
        # G2 cliff: official only (resolution-limited at smoke, inv6)
        if not SMOKE:
            v = v and (c["cliff_gap"] is None or c["cliff_gap"] > 10)
        return v
    ok = all(cell_ok(c) for c in res["cells"].values())
    # G6 LC continuity (only at official N)
    g6 = True
    if N == 8192:
        g6 = all(abs(res["cells"][f"LC_L{L}"]["rank_eps"] - t) <=
                 max(2, 0.01 * t) for L, t in LC_R_TARGET.items())
    res["gates"]["G1_G2_G4_G6_G7_all"] = bool(ok and g6)
    if not (ok and g6):
        print("ABORTED-UNINFORMATIVE: G1/G2/G4/G6/G7", flush=True)
        json.dump(res, open(OUT, "w"), indent=1)
        sys.exit(1)
    if SMOKE:
        res["verdict"]["NOTE"] = "SMOKE: machinery only, no verdict digits"
        res["total_secs"] = round(time.time() - t0, 1)
        json.dump(res, open(OUT, "w"), indent=1)
        print("SMOKE-MACHINERY-GREEN (no license reading)", flush=True)
        print("DONE 1338", flush=True)
        return
    # ---- verdicts (decisive cell L=48 per flavor) ----
    def s1(c):
        f = c["f"]
        return "THINS" if f <= 0.25 else "NO-THIN" if f >= 0.50 else "INCONCLUSIVE"

    def s2(c):
        if "A_max" not in c:
            return "DEGENERATE-SECTOR"
        return ("CONCENTRATES" if c["A_max"] <= 0.30
                else "FALSIFIES" if c["A_min"] >= 1.20 else "INCONCLUSIVE")

    def s0u(c):
        return ("CONCENTRATES" if c["Aunc_max"] <= 0.30
                else "FALSIFIES" if c["Aunc_min"] >= 1.20 else "INCONCLUSIVE")

    for flavor in FLAVORS:
        dc = res["cells"][f"{flavor}_L48"]
        res["verdict"][f"S1_{flavor}"] = s1(dc)
        res["verdict"][f"S2_{flavor}"] = s2(dc)
        res["verdict"][f"S0unc_{flavor}"] = s0u(dc)
    live = any(res["verdict"][f"S1_{f}"] == "THINS" and
               res["verdict"][f"S2_{f}"] == "CONCENTRATES" for f in FLAVORS)
    res["verdict"]["LICENSE_M2"] = bool(live)
    res["total_secs"] = round(time.time() - t0, 1)
    json.dump(res, open(OUT, "w"), indent=1)
    print("VERDICT", json.dumps(res["verdict"]), flush=True)
    print("DONE 1338", flush=True)


if __name__ == "__main__":
    main()
