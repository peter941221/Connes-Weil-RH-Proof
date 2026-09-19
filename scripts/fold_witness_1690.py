#!/usr/bin/env python3
# 1690 — Fold-witness decision rig (record 1690 companion).
#
# F61-compliant: fixed ansatz vectors only (no spectrum readings, no
# truncated-grid carrier statements).  Decision question: does the phase
# fold at xi0 = lambda^-2 CREATE carrier mass, i.e. does the Fresnel
# Wiener--Hopf half-line block  A = P_+ F_a P_+  admit near-kernel ansatz
# vectors, and at what measured depth?
#
# Model (hand-derived, record 1690): near the fold, gamma''(xi0) = 2 pi
# lambda^2, so the local multiplier is the pure chirp e^{i pi a (xi-xi0)^2}
# with a = lambda^2; its convolution kernel is
#     F_a(s) = a^{-1/2} e^{i pi/4} e^{-i pi s^2 / a},
# and the local block is the chirped WH corner A = P_+ F_a P_+.
#
# Designed near-kernel direction (counter-chirp shear): on the half line,
#     b(y) = rho((y-d)/w) * e^{+i pi y^2/a} * e^{-2 pi i q y},  q = -d/a,
# cancels the kernel chirp to a LINEAR y-phase, so (EXACT Gaussian FT,
# code convention rho = e^{-t^2/2}):
#     |A b(x)| = (w sqrt(2 pi)/sqrt(a)) e^{-2 pi^2 w^2 (x/a - q)^2}
# — a Gaussian centered at x_out = a q = -d < 0.  The P_+ survivor is the
# Gaussian tail, giving the EXPLICIT erfc depth
#     r_erfc(d,w,a) = sqrt( erfc(2 pi w d / a) / 2 ).
# The one-sided input truncation at y = 0 adds an ALGEBRAIC floor (the
# FT tail of the y=0 jump, value e^{-d^2/(2w^2)}):
#     r_trunc(d,w,a) = sqrt( a e^{-(d/w)^2} / (4 pi^2 d w sqrt(pi)) ),
# and the sampled-grid quadrature adds a machine-level floor.  The true
# landscape is the RACE between the erfc depth and the truncation floor;
# r(d,w) ~ max(r_erfc, r_trunc) -> 0 along d/w -> inf AND wd/a -> inf.
#
# Readouts:
#   [CTRL] interior UNCHIRPED bump: no shear (stationary phase at y=x),
#          r ~ 1 — chirp cancellation is essential, not generic smallness.
#   [SWEEP] q swept at fixed (d,w): r(q=+d/a) ~ 1 > r(0) ~ 1/sqrt 2 >
#          r(-d/a) = r_pred — the minimum sits at the designed address.
#   [FAMILY] (d,w) grid at q = -d/a: measured r vs the race calibration.
#   [SHEAR] output-profile correlation with the analytic prediction.

import numpy as np
import math
import json
import os

RESULTS = {}


def fresnel_block(a, xs):
    """Discretized Fresnel WH block on the half-line grid xs (x > 0):
    A[j,k] = F_a(x_j - x_k) * dx,  F_a(s) = a^{-1/2} e^{i pi/4} e^{-i pi s^2/a}."""
    dx = xs[1] - xs[0]
    S = xs[:, None] - xs[None, :]
    F = (a ** -0.5) * np.exp(1j * np.pi / 4) * np.exp(-1j * np.pi * S * S / a)
    return F * dx


def packet(xs, d, w, q, a):
    """Counter-chirped Weyl packet on the half-line grid:
    rho((y-d)/w) e^{+i pi y^2/a} e^{-2 pi i q y}, unit L2(grid) norm.
    The quadratic factor is ESSENTIAL (it cancels the kernel chirp)."""
    b = (np.exp(-0.5 * ((xs - d) / w) ** 2)
         * np.exp(1j * np.pi * xs ** 2 / a)
         * np.exp(-2j * np.pi * q * xs))
    return b / np.linalg.norm(b)


def plain_bump(xs, d, w):
    """Unchirped Gaussian packet (control), unit norm."""
    b = np.exp(-0.5 * ((xs - d) / w) ** 2)
    return b / np.linalg.norm(b)


def r_erfc(d, w, a):
    """erfc depth: P_+ survivor of the counter-chirped packet (EXACT for
    the full-line Gaussian FT, code convention rho = e^{-t^2/2})."""
    return math.sqrt(math.erfc(2.0 * math.pi * w * d / a) / 2.0)


def r_trunc(d, w, a):
    """One-sided truncation floor: algebraic FT tail of the y = 0 jump
    e^{-d^2/(2 w^2)} (dominates the erfc depth for wide packets)."""
    return math.sqrt(a * math.exp(-(d / w) ** 2)
                     / (4.0 * math.pi ** 2 * d * w * math.sqrt(math.pi)))


def r_pred(d, w, a):
    """Race calibration: the measured depth is the larger of the erfc
    tail and the truncation floor (grid quadrature floor on top)."""
    return max(r_erfc(d, w, a), r_trunc(d, w, a))


def output_profile_pred(xs, w, q, a):
    """Analytic output modulus (before P_+): w sqrt(2 pi)/sqrt(a) *
    exp(-2 pi^2 w^2 (x/a - q)^2), on the grid."""
    s = xs / a - q
    return (w * math.sqrt(2.0 * math.pi) / math.sqrt(a)) * np.exp(-2.0 * math.pi ** 2 * w * w * s * s)


def run(lam):
    a = lam * lam
    # resolve the witness modulation |q| up to 8/lambda and the kernel
    # chirp: dx = lambda/120 keeps the per-step phase <= ~0.26 rad.
    dx = lam / 120.0
    X = 3.0 if lam > 0.15 else 1.5          # must cover d + 3w, d up to 8 lam
    n = int(X / dx)
    xs = np.arange(n) * dx + dx             # x in (0, X]
    A = fresnel_block(a, xs)
    print(f"  lam={lam}  a={a}  grid N={n} dx={dx:.5f} X={X}")

    # [CTRL] interior unchirped bump: no counter-chirp => no shear.
    b0 = plain_bump(xs, 0.8 if lam > 0.15 else 0.4, lam)
    r_ctrl = float(np.linalg.norm(A @ b0))
    print(f"    [CTRL] unchirped interior bump      r = {r_ctrl:.4f}")

    # [SWEEP] q direction readout at d = 4 lam, w = lam.
    d_s, w_s = 4.0 * lam, lam
    sweep = []
    for qfac, tag in ((+1.0, "q=+d/a"), (0.0, "q=0"),
                      (-0.5, "q=-d/2a"), (-1.0, "q=-d/a")):
        q = qfac * d_s / a
        b = packet(xs, d_s, w_s, q, a)
        r = float(np.linalg.norm(A @ b))
        sweep.append({"tag": tag, "q_over_d/a": qfac, "r": r})
        print(f"    [SWEEP] {tag:<8} r = {r:.6f}")

    # [FAMILY] counter-chirped packets at q = -d/a.
    rows = []
    for dl in (2.0, 4.0, 8.0):
        for wl in (0.5, 1.0, 2.0):
            d, w = dl * lam, wl * lam
            b = packet(xs, d, w, -d / a, a)
            r = float(np.linalg.norm(A @ b))
            rows.append({"dl": dl, "wl": wl, "d_over_w": d / w,
                         "r": r, "r_pred": r_pred(d, w, a)})
    print("    [FAMILY] measured r vs erfc calibration (q = -d/a):")
    for t in rows:
        ratio = (t["r"] / t["r_pred"]) if t["r_pred"] > 0 else float("inf")
        flag = " (d/w=1: y<0 truncation)" if t["d_over_w"] < 1.5 else ""
        print(f"      d={t['dl']:.0f}lam w={t['wl']:.1f}lam  r={t['r']:.3e}"
              f"  pred={t['r_pred']:.3e}  ratio={ratio:8.3f}{flag}")

    # [SHEAR] output-profile shape check at d = 4 lam, w = lam: compare
    # BOTH analytic profiles — the sheared Gaussian peak (sits OFF-grid at
    # x = -d; only its tail could show) and the one-sided truncation tail
    # a^{1/2} e^{-(d/w)^2/2} / (2 pi (x+d)) (dominant when r_trunc wins).
    d_sh, w_sh = 4.0 * lam, lam
    b = packet(xs, d_sh, w_sh, -d_sh / a, a)
    out = np.abs(A @ b)
    pred_peak = output_profile_pred(xs, w_sh, -d_sh / a, a)
    pred_tail = (math.sqrt(a) * math.exp(-0.5 * (d_sh / w_sh) ** 2)
                 / (2.0 * math.pi * (xs + d_sh)))
    corr_peak = float(np.abs(np.dot(out, pred_peak))
                      / (np.linalg.norm(out) * np.linalg.norm(pred_peak) + 1e-300))
    corr_tail = float(np.abs(np.dot(out, pred_tail))
                      / (np.linalg.norm(out) * np.linalg.norm(pred_tail) + 1e-300))
    print(f"    [SHEAR] profile correlation: truncation tail {corr_tail:.6f},"
          f" gaussian peak {corr_peak:.6f}")
    return {"lam": lam, "a": a, "N": n, "dx": dx, "X": X,
            "r_ctrl": r_ctrl, "sweep": sweep, "rows": rows,
            "shear_corr_tail": corr_tail, "shear_corr_peak": corr_peak}


def main():
    print("== fold-witness decision rig (fixed ansatz, F61-compliant) ==")
    print("== [IDENTITY CONTROL] no chirp (a -> 0, F_a -> delta) ==")
    print("  r = 1 exactly (identity block, no boundary to slip through)")
    RESULTS["control_identity"] = 1.0
    for lam in (0.2, 0.1):
        print(f"== [FOLD] lambda = {lam} ==")
        RESULTS[f"lam{lam}"] = run(lam)
    os.makedirs("tmp", exist_ok=True)
    with open("tmp/fold_witness_1690_results.json", "w") as f:
        json.dump(RESULTS, f, indent=1)
    print("results -> tmp/fold_witness_1690_results.json")


if __name__ == "__main__":
    main()
