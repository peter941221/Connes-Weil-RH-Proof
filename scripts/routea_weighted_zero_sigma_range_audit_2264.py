#!/usr/bin/env python3
"""2264 - sigma-range audit: does the frozen direct-product constant cover
the centered strip that the Lean chain actually needs?

Consumer: record 2260 asserts the 2197/2234/2243 screen constant
B_upper = 9506275.102584327 = (2*pi)^2 * C bounds the constant C of
`exists_spectral_laplaceAt_quadratic_bound`
(ConnesWeilRH/Dev/C1SpectralWeil.lean:275), whose evaluations happen at
`centeredXiCoordinate rho = (rho.re - 1/2) + i rho.im`, i.e. at Laplace
real parts in (-1/2, 1/2).

For F = base * corr in Laplace space (product law of
CC20YoshidaConvolution.laplaceAt_convolution) the two-IBP estimate with
sig = Re s is

    t^2 * ||L(base)(s) * L(corr)(s)||
      <= min( D2_b(sig) * M_c(sig), D2_c(sig) * M_b(sig) ),

where M_f(sig) = int exp(sig*x) |f| and D2_f(sig) = int exp(sig*x) |f''|
are the strip-weighted L1 norms of the committed 2197 screen.  The chain
therefore needs the sup over sig in (-1/2, 1/2), while the committed
2197/2234/2243 envelope tabulates sig on [0, 1] and its certified row is
sig = 1.  This audit measures the raw (binary64 trapezoid) min-product on
an extended grid sig in [-0.6, 1.1] for the committed 2234 construction
(results/2234_build_cache.npz) and reports the maxima over [0, 1],
[-1/2, 1/2] and [-1/2, 1], each against the frozen 2243 constant and the
raw 2197 value.

Anchors: at sig = 1.0 the recomputed norms must reproduce the committed
2197 binding row bitwise at binary64 level.

Verdict: whether the frozen constant already covers the centered range at
screen grade (with margin), or whether the negative-sigma half needs its
own certified envelope (2234-style panel/coeff/Lipschitz re-run on
[-1/2, 1]) before the producer lemma may consume the frozen number.
"""
import json
import math
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
CACHE = ROOT / "results" / "2234_build_cache.npz"
OUTPUT = ROOT / "results" / "2264_sigma_range_audit.json"

K = 30.0
NX = 240001
FROZEN_2243 = 9506275.102584327
RAW_2197 = 3057372.2573045553
ANCHOR_2197_ROW = {
    "base_M0": 2.0033357887456087,
    "base_D2": 6688.576604759935,
    "corr_M0": 913.4469710803505,
    "corr_D2": 1526140.687188009,
}


def family_sums(x, fam_a, fam_theta, base, corr):
    """The four committed 2197 sums (base, base'', corr, corr'')."""
    phi_sum = np.zeros_like(x, dtype=complex)
    phi2_sum = np.zeros_like(x, dtype=complex)
    corr_sum = np.zeros_like(x, dtype=complex)
    corr2_sum = np.zeros_like(x, dtype=complex)
    for acoef, (a, theta) in zip(base, zip(fam_a, fam_theta)):
        u = x / a
        q = 1.0 - u * u
        mask = q > 0.0
        phi = np.zeros_like(x)
        phi[mask] = np.exp(-K / q[mask])
        e1 = np.zeros_like(x)
        e2 = np.zeros_like(x)
        e1[mask] = -2.0 * K * u[mask] / (a * q[mask] ** 2)
        e2[mask] = (-2.0 * K / (a * a) *
                    (1.0 / q[mask] ** 2 + 4.0 * u[mask] ** 2 / q[mask] ** 3))
        phase = np.exp(1j * theta * x)
        phi_sum += acoef * phi * phase
        phi2_sum += acoef * phi * (e2 + e1 * e1 + 2j * theta * e1 - theta * theta) * phase
    for ccoef, (a, theta) in zip(corr, zip(fam_a, fam_theta)):
        u = x / a
        q = 1.0 - u * u
        mask = q > 0.0
        phi = np.zeros_like(x)
        phi[mask] = np.exp(-K / q[mask])
        e1 = np.zeros_like(x)
        e2 = np.zeros_like(x)
        e1[mask] = -2.0 * K * u[mask] / (a * q[mask] ** 2)
        e2[mask] = (-2.0 * K / (a * a) *
                    (1.0 / q[mask] ** 2 + 4.0 * u[mask] ** 2 / q[mask] ** 3))
        phase = np.exp(1j * theta * x)
        corr_sum += ccoef * phi * phase
        corr2_sum += ccoef * phi * (e2 + e1 * e1 + 2j * theta * e1 - theta * theta) * phase
    return phi_sum, phi2_sum, corr_sum, corr2_sum


def main():
    data = np.load(CACHE, allow_pickle=True)
    fam_a = data["fam_a"]
    fam_theta = data["fam_theta"]
    base = data["base"]
    corr = data["corr"]
    a_max = float(data["a_max"])
    x = np.linspace(-a_max, a_max, NX)
    phi_sum, phi2_sum, corr_sum, corr2_sum = family_sums(
        x, fam_a, fam_theta, base, corr)

    sigma_grid = np.linspace(-0.6, 1.1, 341)
    rows = []
    for sigma in sigma_grid:
        w = np.exp(float(sigma) * x)
        mb = float(np.trapezoid(np.abs(phi_sum) * w, x))
        db = float(np.trapezoid(np.abs(phi2_sum) * w, x))
        mc = float(np.trapezoid(np.abs(corr_sum) * w, x))
        dc = float(np.trapezoid(np.abs(corr2_sum) * w, x))
        cha = db * mc
        chb = dc * mb
        rows.append({
            "sigma": float(sigma),
            "base_M0": mb, "base_D2": db, "corr_M0": mc, "corr_D2": dc,
            "channel_a": cha, "channel_b": chb,
            "B": min(cha, chb), "C": min(cha, chb) / (2.0 * math.pi) ** 2,
            "binding": "a" if cha <= chb else "b",
        })

    row_at = {round(r["sigma"], 9): r for r in rows}
    anchor = row_at[1.0]
    anchor_rel = {
        key: abs(anchor[key] - value) / max(abs(value), 1e-300)
        for key, value in ANCHOR_2197_ROW.items()}
    anchor_ok = all(v <= 1e-9 for v in anchor_rel.values())

    def best(lo, hi):
        sel = [r for r in rows if lo <= r["sigma"] <= hi]
        return max(sel, key=lambda r: r["B"])

    best_01 = best(0.0, 1.0)
    best_c = best(-0.5, 0.5)
    best_u = best(-0.5, 1.0)
    best_neg = best(-0.6, 0.0)
    row_mhalf = row_at[-0.5]
    covered = best_c["B"] <= FROZEN_2243
    margin = FROZEN_2243 / best_c["B"] if best_c["B"] > 0 else float("inf")
    verdict = (
        f"SIGMA-RANGE-AUDIT: "
        f"{'COVERED' if covered else 'GAP'}. The committed screen envelope "
        f"tabulates sigma in [0, 1] with the certified row at sigma = 1; the "
        f"Lean chain needs sigma in (-1/2, 1/2). Raw binary64 survey on "
        f"[-0.6, 1.1]: max over [0, 1] = {best_01['B']:.10g} at "
        f"sigma = {best_01['sigma']:.4f} (channel {best_01['binding']}) "
        f"(anchor {RAW_2197:.10g}); max over [-1/2, 1/2] = "
        f"{best_c['B']:.10g} at sigma = {best_c['sigma']:.4f} (channel "
        f"{best_c['binding']}); max over [-1/2, 1] = {best_u['B']:.10g} at "
        f"sigma = {best_u['sigma']:.4f}; over [-0.6, 0] = "
        f"{best_neg['B']:.10g} at sigma = {best_neg['sigma']:.4f}. Against "
        f"the frozen bUpper2243 = {FROZEN_2243}: centered max sits at "
        f"{best_c['B'] / FROZEN_2243:.6f} of the frozen constant "
        f"(margin {margin:.4f}x). "
        + ("The frozen constant already dominates the centered range at "
           "screen grade; the producer still needs a certified envelope on "
           "the negative half (2234-style panel/coeff/Lipschitz re-run on "
           "[-1/2, 1]) before consuming the frozen number."
           if covered else
           "The centered range is NOT covered by the frozen constant at "
           "screen grade: the negative half needs its own envelope and the "
           "frozen bUpper2243 must be repriced on [-1/2, 1].")
        + " No producer GO, no gate sign change, no RH claim.")

    result = {
        "record": 2264,
        "status": "SCREEN-GRADE-SIGMA-AUDIT",
        "construction": {
            "cache": "results/2234_build_cache.npz",
            "grid": {"x_nodes": NX, "a_max": a_max, "K": K},
        },
        "anchor_sigma1": {
            "row": {k: anchor[k] for k in ANCHOR_2197_ROW},
            "rel": anchor_rel,
            "ok": anchor_ok,
        },
        "maxima": {
            "over_0_1": best_01,
            "over_centered": best_c,
            "over_union": best_u,
            "over_negative": best_neg,
            "sigma_minus_half": row_mhalf,
        },
        "frozen_2243": FROZEN_2243,
        "raw_2197": RAW_2197,
        "covered": covered,
        "centered_over_frozen": best_c["B"] / FROZEN_2243,
        "margin_vs_frozen": margin,
        "grid": rows,
        "verdict": verdict,
        "nonclaims": [
            "binary64 trapezoid measurements on the committed grid; not "
            "outward interval enclosures",
            "the negative-sigma half carries no certified panel/coefficient/"
            "Lipschitz envelope yet",
            "single candidate construction (2234 build cache); the three "
            "2103 stress candidates are not re-measured here",
            "no producer GO, no gate sign change, no RH claim",
        ],
        "provenance": {
            "script": "scripts/routea_weighted_zero_sigma_range_audit_2264.py",
            "chain": "ConnesWeilRH/Dev/C1SpectralWeil.lean:275 "
                     "(centeredXiCoordinate)",
            "screen": "scripts/routea_weighted_zero_direct_product_mass_"
                      "screen_2197.py",
            "frozen": "results/2243_panel_cem_reprice.json",
        },
    }
    OUTPUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8",
                      newline="\n")
    print(json.dumps({
        "anchor_ok": anchor_ok,
        "anchor_rel": anchor_rel,
        "over_0_1": best_01["B"], "over_centered": best_c["B"],
        "centered_sigma": best_c["sigma"],
        "over_union": best_u["B"], "over_negative": best_neg["B"],
        "covered": covered, "margin_vs_frozen": margin,
    }, indent=2))
    print(verdict)


if __name__ == "__main__":
    main()