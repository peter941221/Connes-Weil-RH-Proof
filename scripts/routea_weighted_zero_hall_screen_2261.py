#!/usr/bin/env python3
"""2261 - Coalitional Hall screen of the direct-product rows (count-side LP).

Consumer: record 2258 registered the coalitional Hall LP as the open
allocation-design question for any count-side revival.  This record
computes its two decidable pieces:

1.  single-factor optimal-cap lower bounds.  Every feasible pointwise
    allocation of a row (a_j(x), 0 <= a_j(x) <= |g_j(x)|,
    sum_j a_j(x) >= |G(x)|) satisfies, for every coalition J,
        sum_{j in J} a_j >= Hall(J) = int e^{sigma x} (|G| - (S - A_J))^+,
    hence max_j a_j >= max_J Hall(J)/|J|.  The greedy coalition curve
    Hall_k (best found coalition of each size k) gives a certified LOWER
    bound t*_lo = max_k 62 Hall_k / (k row) on the best single-factor
    split ratio over the uniform budget row/62.  The k = 30 term is
    exactly 62/30 (the pigeonhole bound).

2.  disjoint-cover diagnostics.  For natural partitions of the 30
    families, Hall(part) measures whether one side alone covers the
    integrand pointwise.  Hall(part) ~ 0 on both sides of a partition
    would make the disjoint two-sided product split degenerate (charge
    ~ 0), confirming that the pointwise universe alone cannot decide
    the product feasibility -- the honest universe needs the analytic
    fixed per-node pieces (the 2258 registered conclusion).

Sampling: float64 numpy on the committed 2197 grid, the 2258 machinery.

Writes results/2261_hall_screen.json.
"""
import json
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import routea_weighted_zero_cancellation_split_2258 as c58  # noqa: E402  # pyright: ignore[reportMissingImports]
import routea_weighted_zero_direct_product_outward_2234 as o34  # noqa: E402  # pyright: ignore[reportMissingImports]

RECORD = 2261
OUTPUT = ROOT / "results" / "2261_hall_screen.json"
BUDGET_DENOM = c58.BUDGET_DENOM
NX = c58.NX


def row_arrays(fam, coef, kind, x):
    """Per-family magnitudes M (30, NX), signed sum modulus AG, total S."""
    M = np.empty((len(fam), NX))
    G = np.zeros(NX, complex)
    for j, (a, th) in enumerate(fam):
        g_m0, g_d2 = c58.family_terms(x, a, th)
        g = coef[j] * (g_m0 if kind == "M0" else g_d2)
        G += g
        M[j] = np.abs(g)
    AG = np.abs(G)
    S = M.sum(axis=0)
    return M, AG, S


def hall_of(mags, AG, wgt):
    """Hall mass of the coalition whose magnitude sum is `mags`."""
    deficit = np.maximum(AG - mags, 0.0)
    return float(np.sum(wgt * deficit))


def main():
    fam, base, corr, a_max = o34.build_construction()
    x = np.linspace(-a_max, a_max, NX)
    wgt = c58.trap_weights(x, a_max)
    rows = ("base_M0", "corr_M0", "base_D2", "corr_D2")
    coef_of = {"base_M0": base, "corr_M0": corr,
               "base_D2": base, "corr_D2": corr}
    kind_of = {"base_M0": "M0", "corr_M0": "M0",
               "base_D2": "D2", "corr_D2": "D2"}

    thetas = np.asarray([t for _, t in fam])
    widths = np.asarray([a for a, _ in fam])

    out_rows = {}
    for r in rows:
        M, AG, S = row_arrays(fam, coef_of[r], kind_of[r], x)
        row_norm = float(np.sum(wgt * AG))
        delta = S - AG

        # greedy coalition curve
        chosen = []
        remaining = list(range(len(fam)))
        T = np.zeros(NX)
        curve = []
        for k in range(1, len(fam) + 1):
            best_j = remaining[0]
            best_h = -1.0
            for j in remaining:
                h = float(np.sum(wgt * np.maximum(T + M[j] - delta, 0.0)))
                if h > best_h:
                    best_j, best_h = j, h
            chosen.append(int(best_j))
            remaining.remove(best_j)
            T = T + M[best_j]
            curve.append({
                "k": k, "added": int(best_j),
                "hall": best_h,
                "ratio_over_budget": BUDGET_DENOM * best_h / (k * row_norm),
            })
        t_lo = max(c["ratio_over_budget"] for c in curve)
        k_star = max(curve, key=lambda c: c["ratio_over_budget"])["k"]

        # disjoint-cover diagnostics
        partitions = {
            "parity": [np.asarray([j % 2 == 0 for j in range(len(fam))]),
                       np.asarray([j % 2 == 1 for j in range(len(fam))])],
            "halves": [np.arange(len(fam)) < 15,
                       np.arange(len(fam)) >= 15],
            "theta_sign": [thetas >= 0.0, thetas < 0.0],
            "min_width": [widths == widths.min(), widths != widths.min()],
        }
        parts = {}
        for name, (sel1, sel2) in partitions.items():
            parts[name] = {}
            for label, sel in (("part_a", sel1), ("part_b", sel2)):
                sel = np.asarray(sel)
                mags = M[sel].sum(axis=0)
                h = hall_of(mags, AG, wgt)
                parts[name][label] = {
                    "size": int(sel.sum()),
                    "hall": h,
                    "ratio_over_budget": BUDGET_DENOM * h / row_norm,
                    "min_cover_ratio": float(np.min(
                        np.where(AG > 0, mags / np.maximum(AG, 1e-300),
                                 np.inf))),
                }
        out_rows[r] = {
            "norm": row_norm,
            "t_star_lower": t_lo,
            "t_star_lower_k": k_star,
            "curve": curve,
            "partitions": parts,
        }
        print(json.dumps({r: {"t_star_lower": t_lo, "k": k_star,
                              "k30": curve[-1]["ratio_over_budget"],
                              "parts": {n: {l: p["ratio_over_budget"]
                                            for l, p in d.items()}
                                        for n, d in parts.items()}}}),
              flush=True)

    result = {
        "record": RECORD,
        "status": "HALL-SCREEN (single-factor cap lower bounds + "
                  "disjoint-cover diagnostics)",
        "date": "2026-09-30",
        "budget_denom": BUDGET_DENOM,
        "pigeonhole_floor": BUDGET_DENOM / len(fam),
        "rows": out_rows,
        "verdict": None,
        "nonclaims": [
            "the greedy curve gives LOWER bounds on max_J Hall(J)/|J| "
            "(any found coalition is a certificate); the exact LP dual "
            "is not claimed",
            "the Hall family is a necessary condition on feasible "
            "pointwise allocations; sufficiency of the Hall family is "
            "not used",
            "float64 measurement on the committed grid",
            "no producer GO, no gate sign change, no RH claim",
        ],
        "provenance": {
            "script": "scripts/routea_weighted_zero_hall_screen_2261.py",
            "machinery": "scripts/routea_weighted_zero_cancellation_"
                         "split_2258.py (family_terms, weights)",
            "predecessor": "docs/proofs/2258_routea_weighted_zero_"
                           "cancellation_split.md",
        },
    }

    degenerate = []
    for r in rows:
        for name, d in out_rows[r]["partitions"].items():
            a_ = d["part_a"]["ratio_over_budget"]
            b_ = d["part_b"]["ratio_over_budget"]
            if a_ < 0.05 and b_ < 0.05:
                degenerate.append(f"{r}:{name}")
    verdict = (
        f"single-factor optimal-cap lower bounds "
        + " / ".join(f"{out_rows[r]['t_star_lower']:.4g}" for r in rows)
        + f" (>= the exact pigeonhole {BUDGET_DENOM/len(fam):.6g} at "
        "k=30); every single-factor split of every row therefore fails "
        "the uniform budget by at least max(found, 62/30).  "
        + (f"Disjoint self-cover detected for partitions: "
           f"{', '.join(degenerate)} -> the pointwise-universe product "
           "split is degenerate there (zero diagonal charge), so the "
           "count-side feasibility question must be posed on the fixed "
           "analytic per-node pieces.  " if degenerate else
           "No partition is self-covering on both sides; the disjoint "
           "degeneracy does not materialize for these natural "
           "partitions.  ")
        + "The coalitional Hall LP stays registered as the design "
          "question; count-free assembly (2257) remains the live route.")
    result["verdict"] = verdict
    OUTPUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8",
                      newline="\n")
    print(json.dumps({"verdict": verdict}, indent=2))


if __name__ == "__main__":
    main()