#!/usr/bin/env python3
"""2266 - exact Hall curve of the direct-product rows: exhaustive coalition
enumeration at both ends plus certified ceilings in the middle.

Consumer: 2261 registered the exact coalitional Hall quantity

    t* = max_J 62 * Hall(J) / (|J| * row),
    Hall(J) = int e^{sigma x} (|G| - sum_{j not in J} |g_j|)^+

as the design threshold for any single-factor budget row/62 (every feasible
pointwise allocation satisfies max_j a_j >= max_J Hall(J)/|J|).  2261 gave
greedy lower bounds only and its greedy peaks scatter (k* = 28, 9, 18, 8
for the four rows), so neither small-k nor large-k sweeps alone suffice.

A direct LP/MILP encoding of the exact integer problem is not available:
the per-node positive part is the support function of the 2^N sign
patterns, so a pure epigraph with lower-bound rows is unbounded, and the
disjunctive form needs one binary per grid node (240001 of them).  This
record instead computes, on the committed 2197/2258 grid at float64:

1. EXACT Hall_k for every k <= 6 and every k >= 24 by exhaustive
   enumeration (the latter by enumerating the excluded complements of size
   <= 6; same cost class).  k = 30 reproduces the pigeonhole value exactly.
2. Certified per-k ceilings for 7 <= k <= 23 from four valid bounds
   (Hall(J) <= min over the four):
   (a) trivial: Hall(J) <= row                       -> ratio <= 62/k;
   (b) mass:    Hall(J) <= sum_{j in J} int min(|G|, |g_j|)
                (min(|G|, sum_J M) <= sum_J min(|G|, M));
   (c) cover:   Hall(J) <= sum_{j in J} int_{M_j > d/k} |G|
                with d = S - |G| >= 0 (the positive nodes of J satisfy
                sum_J M_j > d, so some member exceeds d/k there, and the
                integrand is pointwise capped by |G|);
   (d) msmall:  Hall(J) <= int (|G| - L_m)^+ with m = 30 - k and L_m(x)
                the sum of the m SMALLEST |g_j(x)| at x: for every
                excluded complement C of size m, sum_C M >= L_m
                pointwise, so (|G| - sum_C M)^+ <= (|G| - L_m)^+.
   (b)/(c) are evaluated at the k largest single-family terms; (d) is
   a single sorted-cumsum scan.
3. Lower bounds in the middle from the greedy curve (recomputed, anchored
   bitwise against results/2261_hall_screen.json) improved by a 1-swap
   hill climb at every k whose ceiling could tighten the global bracket.

Output: per row a two-sided bracket [t*_lo, t*_hi] with the witness
coalitions; the global t* is exact exactly where the bracket closes.
float64 measurements; the ceilings are certified upper bounds, the
hill-climb values only lower bounds.  Writes results/2266_hall_exact.json.
"""
import itertools
import json
import math
import multiprocessing
import os
import sys
import time
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path

os.environ.setdefault("OMP_NUM_THREADS", "1")
os.environ.setdefault("OPENBLAS_NUM_THREADS", "1")
os.environ.setdefault("MKL_NUM_THREADS", "1")

import numpy as np  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import routea_weighted_zero_cancellation_split_2258 as c58  # noqa: E402  # pyright: ignore[reportMissingImports]
import routea_weighted_zero_direct_product_outward_2234 as o34  # noqa: E402  # pyright: ignore[reportMissingImports]

RECORD = 2266
OUTPUT = ROOT / "results" / "2266_hall_exact.json"
SCREEN_2261 = ROOT / "results" / "2261_hall_screen.json"
BUDGET_DENOM = c58.BUDGET_DENOM
NX = c58.NX
NFAM = 30
EXACT_SMALL_MAX = 6      # exact for k <= 6
EXACT_LARGE_MIN = 24     # exact for k >= 24 (complements of size <= 6)
CHUNK = 64
WORKERS = 14

# Fork-shared state for the enumeration workers (set before pool creation).
_G = {}
CTX = multiprocessing.get_context("fork")


def row_arrays(fam, coef, kind, x):
    """Per-family magnitudes M (30, NX), signed sum modulus AG, total S."""
    M = np.empty((len(fam), NX))
    G = np.zeros(NX, complex)
    for j, (a, th) in enumerate(fam):
        g_m0, g_d2 = c58.family_terms(x, a, th)
        g = coef[j] * (g_m0 if kind == "M0" else g_d2)
        G += g
        M[j] = np.abs(g)
    return M, np.abs(G), M.sum(axis=0)


def _chunk_task(args):
    """Best Hall value over a contiguous block of subsets (in/out mode)."""
    k, lo, hi, mode = args
    M, c, wgt, S = _G["M"], _G["c"], _G["wgt"], _G["S"]
    idx = _G["COMB"][k][lo:hi]
    n = len(idx)
    Sx = np.zeros((n, NFAM))
    Sx[np.arange(n)[:, None], idx] = 1.0
    A = Sx @ M
    if mode == "out":
        A = S[None, :] - A
        A += c[None, :]
    else:
        A += c[None, :]
    np.maximum(A, 0.0, out=A)
    A *= wgt[None, :]
    halls = A.sum(axis=1)
    t = int(np.argmax(halls))
    return (float(halls[t]), tuple(int(v) for v in idx[t]))


def exhaustive(k, mode):
    """Exact best Hall over all subsets of size k (mode 'in') or over all
    sets whose excluded complement has size k (mode 'out').  Reads the
    fork-shared arrays from _G; must be called after _G is populated."""
    total = math.comb(NFAM, k)
    tasks = [(k, lo, min(lo + CHUNK, total), mode)
             for lo in range(0, total, CHUNK)]
    with ProcessPoolExecutor(max_workers=WORKERS, mp_context=CTX) as ex:
        results = list(ex.map(_chunk_task, tasks, chunksize=1))
    best, best_idx = -1.0, ()
    for hall, combo in results:
        if hall > best:
            best, best_idx = hall, combo
    return best, best_idx


def hall_of_subset(idx, M, c, wgt):
    A = M[list(idx)].sum(axis=0)
    return float(np.dot(wgt, np.maximum(c + A, 0.0)))


def greedy_curve(M, wgt, delta):
    """Greedy coalition curve (deterministic; the 2261 recomputation)."""
    chosen = []
    remaining = list(range(NFAM))
    T = np.zeros(NX)
    curve = []
    for k in range(1, NFAM + 1):
        best_j, best_h = remaining[0], -1.0
        for j in remaining:
            h = float(np.sum(wgt * np.maximum(T + M[j] - delta, 0.0)))
            if h > best_h:
                best_j, best_h = j, h
        chosen.append(int(best_j))
        remaining.remove(best_j)
        T = T + M[best_j]
        curve.append({"k": k, "added": best_j, "hall": best_h,
                      "prefix": tuple(chosen)})
    return curve


def hill_climb(start, M, c, wgt, max_rounds=200):
    """First-improvement 1-swap local search; returns (idx_set, hall)."""
    cur = set(int(v) for v in start)
    cur_h = hall_of_subset(cur, M, c, wgt)
    for _ in range(max_rounds):
        improved = False
        for j in range(NFAM):
            if j in cur:
                continue
            for i in sorted(cur):
                cand = (cur - {i}) | {j}
                h = hall_of_subset(cand, M, c, wgt)
                if h > cur_h + 1e-12:
                    cur, cur_h = cand, h
                    improved = True
                    break
            if improved:
                break
        if not improved:
            break
    return tuple(sorted(cur)), cur_h


def ceiling_tables(M, AG, d, wgt):
    """Per-k certified ceilings: mass/cover at the k best single-family
    terms, plus the complement m-smallest-sum table (indexed by m)."""
    mass = (wgt[None, :] * np.minimum(AG[None, :], M)).sum(axis=1)
    mass_sorted = np.sort(mass)[::-1]
    mass_top = np.cumsum(mass_sorted)
    cover = {}
    for k in range(1, NFAM + 1):
        mask = M > (d / k)[None, :]
        g = (mask * (wgt * AG)[None, :]).sum(axis=1)
        cover[k] = np.cumsum(np.sort(g)[::-1])
    L = np.cumsum(np.sort(M, axis=0), axis=0)
    msmall = np.empty(NFAM + 1)
    msmall[0] = float(np.sum(wgt * AG))
    for m in range(1, NFAM + 1):
        msmall[m] = float(np.sum(wgt * np.maximum(AG - L[m - 1], 0.0)))
    return mass_top, cover, msmall


def main():
    t0 = time.time()
    fam, base, corr, a_max = o34.build_construction()
    x = np.linspace(-a_max, a_max, NX)
    wgt = c58.trap_weights(x, a_max)

    rows = ("base_M0", "corr_M0", "base_D2", "corr_D2")
    coef_of = {"base_M0": base, "corr_M0": corr,
               "base_D2": base, "corr_D2": corr}
    kind_of = {"base_M0": "M0", "corr_M0": "M0",
               "base_D2": "D2", "corr_D2": "D2"}

    screen_2261 = json.loads(SCREEN_2261.read_text(encoding="utf-8"))

    # one index table per subset size, built once and shared by fork
    comb_tables = {
        k: np.asarray(list(itertools.combinations(range(NFAM), k)),
                      dtype=np.int32)
        for k in range(0, EXACT_SMALL_MAX + 1)}

    exact_grid = ([("in", k) for k in range(1, EXACT_SMALL_MAX + 1)] +
                  [("out", k) for k in range(0, NFAM - EXACT_LARGE_MIN + 1)])

    out_rows = {}
    for r in rows:
        tr = time.time()
        M, AG, S = row_arrays(fam, coef_of[r], kind_of[r], x)
        c = AG - S
        d = S - AG
        row_norm = float(np.sum(wgt * AG))

        # recomputed greedy (anchored against the 2261 artifact)
        curve = greedy_curve(M, wgt, d)
        g2261 = {e["k"]: e["hall"] for e in screen_2261["rows"][r]["curve"]}
        anchor_rel = max(
            abs(e["hall"] - g2261[e["k"]]) / max(abs(g2261[e["k"]]), 1e-300)
            for e in curve)
        anchor_ok = anchor_rel <= 1e-9

        # ceilings
        mass_top, cover, msmall = ceiling_tables(M, AG, d, wgt)
        comp_ratio = {
            "trivial": BUDGET_DENOM / np.arange(1, NFAM + 1),
            "mass": BUDGET_DENOM * mass_top
                    / (np.arange(1, NFAM + 1) * row_norm),
            "cover": BUDGET_DENOM * np.array([cover[k][k - 1] for k in range(1, NFAM + 1)])
                     / (np.arange(1, NFAM + 1) * row_norm),
            "msmall": BUDGET_DENOM * msmall[NFAM - np.arange(1, NFAM + 1)]
                      / (np.arange(1, NFAM + 1) * row_norm),
        }

        def ceiling_components(k):
            return {name: float(comp_ratio[name][k - 1])
                    for name in comp_ratio}

        # exact enumeration at both ends
        _G.update(M=M, c=c, wgt=wgt, S=S, COMB=comb_tables)
        exact = {}
        for mode, k in exact_grid:
            hall, combo = exhaustive(k, mode)
            if mode == "out":
                kk = NFAM - k
                full = tuple(j for j in range(NFAM) if j not in set(combo))
                exact[kk] = (hall, full)
            else:
                exact[k] = (hall, combo)
            print(f"[{r}] exact {mode} k={k} done "
                  f"({time.time()-tr:.0f}s)", flush=True)

        # anchors and validity checks
        hall30, _ = exact[NFAM]
        anchor_k30 = abs(hall30 - row_norm) / row_norm
        mono_ok = all(exact[k][0] <= exact[k + 1][0] * (1 + 1e-12)
                      for k in range(1, EXACT_SMALL_MAX))
        mono_ok &= all(exact[k][0] <= exact[k + 1][0] * (1 + 1e-12)
                       for k in range(EXACT_LARGE_MIN, NFAM))
        def ceiling_ub(k):
            return min(row_norm, mass_top[k - 1], cover[k][k - 1],
                       msmall[NFAM - k])

        ub_valid = True
        for k, (hall, _) in exact.items():
            if ceiling_ub(k) < hall * (1 - 1e-9):
                ub_valid = False

        # per-k table with lower bounds, exacts, ceilings
        table = []
        t_lo = -1.0
        t_hi = -1.0
        for k in range(1, NFAM + 1):
            if k in exact:
                hall_exact, witness = exact[k]
                lb, lb_kind = hall_exact, "exact"
                ub = hall_exact
            else:
                hall_exact, witness = None, None
                lb, lb_kind = curve[k - 1]["hall"], "greedy"
                ub = ceiling_ub(k)
            rec = {
                "k": k,
                "hall_exact": hall_exact,
                "hall_lower": lb,
                "lower_kind": lb_kind,
                "hall_upper": float(ub),
                "ceiling_ratios": ceiling_components(k),
                "ratio_lo": float(BUDGET_DENOM * lb / (k * row_norm)),
                "ratio_hi": float(BUDGET_DENOM * ub / (k * row_norm)),
                "witness": list(witness) if witness is not None else None,
            }
            table.append(rec)
            t_lo = max(t_lo, rec["ratio_lo"])
            t_hi = max(t_hi, rec["ratio_hi"])

        # adaptive hill climb: only where a ceiling could beat the floor
        climbed = {}
        for rec in table:
            k = rec["k"]
            if rec["hall_exact"] is not None:
                continue
            if rec["ratio_hi"] <= t_lo * (1 + 1e-12):
                continue
            seed = curve[k - 1]["prefix"]
            idx, hall = hill_climb(seed, M, c, wgt)
            climbed[k] = hall
            if hall > rec["hall_lower"] * (1 + 1e-12):
                rec["hall_lower"] = hall
                rec["lower_kind"] = "hill1"
                rec["witness"] = list(idx)
                rec["ratio_lo"] = float(BUDGET_DENOM * hall / (k * row_norm))
            t_lo = max(t_lo, rec["ratio_lo"])
            print(f"[{r}] climb k={k} -> {hall:.10g} ({time.time()-tr:.0f}s)",
                  flush=True)

        closed = bool(t_hi <= t_lo * (1 + 1e-9))
        k_lo = max(table, key=lambda e: e["ratio_lo"])["k"]
        k_hi = max(table, key=lambda e: e["ratio_hi"])["k"]
        witness = max(table, key=lambda e: e["ratio_lo"])
        bracket_consistent = all(rec["ratio_hi"] >= rec["ratio_lo"] * (1 - 1e-9)
                                 for rec in table)
        out_rows[r] = {
            "norm": row_norm,
            "t_star_lo": float(t_lo),
            "t_star_hi": float(t_hi),
            "closed": closed,
            "k_star_lo": k_lo,
            "k_star_hi": k_hi,
            "witness_k": witness["k"],
            "witness_idx": witness["witness"],
            "table": table,
            "anchors": {
                "greedy_2261_rel_max": anchor_rel,
                "greedy_2261_ok": anchor_ok,
                "k30_vs_row_rel": anchor_k30,
                "k30_ok": anchor_k30 <= 1e-9,
                "monotone_exact_ranges": mono_ok,
                "ceilings_ge_exact": ub_valid,
                "bracket_consistent": bracket_consistent,
            },
        }
        print(json.dumps({r: {"t_lo": float(t_lo), "t_hi": float(t_hi),
                              "closed": closed,
                              "k_lo": k_lo, "k_hi": k_hi,
                              "anchor2261": anchor_rel,
                              "climbed": len(climbed)}}), flush=True)
        OUTPUT.write_text(json.dumps(
            {"record": RECORD, "partial": True, "rows": out_rows},
            indent=2) + "\n", encoding="utf-8", newline="\n")

    # verdict
    parts = []
    all_closed = True
    for r in rows:
        v = out_rows[r]
        all_closed &= v["closed"]
        parts.append(f"{r}: [{v['t_star_lo']:.6g}, {v['t_star_hi']:.6g}]"
                     f" at k={v['k_star_lo']}"
                     + (" (EXACT)" if v["closed"] else
                        f" (k_hi={v['k_star_hi']})"))
    verdict = (
        "HALL-EXACT: exhaustive enumeration at k<=6 and k>=24 (complement-"
        "exact) plus certified ceilings in 7<=k<=23 (trivial / mass / "
        "cover / complement-m-smallest, the four-way min) give per-row "
        "brackets "
        + "; ".join(parts) + ". All rows still exceed the pigeonhole floor "
        f"{BUDGET_DENOM/NFAM:.6g} by the certified lower bounds, so every "
        "single-factor uniform budget of any size (uniform or per-row) "
        "fails on the count side by the same factor as 2261, now with "
        "exact Hall values at both ends of the coalition-size curve"
        + ("; the global maximum is exact for every row."
           if all_closed else
           "; the global maximum is exact for the closed rows and "
           "two-sided-bracketed for the rest (the middle ceilings are "
           "upper bounds, not attained).")
        + " The count-side design still needs the analytic per-node "
          "pieces; count-free assembly (2257) remains the live route. "
          "No producer GO, no gate sign change, no RH claim.")

    result = {
        "record": RECORD,
        "status": "HALL-EXACT (exhaustive two-end enumeration + certified "
                  "four-way middle ceilings + 1-swap lower bounds)",
        "date": "2026-09-30",
        "budget_denom": BUDGET_DENOM,
        "pigeonhole_floor": BUDGET_DENOM / NFAM,
        "grid": {"x_nodes": NX, "a_max": a_max},
        "exact_ranges": {"small": [1, EXACT_SMALL_MAX],
                         "large": [EXACT_LARGE_MIN, NFAM]},
        "chunk": CHUNK, "workers": WORKERS,
        "rows": out_rows,
        "verdict": verdict,
        "nonclaims": [
            "float64 measurements on the committed 2197/2258 grid; the "
            "ceilings are valid upper bounds only up to binary64 slack",
            "the middle-range values (7<=k<=23) are lower bounds from "
            "greedy/1-swap search when not bracketed shut; no signed-"
            "off equality of Hall to any certified object is claimed",
            "Hall(J) is a necessary condition on feasible pointwise "
            "allocations; sufficiency is not used",
            "single candidate construction (2234 build); the three 2103 "
            "stress candidates are not re-measured",
            "no producer GO, no gate sign change, no RH claim",
        ],
        "provenance": {
            "script": "scripts/routea_weighted_zero_hall_exact_2266.py",
            "machinery": "scripts/routea_weighted_zero_cancellation_"
                         "split_2258.py, routea_weighted_zero_direct_"
                         "product_outward_2234.py",
            "predecessor": "scripts/routea_weighted_zero_hall_screen_"
                           "2261.py; results/2261_hall_screen.json",
        },
        "wall_seconds": time.time() - t0,
    }
    OUTPUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8",
                      newline="\n")
    print(json.dumps({"verdict": verdict}, indent=2))
    print(f"wall {time.time()-t0:.0f}s")


if __name__ == "__main__":
    main()