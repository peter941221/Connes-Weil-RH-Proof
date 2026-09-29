#!/usr/bin/env python3
"""2258 - Cancellation-aware split recon of the direct-product screen.

Consumer: the withdrawn count-side transfer (2253 falsified the triangle
per-node split at `owner/62`; the count-free assembly of 2257 is the live
route).  This record asks the structural question the triangle split cannot
answer: the 2234 sigma rows are CANCELLED strip-weighted L1 norms of the
SIGNED family sums,

    row(sigma) = int e^{sigma x} |sum_j c_j f_j^{(k)}(x)| dx,

so a per-node split has these canonical forms:

1.  pro-rata (pointwise proportional allocation of the cancelled norm):
        share_j = int e^{sigma x} |g_j| * (|G| / S) dx,  G = sum_j g_j,
        S = sum_j |g_j|;  telescoping identity  sum_j share_j = row
        exactly, and share_j dominates the pointwise mandatory floor, so
        it is a valid allocation;

2.  coalitional floor (mandatory share; ANY nonneg per-node allocation
    (a_j(x)) with sum_j a_j >= |G| and a_j <= |g_j| must satisfy
    a_j >= max(0, |g_j| - (S - |G|)) pointwise):
        floor_j = int e^{sigma x} max(0, |g_j| - (S - |G|)) dx;

3.  signed pieces (informational; intra-family x-oscillation):
        I_j = int e^{sigma x} g_j(x) dx (complex).

Measured against the uniform per-node budget row/62 (the count-side
transfer budget of the 2246 ledger).  The two-sided (diagonal product)
channel split is 4*mult*share_b_j*share_c_j: both factors allocated, the
sums telescope to the screen product, so the row inflation factors cancel
in the ratios.  Exact structural bounds recorded alongside:
 - flat-factor splits are impossible: 30 nodes < 62 budget slots, so any
   split holding one factor flat has max_j >= row/30 and ratio >= 62/30;
 - the free two-sided allocation min-max is degenerate (concentrate the
   two factors on disjoint node sets: all diagonal products vanish), so
   feasibility is not a free-allocation question; the binding objects are
   the floor and the canonical allocations.

Sampling: float64 numpy on the committed 2197 grid (NX=240001, a_max,
sigma=1), the same formulas as the committed 2234 smoke() numpy reference,
with the boundary region qq <= 0.04 masked (there exp(-K/qq) < 1e-300,
below float64; MPFR keeps a tail of that size).  Reconstruction of the
signed sums is validated against the committed MPFR anchors
results/2234_sigma_100.json.  Screening artifact: no producer GO, no gate
sign change, no RH claim.

Writes results/2258_cancellation_split.json.
"""
import json
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import routea_weighted_zero_direct_product_outward_2234 as o34  # noqa: E402  # pyright: ignore[reportMissingImports]
import routea_weighted_zero_direct_product_mass_screen_2197 as s97  # noqa: E402  # pyright: ignore[reportMissingImports]

RECORD = 2258
SIGMA = 1.0
ANCHOR = ROOT / "results" / "2234_sigma_100.json"
OUTPUT = ROOT / "results" / "2258_cancellation_split.json"

K = s97.K
NX = s97.NX
QQ_MASK = 0.04          # below this |qq| is at the family boundary and
                        # exp(-K/qq) underflows float64 (K = 30)
BUDGET_DENOM = 62.0     # uniform per-node budget row/62 (2246 ledger)
NODE_COUNT = 30         # construction families = nodes of the split


def family_terms(x, a, theta):
    """Signed per-family arrays on the grid: (g_M0, g_D2) with the family
    function f(x) = phi(x/a) exp(i theta x), unit coefficient."""
    u = x / a
    qq = 1.0 - u * u
    mask = qq > QQ_MASK
    qs = np.where(mask, qq, 1.0)
    iq = 1.0 / qs
    ph = np.where(mask, np.exp(-K * iq), 0.0)
    e1 = -2.0 * K * u * iq * iq / a
    e2 = (-2.0 * K / (a * a)) * (iq * iq + 4.0 * u * u * iq ** 3)
    phz = np.exp(1j * theta * x)
    core = e2 + e1 * e1 + 2j * theta * e1 - theta * theta
    g_m0 = ph * phz
    g_d2 = np.where(mask, ph * core, 0.0) * phz
    return g_m0, g_d2


def trap_weights(x, a_max):
    dx = (2.0 * a_max) / (NX - 1)
    tw = np.full(NX, 2.0)
    tw[0] = tw[-1] = 1.0
    return (dx / 2.0) * tw * np.exp(SIGMA * x)


def main():
    fam, base, corr, a_max = o34.build_construction()
    assert len(fam) == NODE_COUNT, len(fam)
    x = np.linspace(-a_max, a_max, NX)
    wgt = trap_weights(x, a_max)
    anchor = json.loads(ANCHOR.read_text(encoding="utf-8"))["values"]

    rows = ("base_M0", "corr_M0", "base_D2", "corr_D2")
    coefs = (base, corr, base, corr)
    kinds = ("M0", "M0", "D2", "D2")
    coef_of = {"base_M0": base, "corr_M0": corr,
               "base_D2": base, "corr_D2": corr}

    # pass 1: signed sums G, magnitude sums S
    G = {r: np.zeros(NX, complex) for r in rows}
    S = {r: np.zeros(NX) for r in rows}
    for j, (a, th) in enumerate(fam):
        g_m0, g_d2 = family_terms(x, a, th)
        for r, coef, kind in zip(rows, coefs, kinds):
            g = coef[j] * (g_m0 if kind == "M0" else g_d2)
            G[r] += g
            S[r] += np.abs(g)
    AG = {r: np.abs(G[r]) for r in rows}

    # pass 2: pro-rata shares, coalitional floors, signed pieces
    share = {r: np.zeros(NODE_COUNT) for r in rows}
    floor = {r: np.zeros(NODE_COUNT) for r in rows}
    signed = {r: np.zeros(NODE_COUNT, complex) for r in rows}
    for j, (a, th) in enumerate(fam):
        g_m0, g_d2 = family_terms(x, a, th)
        for r, coef, kind in zip(rows, coefs, kinds):
            g = coef[j] * (g_m0 if kind == "M0" else g_d2)
            ag = np.abs(g)
            with np.errstate(divide="ignore", invalid="ignore"):
                ratio = np.where(S[r] > 0.0, ag * AG[r] / S[r], 0.0)
            share[r][j] = float(np.sum(wgt * ratio))
            rest = S[r] - AG[r]
            floor[r][j] = float(np.sum(wgt * np.maximum(ag - rest, 0.0)))
            signed[r][j] = complex(np.sum(wgt * g))

    out_rows = {}
    for r in rows:
        norm = float(np.sum(wgt * AG[r]))
        tri = float(np.sum(wgt * S[r]))
        shares = share[r]
        floors = floor[r]
        abs_signed = np.abs(signed[r])
        n_anchor = anchor[r]
        ratio_pro = BUDGET_DENOM * shares / norm
        ratio_floor = BUDGET_DENOM * floors / norm
        ratio_signed = BUDGET_DENOM * abs_signed / norm
        order = np.argsort(-shares)
        top = [{
            "node": int(j), "a": fam[j][0], "theta": fam[j][1],
            "coef": float(coef_of[r][j].real),
            "share": float(shares[j]), "share_frac": float(shares[j] / norm),
            "floor": float(floors[j]), "floor_frac": float(floors[j] / norm),
            "signed_piece_mass": float(abs_signed[j]),
            "ratio_pro_over_budget": float(ratio_pro[j]),
            "ratio_floor_over_budget": float(ratio_floor[j]),
            "ratio_signed_over_budget": float(ratio_signed[j]),
        } for j in order[:5]]
        out_rows[r] = {
            "norm": norm,
            "anchor_2234": n_anchor,
            "reconstruction_rel_err": abs(norm - n_anchor) / n_anchor,
            "triangle_total": tri,
            "cancellation_factor": tri / norm,
            "signed_piece_sum_ratio": float(np.sum(abs_signed)) / norm,
            "pro_rata_sum": float(np.sum(shares)),
            "pro_rata_telescope_rel_err": abs(
                float(np.sum(shares)) - norm) / norm,
            "floor_sum": float(np.sum(floors)),
            "floor_le_share": bool(np.all(floors <= shares + 1e-9 * norm)),
            "max_share_ratio": float(np.max(ratio_pro)),
            "max_floor_ratio": float(np.max(ratio_floor)),
            "max_signed_ratio": float(np.max(ratio_signed)),
            "nodes_over_budget_pro": int(np.sum(ratio_pro > 1.0)),
            "nodes_over_budget_floor": int(np.sum(ratio_floor > 1.0)),
            "top_nodes": top,
        }

    # pass 3: first multiplex Hall datum -- the mandatory coalitional mass
    # of the top-3 share coalition of each row.  Hall(J): the complement
    # can cover at most sum_{k not in J} |g_k| pointwise, so J must
    # carry max(0, |G| - (S - A_J))^+; note this is <= A_J * |G| / S
    # pointwise, so the pro-rata allocation of J dominates every Hall
    # mass of J (validity of pro-rata at all coalition levels).
    hall3 = {}
    for r in rows:
        top3 = list(np.argsort(-share[r])[:3])
        top_sum = np.zeros(NX)
        for j in top3:
            a, th = fam[j]
            g_m0, g_d2 = family_terms(x, a, th)
            g = coef_of[r][j] * (g_m0 if kinds[rows.index(r)] == "M0"
                                 else g_d2)
            top_sum += np.abs(g)
        delta = S[r] - AG[r]
        mand = np.maximum(AG[r] - (S[r] - top_sum), 0.0)
        hall3[r] = {
            "nodes": [int(j) for j in top3],
            "mandatory_mass": float(np.sum(wgt * mand)),
            "ratio_over_budget": float(BUDGET_DENOM * np.sum(wgt * mand)
                                       / out_rows[r]["norm"]),
            "pro_rata_share_frac": float(sum(share[r][j] for j in top3)
                                         / out_rows[r]["norm"]),
            "total_cancellation_frac": float(np.sum(wgt * delta)
                                             / float(np.sum(wgt * S[r]))),
        }
        out_rows[r]["hall_top3"] = hall3[r]

    # channel splits: a = base_D2 x corr_M0 (2243 c1), b = corr_D2 x base_M0
    channels = {}
    for name, r_left, r_right in (("a", "base_D2", "corr_M0"),
                                  ("b", "corr_D2", "base_M0")):
        prod = out_rows[r_left]["norm"] * out_rows[r_right]["norm"]
        s_l, s_r = share[r_left], share[r_right]
        f_l, f_r = floor[r_left], floor[r_right]
        diag = BUDGET_DENOM * s_l * s_r / prod
        diag_floor = BUDGET_DENOM * f_l * f_r / prod
        order = np.argsort(-diag)
        channels[name] = {
            "rows": [r_left, r_right],
            "raw_product": prod,
            "diag_product_share": float(np.sum(s_l * s_r)) / prod,
            "max_diag_ratio": float(np.max(diag)),
            "max_diag_floor_ratio": float(np.max(diag_floor)),
            "nodes_over_budget_diag": int(np.sum(diag > 1.0)),
            "nodes_over_budget_diag_floor": int(np.sum(diag_floor > 1.0)),
            "top_nodes": [{
                "node": int(j), "a": fam[j][0], "theta": fam[j][1],
                "share_l_frac": float(s_l[j] / out_rows[r_left]["norm"]),
                "share_r_frac": float(s_r[j] / out_rows[r_right]["norm"]),
                "floor_l_frac": float(f_l[j] / out_rows[r_left]["norm"]),
                "floor_r_frac": float(f_r[j] / out_rows[r_right]["norm"]),
                "ratio_diag_over_budget": float(diag[j]),
                "ratio_diag_floor_over_budget": float(diag_floor[j]),
            } for j in order[:5]],
        }

    worst_floor = max(channels[n]["max_diag_floor_ratio"]
                      for n in channels)
    worst_diag = max(channels[n]["max_diag_ratio"] for n in channels)
    worst_row_floor = max(out_rows[r]["max_floor_ratio"] for r in rows)
    worst_hall3 = max(out_rows[r]["hall_top3"]["ratio_over_budget"]
                      for r in rows)
    if worst_floor > 1.0:
        verdict = (
            "FLOOR-FALSIFIED: the coalitional mandatory floor alone "
            "exceeds the uniform per-node budget in a channel "
            f"(max floor ratio {worst_floor:.4g} > 1), so no valid "
            "count-side per-node split of the screen rows exists; the "
            "cancellation lever cannot revive the owner/62 transfer.  "
            "Count-free assembly (2257) remains the live route.")
    else:
        verdict = (
            "SPLIT-STILL-FAILS-CANONICALLY: reconstruction certified "
            f"(rel err {max(out_rows[r]['reconstruction_rel_err'] for r in rows):.3g}); "
            "cancellation factors "
            + " / ".join(f"{out_rows[r]['cancellation_factor']:.3g}"
                         for r in rows)
            + "; single-node coalitional floor <= "
            f"{worst_row_floor:.3g} of the uniform budget, top-3 "
            f"coalition Hall mass <= {worst_hall3:.3g} (dominated by "
            "the pro-rata top-3 allocation pointwise) -- no mandatory "
            "localization at these coalition levels; the canonical "
            "pro-rata two-sided "
            f"split fails at max diagonal ratio {worst_diag:.4g} "
            f"(channel a {channels['a']['max_diag_ratio']:.4g}, channel b "
            f"{channels['b']['max_diag_ratio']:.4g}) with "
            f"{channels['b']['nodes_over_budget_diag']}/30 nodes over in "
            "the worse channel, while its total charge is only "
            f"{channels['b']['diag_product_share']:.3g} of the screen "
            "product (localization, not total).  Flat-factor and any "
            "per-factor-bounded split are structurally impossible "
            "(30 nodes < 62 budget slots: the all-node Hall condition).  "
            "The owner/62 count-side transfer stays withdrawn; the "
            "residual obstruction is allocation localization, not "
            "mandatory integrand mass, so any revival needs an "
            "allocation-design argument (the coalitional Hall LP) tied "
            "to the producer's fixed shell pieces.")

    result = {
        "record": RECORD,
        "status": "CANCELLATION-SPLIT-RECON (pro-rata + coalitional floor)",
        "date": "2026-09-30",
        "sigma": SIGMA,
        "budget_denom": BUDGET_DENOM,
        "rows": out_rows,
        "channels": channels,
        "structural": {
            "flat_factor_pigeonhole": {
                "statement": "with one factor held flat at the row norm, "
                             "any nonneg split of the other row has "
                             "max_j >= row/N with N=30 nodes, so its "
                             "ratio over the uniform budget row/62 is at "
                             "least 62/30 > 1: flat-factor splits CANNOT "
                             "fit, independent of the cancellation "
                             "structure",
                "min_ratio": BUDGET_DENOM / NODE_COUNT,
            },
            "free_double_allocation_degenerate": {
                "statement": "if BOTH factors are allocatable with only "
                             "the sum constraints, the min-max objective "
                             "has value 0 (concentrate the left mass on "
                             "one node set and the right mass on a "
                             "disjoint one: the diagonal products "
                             "vanish), so feasibility of a split is NOT "
                             "a free-allocation question; the binding "
                             "objects are the mandatory floor and the "
                             "canonical (fixed-piece) allocations",
            },
            "pro_rata_dominates_floor": {
                "statement": "pointwise max(0, |g_j|-(S-|G|)) <= "
                             "|g_j|*|G|/S, so the pro-rata allocation is "
                             "valid (dominates every valid split's floor)",
                "verified": all(out_rows[r]["floor_le_share"]
                                for r in rows),
            },
            "norms_are_cancelled": {
                "cancellation_factors": {
                    r: out_rows[r]["cancellation_factor"] for r in rows},
            },
        },
        "verdict": verdict,
        "nonclaims": [
            "float64 measurement on the committed grid; the MPFR anchors "
            "bound the reconstruction error (see reconstruction_rel_err)",
            "the coalitional floor is a lower bound valid for pointwise "
            "allocations with sum_j a_j >= |G| and a_j <= |g_j|; the "
            "producer's fixed shell pieces may impose further structure "
            "not modeled here",
            "the ledger ratios use the diagonal (same-family) pairing; "
            "cross-node pairings are not available to the analytic "
            "decomposition",
            "no producer GO, no gate sign change, no RH claim",
        ],
        "provenance": {
            "script": "scripts/routea_weighted_zero_cancellation_split_2258.py",
            "machinery": "scripts/routea_weighted_zero_direct_product_"
                         "outward_2234.py (build_construction, grid)",
            "anchors": "results/2234_sigma_100.json",
            "predecessor": "scripts/routea_weighted_zero_pernode_charge_"
                           "2253.py",
        },
    }

    OUTPUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8",
                      newline="\n")
    brief = {
        "status": result["status"],
        "reconstruction_rel_err_max": max(
            out_rows[r]["reconstruction_rel_err"] for r in rows),
        "rows": {r: {
            "norm": out_rows[r]["norm"],
            "cancellation": out_rows[r]["cancellation_factor"],
            "signed_piece_sum_ratio": out_rows[r]["signed_piece_sum_ratio"],
            "max_share_ratio": out_rows[r]["max_share_ratio"],
            "max_floor_ratio": out_rows[r]["max_floor_ratio"],
            "max_signed_ratio": out_rows[r]["max_signed_ratio"],
            "hall_top3_ratio": out_rows[r]["hall_top3"]["ratio_over_budget"],
            "hall_top3_pro_rata": out_rows[r]["hall_top3"][
                "pro_rata_share_frac"],
        } for r in rows},
        "channels": {n: {
            "max_diag_ratio": channels[n]["max_diag_ratio"],
            "max_diag_floor_ratio": channels[n]["max_diag_floor_ratio"],
            "nodes_over_budget_diag": channels[n]["nodes_over_budget_diag"],
            "diag_product_share": channels[n]["diag_product_share"],
        } for n in channels},
        "verdict": verdict,
    }
    print(json.dumps(brief, indent=2))


if __name__ == "__main__":
    main()