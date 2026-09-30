#!/usr/bin/env python3
"""2269 - Ball-grade Hall quantities for the four direct-product rows.

Records 2261/2266 produced the Hall brackets [t*_lo, t*_hi] of the four
direct-product rows (base_M0, corr_M0, base_D2, corr_D2) in float64:  the
lower bound from the argmax coalition Hall(J) = int w (AG - sum_{j not in
J} M_j)^+ (the 2266 convention: the witness list indexes J, and the
COMPLEMENT's family magnitudes are deducted), the upper bound from the
per-k ceilings with the complement-m-smallest
component msmall[m] = int w (AG - L_m)^+ (L_m = pointwise sum of the m
smallest family magnitudes) binding at the decisive k for every row.
This record re-runs the 2262 directed-MPFR node machinery and ball-izes
exactly those quantities:

  witness coalition Hall       [hall_lo, hall_hi]
  full msmall table (m = 1..30) [ms_l[m], ms_u[m]]
  row norm                     [norm_lo, norm_hi]

Per node x the 2262 `family_step` yields certified float64 intervals for
every (row, family) magnitude and the per-node signed row sums give the AG
interval via the same PAD law.  Aggregations use the 2262 one-sided guards
(up_sum/up_prod vs lo_sum/lo_prod); the m-smallest cumulative sums use the
sorted-domination law (sorted(lb)[i] <= sorted(true)[i] <= sorted(ub)[i]
pointwise).  The certified bracket

  [BUDGET * hall_lo / (k_w * norm_hi),
   max_k min(BUDGET / k, BUDGET * ms_u[30 - k] / (k * norm_lo))]

is a valid two-sided bracket for t*_true: the lower side is a certified
coalition ratio; the upper side is a certified ceiling at every k
(msmall alone is one of the four 2266 ceiling components, so it is a valid
upper bound at every k without re-certifying the other three).

Anchors: mask diagnostics identical to the 2262 standard (zero
disagreements, positive margin); the recomputed norm/triangle/wsum merge
against the 2262 artifact; every 2269 bracket contains the corresponding
2266 float64 reading within a relative 1e-9 slack.

Writes results/2269_hall_ball.json from results/2269_chunk_{k}.json
(removed after a clean reduce).

Run: python3 script.py            (spawns NCHUNK workers, then reduces)
     python3 script.py chunk K    (single chunk, used internally)
     python3 script.py reduce     (reduce existing chunks)
"""
import ctypes as C
import json
import math
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import routea_weighted_zero_cancellation_split_2258 as c58  # noqa: E402  # pyright: ignore[reportMissingImports]
import routea_weighted_zero_direct_product_outward_2234 as o34  # noqa: E402  # pyright: ignore[reportMissingImports]
import routea_weighted_zero_cancellation_split_ball_2262 as b62  # noqa: E402  # pyright: ignore[reportMissingImports]

RECORD = 2269
R = ROOT / "results"
OUTPUT = R / "2269_hall_ball.json"
ANCHOR_2266 = R / "2266_hall_exact.json"
ANCHOR_2262 = R / "2262_cancellation_split_directed.json"
NCHUNK = 12
NFAM = 30
BUDGET = c58.BUDGET_DENOM
NX = c58.NX
NODE_COUNT = c58.NODE_COUNT
ROWS = b62.ROWS
ROW_ACC = b62.ROW_ACC
lib = o34.lib
M = o34.M
RNDN = o34.RNDN
up_pad = b62.up_pad
lo_pad = b62.lo_pad
up_sum = b62.up_sum
lo_sum = b62.lo_sum
up_prod = b62.up_prod
lo_prod = b62.lo_prod
family_step = b62.family_step


def witness_data():
    rec = json.loads(ANCHOR_2266.read_text(encoding="utf-8"))
    out = {}
    for r in ROWS:
        idx = tuple(rec["rows"][r]["witness_idx"])
        comp = tuple(j for j in range(NFAM) if j not in set(idx))
        out[r] = {"k": rec["rows"][r]["witness_k"], "idx": idx, "comp": comp}
    return out


def chunk_worker(k, nchunk, wit):
    fam, base, corr, a_max = o34.build_construction()
    x = o34.x_grid(a_max)
    n = x.shape[0]
    i0 = (n * k) // nchunk
    i1 = (n * (k + 1)) // nchunk
    dxf = (2.0 * a_max) / (NX - 1)
    wb = o34.WB(96)
    acc = [M() for _ in range(8)]
    e_in = M()
    e_out = M()
    fam_par = [(a, th, complex(bc), complex(cc))
               for (a, th), bc, cc in zip(fam, base, corr)]
    cms = [(up_pad(abs(bc)), lo_pad(abs(bc)),
            up_pad(abs(cc)), lo_pad(abs(cc)))
           for (_, _), bc, cc in zip(fam, base, corr)]
    norm_u = [0.0] * 4
    norm_l = [0.0] * 4
    tri_u = [0.0] * 4
    tri_l = [0.0] * 4
    hall_u = [0.0] * 4
    hall_l = [0.0] * 4
    ms_u = [[0.0] * (NFAM + 1) for _ in range(4)]
    ms_l = [[0.0] * (NFAM + 1) for _ in range(4)]
    wsum_u = 0.0
    wsum_l = 0.0
    diag = [0, 0, math.inf, 0, 0]
    mvals = [0.0] * 8
    mb0u = [0.0] * NODE_COUNT
    mb0l = [0.0] * NODE_COUNT
    mc0u = [0.0] * NODE_COUNT
    mc0l = [0.0] * NODE_COUNT
    mb2u = [0.0] * NODE_COUNT
    mb2l = [0.0] * NODE_COUNT
    mc2u = [0.0] * NODE_COUNT
    mc2l = [0.0] * NODE_COUNT
    for i in range(i0, i1):
        xv = float(x[i])
        tw = 1.0 if (i == 0 or i == n - 1) else 2.0
        lib.mpfr_set_d(C.byref(e_in.x), C.c_double(xv), RNDN)
        lib.mpfr_exp(C.byref(e_out.x), C.byref(e_in.x), RNDN)
        e_f = e_out.get_d(RNDN)
        w_u = up_prod((dxf / 2.0) * tw, up_pad(e_f))
        w_l = lo_prod((dxf / 2.0) * tw, lo_pad(e_f))
        wsum_u = up_sum(wsum_u, w_u)
        wsum_l = lo_sum(wsum_l, w_l)
        for o in acc:
            lib.mpfr_set_d(C.byref(o.x), C.c_double(0.0), RNDN)
        for j, fam_j in enumerate(fam_par):
            family_step(wb, xv, fam_j, cms[j], mvals, acc, diag)
            mb0u[j], mb0l[j] = mvals[0], mvals[1]
            mc0u[j], mc0l[j] = mvals[2], mvals[3]
            mb2u[j], mb2l[j] = mvals[4], mvals[5]
            mc2u[j], mc2l[j] = mvals[6], mvals[7]
        m_u = (mb0u, mc0u, mb2u, mc2u)
        m_l = (mb0l, mc0l, mb2l, mc2l)
        for r in range(4):
            s_u = 0.0
            s_l = 0.0
            for j in range(NODE_COUNT):
                s_u = up_sum(s_u, m_u[r][j])
                s_l = lo_sum(s_l, m_l[r][j])
            ri, ii = ROW_ACC[r]
            h_f = math.hypot(acc[ri].get_d(RNDN), acc[ii].get_d(RNDN))
            ag_u = up_pad(h_f)
            ag_l = lo_pad(h_f)
            norm_u[r] = up_sum(norm_u[r], up_prod(w_u, ag_u))
            norm_l[r] = lo_sum(norm_l[r], lo_prod(w_l, ag_l))
            tri_u[r] = up_sum(tri_u[r], up_prod(w_u, s_u))
            tri_l[r] = lo_sum(tri_l[r], lo_prod(w_l, s_l))
            # Hall(J) = int w (AG - sum_{j not in J} M_j)^+ : the 2266
            # coalition convention deducts the COMPLEMENT of the witness.
            cl_u = 0.0
            cl_l = 0.0
            for j in wit[ROWS[r]]["comp"]:
                cl_u = up_sum(cl_u, m_u[r][j])
                cl_l = lo_sum(cl_l, m_l[r][j])
            t_u = up_sum(ag_u, -cl_l)
            if t_u > 0.0:
                hall_u[r] = up_sum(hall_u[r], up_prod(w_u, t_u))
            t_l = lo_sum(ag_l, -cl_u)
            if t_l > 0.0:
                hall_l[r] = lo_sum(hall_l[r], lo_prod(w_l, t_l))
            su_sorted = sorted(m_u[r][:NODE_COUNT])
            sl_sorted = sorted(m_l[r][:NODE_COUNT])
            cum_lo = 0.0
            cum_hi = 0.0
            for m in range(1, NFAM + 1):
                cum_lo = lo_sum(cum_lo, sl_sorted[m - 1])
                t2_u = up_sum(ag_u, -cum_lo)
                if t2_u > 0.0:
                    ms_u[r][m] = up_sum(ms_u[r][m], up_prod(w_u, t2_u))
                cum_hi = up_sum(cum_hi, su_sorted[m - 1])
                t2_l = lo_sum(ag_l, -cum_hi)
                if t2_l > 0.0:
                    ms_l[r][m] = lo_sum(ms_l[r][m], lo_prod(w_l, t2_l))
    out = {
        "chunk": k, "i0": i0, "i1": i1, "nchunk": nchunk,
        "norm_u": norm_u, "norm_l": norm_l,
        "tri_u": tri_u, "tri_l": tri_l,
        "hall_u": hall_u, "hall_l": hall_l,
        "ms_u": ms_u, "ms_l": ms_l,
        "wsum_u": wsum_u, "wsum_l": wsum_l,
        "diag": {"active_pairs": diag[0], "masked_pairs": diag[1],
                 "min_mask_margin": diag[2], "mask_disagreements": diag[3],
                 "mask_undecided": diag[4]},
    }
    (R / f"2269_chunk_{k}.json").write_text(
        json.dumps(out) + "\n", encoding="utf-8", newline="\n")
    print(json.dumps({"chunk": k, "nodes": i1 - i0, "diag": out["diag"]}),
          flush=True)


def reduce_chunks(nchunk, wit):
    rec66 = json.loads(ANCHOR_2266.read_text(encoding="utf-8"))
    rec62 = json.loads(ANCHOR_2262.read_text(encoding="utf-8"))
    parts = [json.loads((R / f"2269_chunk_{k}.json").read_text(
        encoding="utf-8")) for k in range(nchunk)]
    norm_u = [0.0] * 4
    norm_l = [0.0] * 4
    tri_u = [0.0] * 4
    tri_l = [0.0] * 4
    hall_u = [0.0] * 4
    hall_l = [0.0] * 4
    ms_u = [[0.0] * (NFAM + 1) for _ in range(4)]
    ms_l = [[0.0] * (NFAM + 1) for _ in range(4)]
    wsum_u = 0.0
    wsum_l = 0.0
    diag = {"active_pairs": 0, "masked_pairs": 0, "min_mask_margin": math.inf,
            "mask_disagreements": 0, "mask_undecided": 0}
    for p in parts:
        for r in range(4):
            norm_u[r] = up_sum(norm_u[r], p["norm_u"][r])
            norm_l[r] = lo_sum(norm_l[r], p["norm_l"][r])
            tri_u[r] = up_sum(tri_u[r], p["tri_u"][r])
            tri_l[r] = lo_sum(tri_l[r], p["tri_l"][r])
            hall_u[r] = up_sum(hall_u[r], p["hall_u"][r])
            hall_l[r] = lo_sum(hall_l[r], p["hall_l"][r])
            for m in range(NFAM + 1):
                ms_u[r][m] = up_sum(ms_u[r][m], p["ms_u"][r][m])
                ms_l[r][m] = lo_sum(ms_l[r][m], p["ms_l"][r][m])
        wsum_u = up_sum(wsum_u, p["wsum_u"])
        wsum_l = lo_sum(wsum_l, p["wsum_l"])
        d = p["diag"]
        diag["active_pairs"] += d["active_pairs"]
        diag["masked_pairs"] += d["masked_pairs"]
        diag["min_mask_margin"] = min(diag["min_mask_margin"],
                                      d["min_mask_margin"])
        diag["mask_disagreements"] += d["mask_disagreements"]
        diag["mask_undecided"] += d["mask_undecided"]

    rows_out = {}
    contains_ok = True
    for r in ROWS:
        i = ROWS.index(r)
        k_w = wit[r]["k"]
        rec_r = rec66["rows"][r]
        norm_2266 = rec_r["norm"]
        norm_ok = (norm_l[i] <= norm_2266 * (1 + 1e-9)
                   and norm_u[i] >= norm_2266 * (1 - 1e-9))
        tab = {e["k"]: e for e in rec_r["table"]}
        e_lo = tab[k_w]
        hall_2266 = e_lo["ratio_lo"] * k_w * rec_r["norm"] / BUDGET
        hall_rel = {"lo_over_2266": (hall_l[i] - hall_2266) / hall_2266,
                    "hi_over_2266": (hall_u[i] - hall_2266) / hall_2266}
        ratio_lo_cert = BUDGET * hall_l[i] / (k_w * norm_u[i])
        best_hi = 0.0
        best_k = None
        for k in range(1, NFAM + 1):
            m = NFAM - k
            if m == 0:
                u_k = BUDGET * norm_u[i] / (k * norm_l[i])
            else:
                u_k = BUDGET * ms_u[i][m] / (k * norm_l[i])
            u_k = min(u_k, BUDGET / k)
            if u_k > best_hi:
                best_hi = u_k
                best_k = k
        ratio_hi_cert = best_hi
        contains = (ratio_lo_cert <= rec_r["t_star_lo"] * (1 + 1e-9)
                    and ratio_hi_cert >= rec_r["t_star_hi"] * (1 - 1e-9))
        contains_ok &= contains
        rows_out[r] = {
            "witness_k": k_w, "witness_size": len(wit[r]["idx"]),
            "hall": [hall_l[i], hall_u[i]],
            "hall_2266": hall_2266, "hall_rel": hall_rel,
            "msmall": {"hi": ms_u[i], "lo": ms_l[i]},
            "norm": [norm_l[i], norm_u[i]], "norm_2266": norm_2266,
            "norm_ok": norm_ok,
            "triangle": [tri_l[i], tri_u[i]],
            "ratio_lo_cert": ratio_lo_cert,
            "ratio_hi_cert": ratio_hi_cert,
            "ratio_hi_argmax_k": best_k,
            "t_2266": [rec_r["t_star_lo"], rec_r["t_star_hi"]],
            "contains_2266": contains,
        }
    anchor62 = {}
    tri_ok = True
    for r in ROWS:
        i = ROWS.index(r)
        n62 = rec62["rows"][r]["norm"]
        t62 = rec62["rows"][r]["triangle"]
        norm_in = (norm_l[i] <= n62[1] * (1 + 1e-12)
                   and norm_u[i] >= n62[0] * (1 - 1e-12))
        tri_in = (tri_l[i] <= t62[1] * (1 + 1e-12)
                  and tri_u[i] >= t62[0] * (1 - 1e-12))
        tri_ok &= norm_in and tri_in
        anchor62[r] = {"norm_in_2262": bool(norm_in),
                       "triangle_in_2262": bool(tri_in),
                       "norm_lo_delta": norm_l[i] - n62[0],
                       "tri_lo_delta": tri_l[i] - t62[0]}
    w62_lo, w62_hi = sorted(rec62["wsum"])
    wsum_ok = (abs(wsum_l - w62_lo) <= 1e-12 * abs(w62_lo)
               and abs(wsum_u - w62_hi) <= 1e-12 * abs(w62_hi))
    mask_ok = (diag["mask_disagreements"] == 0 and diag["mask_undecided"] == 0
               and diag["min_mask_margin"] > 0.0)
    hall_anchor_ok = all(abs(v) <= 1e-9 for r in ROWS
                         for v in rows_out[r]["hall_rel"].values())
    all_ok = bool(contains_ok and tri_ok and wsum_ok and mask_ok
                  and hall_anchor_ok
                  and all(rows_out[r]["norm_ok"] for r in ROWS))
    result = {
        "record": RECORD,
        "status": ("HALL-BALL-CERTIFIED" if all_ok
                   else "HALL-BALL-ANCHOR-FAIL"),
        "budget_denom": BUDGET,
        "grid": {"NX": NX, "families": NFAM, "sigma": 1.0},
        "diag": diag,
        "wsum": [wsum_l, wsum_u],
        "rows": rows_out,
        "anchor_2262": anchor62,
        "wsum_ok": bool(wsum_ok),
        "mask_ok": bool(mask_ok),
        "hall_anchor_ok": bool(hall_anchor_ok),
        "verdict": (
            "the four rows' decisive Hall quantities are ball-grade: the "
            "witness coalition Hall, the full complement-m-smallest table, "
            "and the row norm carry directed-MPFR two-sided brackets whose "
            "ratio bracket contains the 2266 float64 bracket; the certified "
            "upper uses min(62/k, 62 msmall_u[30-k]/(k norm_lo)) at every k, "
            "and the certified lower uses the stored witness coalition"),
        "nonclaims": [
            "the 2266 per-k min-of-four ceiling is not re-certified: the "
            "certified upper uses the msmall component alone at every k "
            "(valid because msmall is one of the four 2266 components), and "
            "the trivial 62/k; mass and cover stay float64-grade",
            "the certified lower bound uses only the stored 2266 witness "
            "coalition per row; the exhaustive small/large-k enumerations "
            "stay float64-grade",
            "mask decisions follow the exact 2262 semantics (MPFR q with "
            "float64-mask agreement on every (x, j) pair)",
            "no count-side revival, no allocation design, no producer GO, "
            "no gate sign change, no RH claim",
        ],
        "provenance": {
            "script": "scripts/routea_weighted_zero_hall_ball_2269.py",
            "machinery": "scripts/routea_weighted_zero_cancellation_split_"
                         "ball_2262.py family_step (same node semantics)",
            "anchor": ["results/2266_hall_exact.json",
                       "results/2262_cancellation_split_directed.json"],
        },
    }
    OUTPUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8",
                      newline="\n")
    for k in range(nchunk):
        (R / f"2269_chunk_{k}.json").unlink(missing_ok=True)
    print(json.dumps({
        "status": result["status"],
        "rows": {r: {"t_2266": rows_out[r]["t_2266"],
                     "cert": [rows_out[r]["ratio_lo_cert"],
                              rows_out[r]["ratio_hi_cert"]],
                     "contains": rows_out[r]["contains_2266"]}
                 for r in ROWS},
        "mask_ok": bool(mask_ok), "tri_ok": bool(tri_ok),
        "wsum_ok": bool(wsum_ok), "hall_anchor_ok": bool(hall_anchor_ok),
        "min_mask_margin": diag["min_mask_margin"],
    }, indent=2), flush=True)


def main():
    argv = sys.argv[1:]
    wit = witness_data()
    if argv and argv[0] == "chunk":
        chunk_worker(int(argv[1]), int(argv[2]) if len(argv) > 2 else NCHUNK,
                     wit)
        return
    if argv and argv[0] == "reduce":
        reduce_chunks(int(argv[1]) if len(argv) > 1 else NCHUNK, wit)
        return
    procs = [subprocess.Popen([sys.executable, __file__, "chunk", str(k),
                               str(NCHUNK)]) for k in range(NCHUNK)]
    codes = [p.wait() for p in procs]
    if any(c != 0 for c in codes):
        raise SystemExit(f"chunk failures: {codes}")
    reduce_chunks(NCHUNK, wit)


if __name__ == "__main__":
    main()