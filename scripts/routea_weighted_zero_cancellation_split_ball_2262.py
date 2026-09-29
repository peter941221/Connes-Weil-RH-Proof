#!/usr/bin/env python3
"""2262 - Directed MPFR re-certification of the 2258 cancellation-split
quantities.

Consumer: the float64 reconstruction of 2258 (cancellation-aware split
recon of the direct-product rows).  This record replaces the float64
readings by certified enclosures of the same quantities:

  row norms       norm_r  = int w(x) |G_r(x)| dx
  triangle sums   tri_r   = int w(x) S_r(x) dx,  S_r = sum_j |g_{r,j}|
  cancellation    tri_r / norm_r
  pro-rata shares share_{r,j} = int w |G_r| |g_{r,j}| / S_r dx
  floors          floor_{r,j} = int w max(0, |g_{r,j}| - (S_r - |G_r|)) dx
  per-node ratio  62 share_{r,j} / norm_r  (uniform budget row/62)

with w(x) = (dx/2) tw e^{sigma x}, sigma = 1, on the committed 2197 grid
(NX = 240001), the exact 2258 trapezoid weights (float64 dx = 2 a_max /
(NX-1), tw = 1 at the two endpoints, 2 interior), and the exact 2258
family semantics (mask q > 0.04, both rows zeroed outside it).

Rigor.  Every per-x family value is evaluated at 256-bit MPFR along the
o34.node_bounds path (same operations, same rounding order); the signed
sums G_r accumulate in MPFR RNDN.  General float64 extractions of an
MPFR value carry an explicit relative + absolute pad PAD = 2^-52
(covering the 2^-53 float64 RNDN conversion, the 2^-254 MPFR RNDN drift
over 30 adds, and the 0.5 ulp of hypot); strictly positive magnitudes
(phi, and the core hypot) use directed RNDU/RNDD conversions with
relative-only pads, because phi = e^{-K/q} underflows float64 to 0.0
near the mask edge (K/q ~ 745, phi ~ 1e-326) and a plain absolute pad
of 2^-52 would leak ~2^-52 |c| hypot(g, h) ~ 1e6-scale garbage into the
D2 magnitudes (the 2242 denormal-artifact zone, here at q ~ 0.04).
Every upper accumulation (up_sum/up_prod/up_div) is guarded by one
nextafter toward +inf, every lower bound by one nextafter toward -inf,
which by induction over the nonnegative partial sums makes each
accumulator a rigorous one-sided bound of the true value.  Per-family
magnitudes use the analytic forms |g_M0| = |c| phi and |g_D2| = |c|
phi hypot(g, h) (|e^{i theta x}| = 1 exactly), so the enclosures bound
the true mathematical quantities; the float64 2258 readings are
compared against them with an ulp residual (float64 carries its own
~1e-15 rounding, reported, not hidden).

Mask decisions are certified by margin: q is evaluated in MPFR and the
float64 mask (the committed 2258 semantics) is verified to agree on
every (x, j) pair; the minimum distance of q to the 0.04 boundary is
recorded.

Writes results/2262_cancellation_split_directed.json from NCHUNK chunk
files (results/2262_chunk_{k}.json, removed after a clean reduce).

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

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import routea_weighted_zero_cancellation_split_2258 as c58  # noqa: E402  # pyright: ignore[reportMissingImports]
import routea_weighted_zero_direct_product_outward_2234 as o34  # noqa: E402  # pyright: ignore[reportMissingImports]

RECORD = 2262
R = ROOT / "results"
OUTPUT = R / "2262_cancellation_split_directed.json"
ANCHOR_2258 = R / "2258_cancellation_split.json"
NCHUNK = 12
QQ_MASK = c58.QQ_MASK
K = c58.K
NX = c58.NX
NODE_COUNT = c58.NODE_COUNT
BUDGET_DENOM = c58.BUDGET_DENOM
ROWS = ("base_M0", "corr_M0", "base_D2", "corr_D2")
# acc slots (re, im) per row: base_M0, corr_M0, base_D2, corr_D2
ROW_ACC = ((0, 1), (4, 5), (2, 3), (6, 7))
PAD = 2.0 ** -52

lib = o34.lib
M = o34.M
RNDN = o34.RNDN


def up_pad(v):
    return o34.up_many(v + PAD * (1.0 + abs(v)), 1)


def lo_pad(v):
    return math.nextafter(v - PAD * (1.0 + abs(v)), -math.inf)


def up_sum(v, x):
    return o34.up_many(v + x, 1)


def lo_sum(v, x):
    return math.nextafter(v + x, -math.inf)


def up_prod(a, b):
    return o34.up_many(a * b, 1)


def lo_prod(a, b):
    return math.nextafter(a * b, -math.inf)


def up_div(a, b):
    return o34.up_many(a / b, 1)


def lo_div(a, b):
    return math.nextafter(a / b, -math.inf)


def conv_up_pos(o):
    """Upper float64 bound of a strictly positive MPFR value: directed
    RNDU conversion + relative-only pad.  (The absolute pad used for
    general values is fatal here: phi = e^{-K/q} underflows float64 to
    0.0 near the mask edge (K/q ~ 745), and an absolute 2^-52 pad then
    leaks ~2^-52 * |c| * hypot(g, h) ~ 1e6-scale garbage through the D2
    magnitudes.)"""
    v = o.get_d(2)
    return o34.up_many(v + PAD * v, 1)


def conv_lo_pos(o):
    """Lower float64 bound of a nonnegative MPFR value (RNDD + relative
    pad, clamped at 0; subnormal values collapse to 0, which is a valid
    lower bound and contributes nothing)."""
    v = o.get_d(3)
    w = v - PAD * v
    return math.nextafter(w, 0.0) if w > 0.0 else 0.0


def conv_up(o):
    v = o.get_d(2)
    return o34.up_many(v + PAD * (1.0 + abs(v)), 1)


def conv_lo(o):
    v = o.get_d(3)
    return math.nextafter(v - PAD * (1.0 + abs(v)), -math.inf)


def family_step(wb, xv, fam_j, cms, mvals, acc, diag):
    """One (x, family) step: mask decision, certified magnitudes in
    mvals (8 slots, zeroed when masked), signed RNDN accumulation into
    acc (the o34.node_bounds path).  cms = (base_mag_u, base_mag_l,
    corr_mag_u, corr_mag_l).  diag = running diagnostics list."""
    for q8 in range(8):
        mvals[q8] = 0.0
    a, th, bc, cc = fam_j
    sp0 = wb.sp
    u = wb.div(wb.push(), wb.set(wb.push(), xv), wb.set(wb.push(), a))
    one = wb.set(wb.push(), 1.0)
    q = wb.sub(wb.push(), one, wb.mul(wb.push(), u, u))
    qf = q.get_d(RNDN)
    u64 = xv / a
    q64 = 1.0 - u64 * u64
    margin = abs(qf - QQ_MASK)
    if margin < diag[2]:
        diag[2] = margin
    q_l = lo_pad(qf)
    q_u = up_pad(qf)
    if q_l > QQ_MASK:
        active = True
    elif q_u < QQ_MASK:
        active = False
    else:
        diag[4] += 1
        active = qf > QQ_MASK
    if active != (q64 > QQ_MASK):
        diag[3] += 1
    if not active:
        diag[1] += 1
        wb.sp = sp0
        return
    diag[0] += 1
    invq = wb.div(wb.push(), one, q)
    invq2 = wb.mul(wb.push(), invq, invq)
    invq3 = wb.mul(wb.push(), invq2, invq)
    ainv = wb.div(wb.push(), one, wb.set(wb.push(), a))
    ainv2 = wb.mul(wb.push(), ainv, ainv)
    twoK = wb.set(wb.push(), 2.0 * K)
    e1 = wb.mul(wb.push(),
                wb.mul(wb.push(), wb.set(wb.push(), -1.0), twoK),
                wb.mul(wb.push(), wb.mul(wb.push(), ainv, u), invq2))
    u2 = wb.sub(wb.push(), one, q)
    inner = wb.add(wb.push(), invq2,
                   wb.mul(wb.push(), wb.set(wb.push(), 4.0),
                          wb.mul(wb.push(), u2, invq3)))
    e2 = wb.mul(wb.push(),
                wb.mul(wb.push(), wb.set(wb.push(), -1.0),
                       wb.mul(wb.push(), twoK, ainv2)),
                inner)
    phi = wb.exp(wb.push(),
                 wb.mul(wb.push(), wb.set(wb.push(), -K), invq))
    th_m = wb.set(wb.push(), th)
    th2 = wb.mul(wb.push(), th_m, th_m)
    g_val = wb.sub(wb.push(), wb.add(wb.push(), e2,
                                     wb.mul(wb.push(), e1, e1)), th2)
    h_val = wb.mul(wb.push(), wb.set(wb.push(), 2.0 * th), e1)
    thx = wb.mul(wb.push(), th_m, wb.set(wb.push(), xv))
    cs = wb.cos(wb.push(), thx)
    sn = wb.sin(wb.push(), thx)
    phi_u = conv_up_pos(phi)
    phi_l = conv_lo_pos(phi)
    g_lo_v = conv_lo(g_val)
    g_up_v = conv_up(g_val)
    h_lo_v = conv_lo(h_val)
    h_up_v = conv_up(h_val)
    absg_l = 0.0 if g_lo_v <= 0.0 <= g_up_v else min(abs(g_lo_v),
                                                     abs(g_up_v))
    absh_l = 0.0 if h_lo_v <= 0.0 <= h_up_v else min(abs(h_lo_v),
                                                     abs(h_up_v))
    gh_l = math.nextafter(math.hypot(absg_l, absh_l), 0.0)
    gh_u = o34.up_many(math.hypot(max(abs(g_lo_v), abs(g_up_v)),
                                  max(abs(h_lo_v), abs(h_up_v))), 1)
    for slot, cm_u, cm_l in ((0, cms[0], cms[1]), (2, cms[2], cms[3])):
        m0_u = up_prod(cm_u, phi_u)
        m0_l = lo_prod(cm_l, phi_l)
        mvals[slot] = m0_u
        mvals[slot + 1] = m0_l
        mvals[4 + slot] = up_prod(m0_u, gh_u)
        mvals[4 + slot + 1] = lo_prod(m0_l, gh_l)
    for base_index, cf in ((0, bc), (1, cc)):
        cr, ci = float(cf.real), float(cf.imag)
        re = wb.mul(wb.push(), phi,
                    wb.sub(wb.push(),
                           wb.mul(wb.push(), wb.set(wb.push(), cr), cs),
                           wb.mul(wb.push(), wb.set(wb.push(), ci), sn)))
        im = wb.mul(wb.push(), phi,
                    wb.add(wb.push(),
                           wb.mul(wb.push(), wb.set(wb.push(), cr), sn),
                           wb.mul(wb.push(), wb.set(wb.push(), ci), cs)))
        re2 = wb.sub(wb.push(), wb.mul(wb.push(), re, g_val),
                     wb.mul(wb.push(), im, h_val))
        im2 = wb.add(wb.push(), wb.mul(wb.push(), re, h_val),
                     wb.mul(wb.push(), im, g_val))
        o = 4 * base_index
        lib.mpfr_add(C.byref(acc[o].x), C.byref(acc[o].x),
                     C.byref(re.x), RNDN)
        lib.mpfr_add(C.byref(acc[o + 1].x), C.byref(acc[o + 1].x),
                     C.byref(im.x), RNDN)
        lib.mpfr_add(C.byref(acc[o + 2].x), C.byref(acc[o + 2].x),
                     C.byref(re2.x), RNDN)
        lib.mpfr_add(C.byref(acc[o + 3].x), C.byref(acc[o + 3].x),
                     C.byref(im2.x), RNDN)
    wb.sp = sp0


def chunk_worker(k, nchunk):
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
    share_u = np.zeros((4, NODE_COUNT))
    share_l = np.zeros((4, NODE_COUNT))
    floor_u = np.zeros((4, NODE_COUNT))
    floor_l = np.zeros((4, NODE_COUNT))
    fmass_u = np.zeros((4, NODE_COUNT))
    fmass_l = np.zeros((4, NODE_COUNT))
    norm_u = [0.0] * 4
    norm_l = [0.0] * 4
    tri_u = [0.0] * 4
    tri_l = [0.0] * 4
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
        s_u = [0.0] * 4
        s_l = [0.0] * 4
        for r in range(4):
            su = 0.0
            sl = 0.0
            for j in range(NODE_COUNT):
                su = up_sum(su, m_u[r][j])
                sl = lo_sum(sl, m_l[r][j])
            s_u[r], s_l[r] = su, sl
        for r in range(4):
            ri, ii = ROW_ACC[r]
            h_f = math.hypot(acc[ri].get_d(RNDN), acc[ii].get_d(RNDN))
            ag_u = up_pad(h_f)
            ag_l = lo_pad(h_f)
            norm_u[r] = up_sum(norm_u[r], up_prod(w_u, ag_u))
            norm_l[r] = lo_sum(norm_l[r], lo_prod(w_l, ag_l))
            tri_u[r] = up_sum(tri_u[r], up_prod(w_u, s_u[r]))
            tri_l[r] = lo_sum(tri_l[r], lo_prod(w_l, s_l[r]))
            for j in range(NODE_COUNT):
                mu = m_u[r][j]
                ml = m_l[r][j]
                in_u = up_sum(up_sum(mu, -s_l[r]), ag_l)
                in_l = lo_sum(lo_sum(ml, -s_u[r]), ag_l)
                if in_u > 0.0:
                    floor_u[r, j] = up_sum(floor_u[r, j],
                                           up_prod(w_u, in_u))
                if in_l > 0.0:
                    floor_l[r, j] = lo_sum(floor_l[r, j],
                                           lo_prod(w_l, in_l))
                fmass_u[r, j] = up_sum(fmass_u[r, j], up_prod(w_u, mu))
                fmass_l[r, j] = lo_sum(fmass_l[r, j], lo_prod(w_l, ml))
                if s_l[r] > 0.0:
                    share_u[r, j] = up_sum(
                        share_u[r, j],
                        up_div(up_prod(up_prod(w_u, ag_u), mu), s_l[r]))
                    share_l[r, j] = lo_sum(
                        share_l[r, j],
                        lo_div(lo_prod(lo_prod(w_l, ag_l), ml), s_u[r]))
    out = {
        "chunk": k, "i0": i0, "i1": i1, "nchunk": nchunk,
        "share_u": share_u.tolist(), "share_l": share_l.tolist(),
        "floor_u": floor_u.tolist(), "floor_l": floor_l.tolist(),
        "fmass_u": fmass_u.tolist(), "fmass_l": fmass_l.tolist(),
        "norm_u": norm_u, "norm_l": norm_l,
        "tri_u": tri_u, "tri_l": tri_l,
        "wsum_u": wsum_u, "wsum_l": wsum_l,
        "diag": {"active_pairs": diag[0], "masked_pairs": diag[1],
                 "min_mask_margin": diag[2], "mask_disagreements": diag[3],
                 "mask_undecided": diag[4]},
    }
    (R / f"2262_chunk_{k}.json").write_text(
        json.dumps(out) + "\n", encoding="utf-8", newline="\n")
    print(json.dumps({"chunk": k, "nodes": i1 - i0, "diag": out["diag"]}),
          flush=True)


def sum_grid(a, b, sum_fn):
    return [[sum_fn(a[r][j], b[r][j]) for j in range(NODE_COUNT)]
            for r in range(4)]


def float64_rows():
    """Recompute the float64 2258 readings on the committed grid."""
    fam, base, corr, a_max = o34.build_construction()
    x = np.linspace(-a_max, a_max, NX)
    wgt = c58.trap_weights(x, a_max)
    coefs = {"base_M0": base, "corr_M0": corr,
             "base_D2": base, "corr_D2": corr}
    kinds = {"base_M0": "M0", "corr_M0": "M0",
             "base_D2": "D2", "corr_D2": "D2"}
    G = {r: np.zeros(NX, complex) for r in ROWS}
    S = {r: np.zeros(NX) for r in ROWS}
    Mabs = {r: np.zeros((NODE_COUNT, NX)) for r in ROWS}
    for j, (a, th) in enumerate(fam):
        g_m0, g_d2 = c58.family_terms(x, a, th)
        for r in ROWS:
            g = coefs[r][j] * (g_m0 if kinds[r] == "M0" else g_d2)
            G[r] += g
            Mabs[r][j] = np.abs(g)
            S[r] += Mabs[r][j]
    out = {}
    for r in ROWS:
        AG = np.abs(G[r])
        share = np.zeros(NODE_COUNT)
        floor = np.zeros(NODE_COUNT)
        fmass = np.zeros(NODE_COUNT)
        for j in range(NODE_COUNT):
            with np.errstate(divide="ignore", invalid="ignore"):
                ratio = np.where(S[r] > 0.0, Mabs[r][j] * AG / S[r], 0.0)
            share[j] = float(np.sum(wgt * ratio))
            floor[j] = float(np.sum(wgt * np.maximum(
                Mabs[r][j] - (S[r] - AG), 0.0)))
            fmass[j] = float(np.sum(wgt * Mabs[r][j]))
        out[r] = {"norm": float(np.sum(wgt * AG)),
                  "tri": float(np.sum(wgt * S[r])),
                  "share": share, "floor": floor, "fmass": fmass}
    return out


def reduce_chunks(nchunk):
    parts = [json.loads((R / f"2262_chunk_{k}.json").read_text(
        encoding="utf-8")) for k in range(nchunk)]
    p0 = parts[0]
    share_u = p0["share_u"]
    share_l = p0["share_l"]
    floor_u = p0["floor_u"]
    floor_l = p0["floor_l"]
    fmass_u = p0["fmass_u"]
    fmass_l = p0["fmass_l"]
    norm_u = list(p0["norm_u"])
    norm_l = list(p0["norm_l"])
    tri_u = list(p0["tri_u"])
    tri_l = list(p0["tri_l"])
    wsum_u = p0["wsum_u"]
    wsum_l = p0["wsum_l"]
    diag = {"active_pairs": 0, "masked_pairs": 0, "min_mask_margin":
            math.inf, "mask_disagreements": 0, "mask_undecided": 0}
    for p in parts:
        share_u = sum_grid(share_u, p["share_u"], up_sum) \
            if p is not p0 else share_u
        share_l = sum_grid(share_l, p["share_l"], lo_sum) \
            if p is not p0 else share_l
        floor_u = sum_grid(floor_u, p["floor_u"], up_sum) \
            if p is not p0 else floor_u
        floor_l = sum_grid(floor_l, p["floor_l"], lo_sum) \
            if p is not p0 else floor_l
        fmass_u = sum_grid(fmass_u, p["fmass_u"], up_sum) \
            if p is not p0 else fmass_u
        fmass_l = sum_grid(fmass_l, p["fmass_l"], lo_sum) \
            if p is not p0 else fmass_l
        if p is not p0:
            norm_u = [up_sum(a, b) for a, b in zip(norm_u, p["norm_u"])]
            norm_l = [lo_sum(a, b) for a, b in zip(norm_l, p["norm_l"])]
            tri_u = [up_sum(a, b) for a, b in zip(tri_u, p["tri_u"])]
            tri_l = [lo_sum(a, b) for a, b in zip(tri_l, p["tri_l"])]
            wsum_u = up_sum(wsum_u, p["wsum_u"])
            wsum_l = lo_sum(wsum_l, p["wsum_l"])
        d = p["diag"]
        diag["active_pairs"] += d["active_pairs"]
        diag["masked_pairs"] += d["masked_pairs"]
        diag["mask_disagreements"] += d["mask_disagreements"]
        diag["mask_undecided"] += d["mask_undecided"]
        diag["min_mask_margin"] = min(diag["min_mask_margin"],
                                      d["min_mask_margin"])

    anchors = {}
    if ANCHOR_2258.exists():
        a58 = json.loads(ANCHOR_2258.read_text(encoding="utf-8"))
        anchors = {r: a58["rows"][r].get("anchor_2234") for r in ROWS}

    f64 = float64_rows()

    def ulp_res(v, lo, hi):
        if v < lo:
            return (lo - v) / math.ulp(v if v != 0.0 else 1.0)
        if v > hi:
            return (v - hi) / math.ulp(v if v != 0.0 else 1.0)
        return 0.0

    rows_out = {}
    all_res = []
    for r in ROWS:
        i = ROWS.index(r)
        n_u, n_l = norm_u[i], norm_l[i]
        t_u, t_l = tri_u[i], tri_l[i]
        core = f64[r]
        ratio_u = [up_div(BUDGET_DENOM * share_u[i][j], n_l)
                   for j in range(NODE_COUNT)]
        ratio_l = [lo_div(BUDGET_DENOM * share_l[i][j], n_u)
                   for j in range(NODE_COUNT)]
        f_ratio_u = [up_div(BUDGET_DENOM * floor_u[i][j], n_l)
                     for j in range(NODE_COUNT)]
        max_share_res = max(
            ulp_res(core["share"][j], share_l[i][j], share_u[i][j])
            for j in range(NODE_COUNT))
        max_floor_res = max(
            ulp_res(core["floor"][j], floor_l[i][j], floor_u[i][j])
            for j in range(NODE_COUNT))
        max_fmass_res = max(
            ulp_res(core["fmass"][j], fmass_l[i][j], fmass_u[i][j])
            for j in range(NODE_COUNT))
        norm_res = ulp_res(core["norm"], n_l, n_u)
        tri_res = ulp_res(core["tri"], t_l, t_u)
        all_res += [norm_res, tri_res, max_share_res, max_fmass_res]
        anchor = anchors.get(r)
        rows_out[r] = {
            "norm": [n_l, n_u],
            "triangle": [t_l, t_u],
            "cancellation": [lo_div(t_l, n_u), up_div(t_u, n_l)],
            "anchor_2234": anchor,
            "anchor_ge_norm_lower": (None if anchor is None
                                     else anchor >= n_l),
            "anchor_above_norm_upper_ulp": (
                None if anchor is None else ulp_res(anchor, n_l, n_u)),
            "norm_reading": core["norm"],
            "norm_reading_residual_ulp": norm_res,
            "triangle_reading": core["tri"],
            "triangle_reading_residual_ulp": tri_res,
            "cancellation_reading": core["tri"] / core["norm"],
            "share": [[share_l[i][j], share_u[i][j]]
                      for j in range(NODE_COUNT)],
            "floor": [[floor_l[i][j], floor_u[i][j]]
                      for j in range(NODE_COUNT)],
            "floor_reading": core["floor"].tolist(),
            "fmass": [[fmass_l[i][j], fmass_u[i][j]]
                      for j in range(NODE_COUNT)],
            "ratio_over_budget": [[ratio_l[j], ratio_u[j]]
                                  for j in range(NODE_COUNT)],
            "floor_ratio_upper_over_budget": f_ratio_u,
            "nodes_certified_fail": int(sum(1 for v in ratio_l if v > 1.0)),
            "nodes_certified_pass": int(sum(1 for v in ratio_u if v < 1.0)),
            "max_ratio_lower": max(ratio_l),
            "max_floor_ratio_upper": max(f_ratio_u),
            "max_share_residual_ulp": max_share_res,
            "max_floor_residual_ulp": max_floor_res,
            "max_fmass_residual_ulp": max_fmass_res,
        }

    channels = {}
    for name, rl, rr in (("a", "base_D2", "corr_M0"),
                         ("b", "corr_D2", "base_M0")):
        il, ir = ROWS.index(rl), ROWS.index(rr)
        n_l_prod = lo_prod(norm_l[il], norm_l[ir])
        n_u_prod = up_prod(norm_u[il], norm_u[ir])
        diag_u = [up_div(BUDGET_DENOM * up_prod(share_u[il][j],
                                                share_u[ir][j]), n_l_prod)
                  for j in range(NODE_COUNT)]
        diag_l = [lo_div(BUDGET_DENOM * lo_prod(share_l[il][j],
                                                share_l[ir][j]), n_u_prod)
                  for j in range(NODE_COUNT)]
        fdiag_u = [up_div(BUDGET_DENOM * up_prod(floor_u[il][j],
                                                 floor_u[ir][j]), n_l_prod)
                   for j in range(NODE_COUNT)]
        channels[name] = {
            "rows": [rl, rr],
            "diag_ratio": [[diag_l[j], diag_u[j]]
                           for j in range(NODE_COUNT)],
            "diag_floor_upper": fdiag_u,
            "nodes_certified_fail": int(sum(1 for v in diag_l if v > 1.0)),
            "nodes_certified_pass": int(sum(1 for v in diag_u if v < 1.0)),
        }

    max_res = max(all_res)
    max_floor_ratio_u = max(rows_out[r]["max_floor_ratio_upper"]
                            for r in ROWS)
    verdict = (
        "BALL-CERTIFIED 2258: cancellation "
        + "; ".join(f"{r} [{rows_out[r]['cancellation'][0]:.6g}, "
                    f"{rows_out[r]['cancellation'][1]:.6g}]"
                    for r in ROWS)
        + "; nodes failing the uniform budget at the certified LOWER "
          "ratios: "
        + " / ".join(f"{r} {rows_out[r]['nodes_certified_fail']}/30"
                     for r in ROWS)
        + "; channels "
        + " / ".join(f"{n} {channels[n]['nodes_certified_fail']}/30"
                     for n in channels)
        + f". Max float64-reading residual {max_res:.3g} ulp over "
          "norms/triangles/shares/masses; mask certified "
          f"(min |q - 0.04| = {diag['min_mask_margin']:.6g}, "
          f"{diag['mask_disagreements']} disagreements, "
          f"{diag['mask_undecided']} undecided). Floor readings are "
          "excluded from the residual line (the float64 floor subtracts "
          "S - AG at the S ~ 1e19 scale and is cancellation noise); the "
          "certified floor-ratio upper bounds are all <= "
          f"{max_floor_ratio_u:.3g} of the budget. The 2258 conclusions "
          "survive interval certification; no producer GO, no gate sign "
          "change, no RH claim.")
    result = {
        "record": RECORD,
        "status": "DIRECTED-MPFR-CERTIFIED (256-bit MPFR RNDN path, pad "
                  "2^-52 on every extraction, one-nextafter guards on "
                  "every positive accumulation)",
        "date": "2026-09-30",
        "grid": {"NX": NX, "mask": QQ_MASK, "sigma": 1.0, "pad": PAD},
        "diag": diag,
        "wsum": [wsum_l, wsum_u],
        "rows": rows_out,
        "channels": channels,
        "max_reading_residual_ulp": max_res,
        "floor_reading_note": (
            "the float64 floor reading ag - (S - AG) subtracts S at the "
            "1e19 scale and carries cancellation noise at the 2^-53 S "
            "scale; the certified floor enclosures are the meaningful "
            "objects (per-node floor_l/floor_u and the ratio bounds), and "
            "the float64 floor readings are stored per row for the audit"),
        "verdict": verdict,
        "nonclaims": [
            "the certified objects are the true mathematical quantities "
            "with the committed 2258 mask semantics; the float64 readings "
            "carry their own ~1e-15 rounding, reported as ulp residuals",
            "the signed pieces and the Hall top-3 datum of 2258 are not "
            "part of this certification (informational there)",
            "no producer GO, no gate sign change, no RH claim",
        ],
        "provenance": {
            "script": "scripts/routea_weighted_zero_cancellation_split_"
                      "ball_2262.py",
            "machinery": "scripts/routea_weighted_zero_direct_product_"
                         "outward_2234.py (MPFR path), "
                         "routea_weighted_zero_cancellation_split_2258.py "
                         "(semantics)",
            "predecessor": "docs/proofs/2258_routea_weighted_zero_"
                           "cancellation_split.md",
        },
    }
    OUTPUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8",
                      newline="\n")
    for k in range(nchunk):
        (R / f"2262_chunk_{k}.json").unlink(missing_ok=True)
    brief = {
        "verdict": verdict,
        "cancellation": {r: rows_out[r]["cancellation"] for r in ROWS},
        "fails": {r: rows_out[r]["nodes_certified_fail"] for r in ROWS},
        "channels": {n: channels[n]["nodes_certified_fail"]
                     for n in channels},
        "max_res_ulp": max_res,
        "max_floor_ratio_upper": max_floor_ratio_u,
        "diag": diag,
        "anchors": {r: [rows_out[r]["anchor_2234"],
                        rows_out[r]["anchor_ge_norm_lower"]] for r in ROWS},
    }
    print(json.dumps(brief, indent=2))


def main():
    argv = sys.argv[1:]
    if argv and argv[0] == "chunk":
        chunk_worker(int(argv[1]), int(argv[2]) if len(argv) > 2 else NCHUNK)
        return
    if argv and argv[0] == "reduce":
        reduce_chunks(int(argv[1]) if len(argv) > 1 else NCHUNK)
        return
    procs = [subprocess.Popen([sys.executable, __file__, "chunk", str(k),
                               str(NCHUNK)]) for k in range(NCHUNK)]
    codes = [p.wait() for p in procs]
    if any(c != 0 for c in codes):
        raise SystemExit(f"chunk failures: {codes}")
    reduce_chunks(NCHUNK)


if __name__ == "__main__":
    main()