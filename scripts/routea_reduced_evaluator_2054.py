#!/usr/bin/env python3
# routea_reduced_evaluator_2054.py — record 2054 (probe; verdict rules
# frozen before the run)
#
# THE REDUCED EVALUATOR: re-price the L2 interval architecture at the
# m = 1600 object.  Record 2053 measured that the committed phi-quadrature
# rule (m = 400) carries its own error of 1.1111757e+20 at this owner
# (fam-16/17 alias on the positive side), 3.3e7x the true window integral
# -3.406049871881e+12; the registered follow-up is to re-run the SAME
# chain at m = 1600 and price the window remainder against the re-based
# ideal budget.  This probe does exactly that; it touches NO committed
# pipeline and NO 2048-2053 artifact.
#
# OBJECT (tier A).  The committed 2037-class float pipeline with the
# phi-quadrature rule at m = 1600:
#   xw1600_j = r59.phi_weights(a_j, panels = 6, m = 1600)  (9600 nodes/fam)
# and everything else committed: base/corr from r37.setup (eigh/min-h1 on
# the m = 400 nodal matrix), sigma/book kernel, window [-40, 40], owner
# one-copy G8-H.  SCOPE as records 2051/2052: stored floats exact; L5
# (F construction, phi quadrature, eigh/min-h1, sigma) not touched.
# TIER-B DIAGNOSTIC (not the object): base/corr re-solved at m = 1600
# (nodal matrix a_mat1600), reported as the L5-class movement reading.
#
# WHAT IS PRICED.  Q_1600(40) = W(h) + remainder, and the verdict total is
#   total = min over rungs of min(charge_L3, charge_agg)   (model part, L2)
#         + charge_L1(h*)                                  (nodal input, 2052)
#         + arch_1600                                      (sigma projection)
# exactly the 2051/2052 assembly at the new object.  L4 (full-line tail)
# is NOT re-run: the 2053 kill functions bound the IDEAL object's own tail
# (Gevrey rungs + stored base/corr magnitudes) and are evaluator-
# independent; they stand unchanged.  Verdict is therefore about the
# WINDOW node, with the L4 tail kill on record.
#
# FROZEN REFERENCES (provenance)
#   results/2053_l4_horizon.json (md5 275a4e07aa4453b4ae661275d90f3743):
#     Q_400  = -1.1111757839943646e+20   (hh = 0.01 window grid, m = 400)
#     Q_1600 = -3406049871881.2666       (hh = 0.01, m = 1600)
#   results/2051_l3_aggregate.json (md5 db710a0795acba3f536fec84eefee508
#   is the SCRIPT; artifact values):
#     charge_L3(0.002, m=400)  = 5.657706991143483e+18
#     charge_agg(0.002, m=400) = 2.7512365454404613e+18
#     C_book = 458.0475860314685, C1_book = 21898.85724574201,
#     support 9.504, book 1647, families 17
#   r51/r52 constants: Coef1(0.002) = 23309.192 (2048); ECHO_REL = 1e-15;
#   INS = 1.05; ANCHOR_WIDTH_MEAN_2043 = 569.087 (tol 2%), ANCHOR_DXI = .05
#   BUDGET3 = |Q_1600| = 3.4060498718812666e+12 (ideal window budget at the
#   m = 1600 object); BAR10 = 0.1 * BUDGET3 = 3.4060498718812666e+11.
#
# CONTROLS (gates; frozen)
#   C1  Q_400_2054 (full window, hh = 0.01, committed 2037 path) vs frozen
#       Q_400: rel <= 1e-6 AND negative.
#   C2  Q_1600_2054 (same path, xw1600) vs frozen Q_1600: rel <= 1e-6 AND
#       negative.  C1+C2 anchor 2053's adjudicated numbers.
#   C3  setup cross-reads: families 17, book 1647, support 9.504,
#       C_book vs 458.0475860314685, C1_book vs 21898.85724574201, all
#       rel <= 1e-9; C_book/C1_book identical at m = 400 and m = 1600
#       (m-independence of the book).
#   C4  span-parallel instrument equivalence (three readings; gate on C4c):
#       C4a worker-executed jet task vs the same call in-parent;
#       C4b ParModel.g_jet vs r51.Model.g_jet on the same 2-span node set;
#       C4c the same at the operative span size (gate: max componentwise
#       rel <= 1e-12).  Batch-size ulp sensitivity is measured, not assumed.
#   C5  2051 frozen cross-read at the FULL m = 400 instrument (dxi_g =
#       0.00025, run_rung chunk = 2048, exactly the 2051 shapes):
#       charge_L3(0.002) and charge_agg(0.002) vs the frozen values, rel
#       <= 1e-9.  Validates the plumbing end-to-end against a committed
#       artifact before any m = 1600 number is trusted.
#   C6  arch-projection provenance: width_mean (m-independent quantity)
#       vs 569.087 within 2% (the 2048 A1 convention).
#
# VALIDITY ANCHORS (gates, at m = 1600)
#   A1  pipeline agreement max |model g - committed g| <= 1e-9 * gmax per
#       rung (r51.run_rung's own a1_abs against the fine grid).
#   A2a enclosure validity: r51.run_rung's a2_violations == 0 per rung.
#       A2b (commit-vs-model fd gap) is BOOKED, reported, not gated (2051
#       restructure).
#   A3  bundle-vs-mpmath.iv containment (r51.iv_containment) at m = 1600.
#   A6  jet algebra selftest (r51.selftest; m-independent).
#   B1  containment at h* ladder nodes incl. the mass hump (-6.68, -7.03):
#       |C - g^O| <= e_g, g^O in mpmath dps 40 (2052 machinery).
#   B4  finite/nonnegative charges; Coef1 total == sum of node
#       coefficients (rel <= 1e-9).
#   B5  forward-calculus selftest (r52.selftest, dps 50, 200 draws).
#   A4/A7 are REPORTED structure (agg vs L3 per rung; aggregate pricing
#   loss), not gates: at the new object the L3-vs-agg ranking is data the
#   verdict consumes, not a validity condition (re-scope vs 2051,
#   disclosed).
#
# VERDICT RULES (frozen)
#   ANCHOR-FAIL         : any gate above misses
#   REDUCED-L2-VIABLE   : gates pass AND total < BAR10      (10% budget)
#   REDUCED-L2-GRAY     : gates pass AND total < BUDGET3
#   REDUCED-L2-FAIL     : gates pass AND total >= BUDGET3
#
# CLI: (default) full probe;  --smoke  coarse plumbing (dxi_g = 0.002,
#      ladder (0.02,), skips B1/A3/A7/C5, disclosed);  --workers N
#      (default 12);  --selftest  A6 + B5 only;  --chunk N overrides the
#      L1 calculus chunk (default 2048 = the 2052 shape).

import json
import math
import os
import sys
import time

import multiprocessing as mp

import numpy as np

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, "scripts"))

import fourpoint_owner_completion_1980 as r80  # noqa: E402
import fourpoint_owner_density_1959 as r59     # noqa: E402
import routea_g8h_basis_comparison_2037 as r37  # noqa: E402
import routea_l3_aggregate_2051 as r51         # noqa: E402
import routea_l1_nodal_enclosure_2052 as r52   # noqa: E402
import routea_interval_kernel_2043 as r43      # noqa: E402

U = 2.0 ** -53
XI_MAX = 40.0
M_RED = 1600
PANELS = 6
DXI_G = 0.00025
H_LADDER = (0.01, 0.005, 0.002, 0.001)
HH_CTRL = 0.01

# frozen 2053 window values (results/2053_l4_horizon.json)
Q400_FROZEN = -1.1111757839943646e+20
Q1600_FROZEN = -3406049871881.2666
BUDGET3 = abs(Q1600_FROZEN)
BAR10 = 0.1 * BUDGET3

# frozen 2051 m = 400 charges at h = 0.002
L3_2051_0P002 = 5.657706991143483e+18
AGG_2051_0P002 = 2.7512365454404613e+18
C_BOOK_2051 = 458.0475860314685
C1_BOOK_2051 = 21898.85724574201
SUPPORT_2051 = 9.504
BOOK_2051 = 1647
NFAM_2051 = 17
COEF1_2048_0P002 = 23309.192

ARCH_ANCHOR_DXI = 0.05
ANCHOR_WIDTH_MEAN_2043 = 569.087
ANCHOR_WIDTH_TOL = 0.02

TOL_C1C2 = 1e-6
TOL_C3 = 1e-9
TOL_C4 = 1e-12
TOL_C5 = 1e-9

SPAN_JET = 4096   # = the jet chunk size run_rung itself uses
SPAN_L1 = 2048    # = the 2052 L1 calculus chunk
SPAN_FG = 8192    # fine-grid span (no sequential analog; any shape)

PICKS_B1 = [0.0, 0.493, -6.68, -7.03, 20.0, 34.97, 39.747]

_POOL = None
_PC = {}


def _task_jet(args):
    span, rho, chunk = args
    return r51.Model.g_jet(_PC["model"], span, rho, chunk)


def _jet_parts(j):
    """Flatten a real jet [c0,c1,c2,c3,k4]: slots 0-3 are (val, err)
    bundles, slot 4 is a bare array (the r51 convention)."""
    parts = []
    for slot in j:
        if isinstance(slot, tuple):
            parts.extend([slot[0], slot[1]])
        else:
            parts.append(np.asarray(slot))
    return parts


def _task_g(args):
    lo, hi = args
    xi = _PC["xi"][lo:hi]
    s = 0.5 - 2j * np.pi * xi
    v = r80.family_values(_PC["fam"], r37.K, s, _PC["xw"])
    lb = _PC["base"] @ v
    cc = _PC["corr"] @ v
    p = np.real(r59.P_from_nodes(xi, _PC["cnt"]))
    return p * p * np.abs(lb) ** 2 * np.abs(cc) ** 2


def _task_l1(args):
    lo, hi = args
    C, EG = r52.committed_and_bound(_PC["model"], _PC["nodes"][lo:hi],
                                    _PC["xw"], _PC["l1chunk"])
    return C, EG


def phase_pool(workers):
    """(Re)create the pool so workers fork the CURRENT _PC context."""
    global _POOL
    if _POOL is not None:
        _POOL.terminate()
        _POOL.join()
        _POOL = None
    if workers > 1:
        _POOL = mp.get_context("fork").Pool(workers)
    return _POOL


def pmap(fn, args):
    if _POOL is None:
        return [fn(a) for a in args]
    return _POOL.map(fn, args)


class ParModel(r51.Model):
    """r51.Model with a span-parallel g_jet; identical per-node arithmetic,
    spans at the jet chunk size so batch shapes match the sequential path
    (equivalence measured by C4, not assumed)."""

    def g_jet(self, nodes, rho, chunk):
        if _POOL is None or len(nodes) <= SPAN_JET:
            return r51.Model.g_jet(self, nodes, rho, chunk)
        n = len(nodes)
        tasks = [(nodes[lo:min(lo + SPAN_JET, n)], rho, chunk)
                 for lo in range(0, n, SPAN_JET)]
        parts = _POOL.map(_task_jet, tasks)
        res = []
        for k in range(5):
            if isinstance(parts[0][k], tuple):
                res.append((np.concatenate([p[k][0] for p in parts]),
                            np.concatenate([p[k][1] for p in parts])))
            else:
                res.append(np.concatenate([np.asarray(p[k])
                                           for p in parts]))
        return res


def kernel_at(xg, ps):
    """Committed composite kernel sigma_arch + book at xg (float)."""
    ker = r59.rig.sigma_vec(2 * np.pi * xg)
    for num, w in ps:
        ker = ker + 2 * w / math.sqrt(num) * np.cos(2 * np.pi * xg
                                                     * math.log(num))
    return ker


def window_control(fam, xw, base, corr, rho, ps):
    """The 2053 C4-profile construction verbatim: hh = 0.01 window grid,
    committed path, returns Q_full, g, and the cached v for tier B."""
    xg = np.arange(-XI_MAX, XI_MAX + HH_CTRL / 2, HH_CTRL)
    s = 0.5 - 2j * np.pi * xg
    v = r80.family_values(fam, r37.K, s, xw)
    lb = base @ v
    cc = corr @ v
    p = np.real(r59.P_from_nodes(xg, r80.counterpart_nodes(rho)))
    g = p * p * np.abs(lb) ** 2 * np.abs(cc) ** 2
    ker = kernel_at(xg, ps)
    fx = ker * g
    Q = float(np.sum(0.5 * (fx[1:] + fx[:-1]) * HH_CTRL))
    return {"Q": Q, "g_max": float(np.max(g)), "xg": xg, "ker": ker, "v": v,
            "p": p, "n": len(xg)}


def fine_grid(fam, xw, base, corr, rho, dxi_g, workers, tag):
    """g on the fine grid (span-parallel) + its second-difference stencil."""
    global _PC
    n_g = int(round(2 * XI_MAX / dxi_g))
    xi = np.linspace(-XI_MAX, XI_MAX, n_g + 1)
    _PC = {"fam": fam, "xw": xw, "base": base, "corr": corr,
           "cnt": r80.counterpart_nodes(rho), "xi": xi}
    phase_pool(workers)
    t0 = time.time()
    spans = [(lo, min(lo + SPAN_FG, n_g + 1))
             for lo in range(0, n_g + 1, SPAN_FG)]
    g_com = np.concatenate(pmap(_task_g, spans))
    gpp = np.empty_like(g_com)
    gpp[1:-1] = (g_com[2:] - 2 * g_com[1:-1] + g_com[:-2]) / (dxi_g ** 2)
    gpp[0] = gpp[1]
    gpp[-1] = gpp[-2]
    print("  fine grid %s: %d pts, gmax %.6e (%.1fs)"
          % (tag, n_g + 1, float(np.max(np.abs(g_com))), time.time() - t0),
          flush=True)
    return g_com, gpp, xi


def controls_c4(model, workers):
    """C4: worker vs parent jet execution and ParModel vs Model."""
    global _PC
    _PC = {"model": model}
    phase_pool(workers)
    span = np.array([-13.25, 0.31, 7.77, 21.5])
    rho_c4 = 0.001

    def rel(a, b):
        d = 0.0
        for va, vb in zip(_jet_parts(a), _jet_parts(b)):
            den = np.maximum(np.abs(vb), 1e-30)
            d = max(d, float(np.max(np.abs(va - vb) / den)))
        return d

    d_in = _task_jet((span, rho_c4, 4096))
    c4a = None
    if _POOL is not None:
        d_wk = _POOL.map(_task_jet, [(span, rho_c4, 4096)])[0]
        c4a = rel(d_in, d_wk)
    nodes_c4 = np.linspace(-1.0, 1.0, 2 * SPAN_JET)
    c4b = None
    if _POOL is not None:
        j_seq = r51.Model.g_jet(model, nodes_c4, rho_c4, 4096)
        j_par = model.g_jet(nodes_c4, rho_c4, 4096)
        c4b = rel(j_par, j_seq)
    vac = _POOL is None
    print("C4 worker-vs-parent %s  ParModel-vs-Model %s%s"
          % (c4a, c4b, " (vacuous: workers=1)" if vac else ""), flush=True)
    return {"C4a_worker_vs_parent": c4a, "C4b_parmodel_vs_model": c4b,
            "vacuous_no_pool": vac,
            "pass": bool(vac or (c4b is not None and c4b <= TOL_C4))}


def window_arch(fam, xw, base, corr, rho, ps):
    """arch charge at 0.05, 2048 A1 convention verbatim (iv.dps 20)."""
    import mpmath as mp
    mp.iv.dps = 20
    iv = mp.iv
    n_pan = int(round(2 * XI_MAX / ARCH_ANCHOR_DXI))
    edges_a = np.linspace(-XI_MAX, XI_MAX, n_pan + 1)
    ker_a, g_a = r43.float_kernel_and_g(edges_a, fam, xw, base, corr, rho,
                                        ps)
    g_mid_a = 0.5 * (g_a[:-1] + g_a[1:])
    w_tot = np.empty(n_pan)
    w_arch = np.empty(n_pan)
    ck_iv = [(iv.mpf(2) * iv.pi) * iv.log(iv.mpf(int(num))) for num, _ in ps]
    wk_iv = [iv.mpf(2) * iv.mpf(int(w)) / iv.sqrt(iv.mpf(int(num)))
             for num, w in ps]
    for i in range(n_pan):
        xi_iv = iv.mpf([repr(float(edges_a[i])), repr(float(edges_a[i + 1]))])
        sig_iv = r43.sigma_arch_iv((iv.mpf(2) * iv.pi) * xi_iv)
        book_iv = iv.mpf(0)
        for j in range(len(ps)):
            book_iv = book_iv + wk_iv[j] * iv.cos(ck_iv[j] * xi_iv)
        tot_iv = sig_iv + book_iv
        w_tot[i] = float(mp.mpf(tot_iv.b) - mp.mpf(tot_iv.a))
        w_arch[i] = float(mp.mpf(sig_iv.b) - mp.mpf(sig_iv.a))
    width_mean = float(w_tot.mean())
    arch_proj = float(np.sum(w_arch * g_mid_a * ARCH_ANCHOR_DXI))
    return {"width_mean": width_mean, "arch_proj": arch_proj,
            "gmax_anchor": float(np.max(np.abs(g_a)))}


def main():
    global _PC
    smoke = "--smoke" in sys.argv
    t0 = time.time()
    workers = 12
    l1chunk = SPAN_L1
    for i, arg in enumerate(sys.argv):
        if arg == "--workers":
            workers = int(sys.argv[i + 1])
        if arg == "--chunk":
            l1chunk = int(sys.argv[i + 1])
    if "--selftest" in sys.argv:
        print("A6", json.dumps(r51.selftest()))
        print("B5", json.dumps(r52.selftest()))
        return

    sec = {}
    dxi_g = 0.002 if smoke else DXI_G
    ladder = (0.02,) if smoke else H_LADDER

    # ------------------------------------------------------------ S0 setup
    rho_o, nodes_o, values, fam, xw400, gram, a_mat, _, _ = r37.setup(False)
    base, info_b = r37.min_h1(gram, a_mat, np.ones(len(nodes_o), complex))
    corr, info_c = r37.min_h1(gram, a_mat, np.asarray(values, complex))
    xw1600 = [r59.phi_weights(a_, panels=PANELS, m=M_RED)
              for a_, _t in fam]
    m_nodes = float(np.mean([len(X) for X, _w in xw1600]))
    cnt = r80.counterpart_nodes(rho_o)
    model400 = r51.Model(fam, r37.K, xw400, base, corr, cnt)
    model = ParModel(fam, r37.K, xw1600, base, corr, cnt)
    ps = model.ps
    c_k = np.array([2 * w / math.sqrt(num) for num, w in ps])
    om_k = np.array([2 * math.pi * math.log(num) for num, _w in ps])
    C_book = float(np.sum(c_k))
    C1_book = float(np.sum(c_k * om_k))
    print("S0 setup: %.1fs fam %d support %.6f book %d m_nodes %.1f "
          "C_book %.6f C1_book %.6g"
          % (time.time() - t0, model.nfam, model.support, len(ps), m_nodes,
             C_book, C1_book), flush=True)

    c3 = {
        "nfam": model.nfam, "book": len(ps), "support": model.support,
        "C_book": C_book, "C1_book": C1_book, "m_nodes_mean": m_nodes,
        "pass": (model.nfam == NFAM_2051 and len(ps) == BOOK_2051
                 and abs(model.support - SUPPORT_2051) <= 1e-12
                 and abs(C_book / C_BOOK_2051 - 1.0) <= TOL_C3
                 and abs(C1_book / C1_BOOK_2051 - 1.0) <= TOL_C3)}
    w40 = [r59.phi_weights(a_, panels=PANELS, m=400) for a_, _t in fam]
    cb400 = float(np.sum([2 * w / math.sqrt(num) for num, w in
                          r51.Model(fam, r37.K, w40, base, corr, cnt).ps]))
    c3["C_book_m400_identical"] = abs(cb400 - C_book) <= 1e-12 * C_book
    print("C3 %s" % {k: v for k, v in c3.items() if k != "pass"}, flush=True)
    sec["C3_setup"] = c3

    # ------------------------------------------- S1 Q controls + tier B
    t1 = time.time()
    qc400 = window_control(fam, xw400, base, corr, rho_o, ps)
    c1_rel = abs(qc400["Q"] / Q400_FROZEN - 1.0)
    c1_ok = c1_rel <= TOL_C1C2 and qc400["Q"] < 0
    qc1600 = window_control(fam, xw1600, base, corr, rho_o, ps)
    c2_rel = abs(qc1600["Q"] / Q1600_FROZEN - 1.0)
    c2_ok = c2_rel <= TOL_C1C2 and qc1600["Q"] < 0
    print("C1 Q_400 = %.10e (rel %.3e, sign_ok %s)  C2 Q_1600 = %.10e "
          "(rel %.3e, sign_ok %s) [%.1fs]"
          % (qc400["Q"], c1_rel, qc400["Q"] < 0, qc1600["Q"], c2_rel,
             qc1600["Q"] < 0, time.time() - t1), flush=True)
    sec["C1C2_window"] = {"Q_400": qc400["Q"], "rel_400": c1_rel,
                          "Q_1600": qc1600["Q"], "rel_1600": c2_rel,
                          "pass": bool(c1_ok and c2_ok)}
    # tier-B diagnostic: base/corr re-solved on the m = 1600 nodal matrix
    a_mat16 = r80.family_values(fam, r37.K,
                                np.asarray(nodes_o, complex), xw1600).T
    baseB, _ = r37.min_h1(gram, a_mat16, np.ones(len(nodes_o), complex))
    corrB, _ = r37.min_h1(gram, a_mat16, np.asarray(values, complex))
    lbB = baseB @ qc1600["v"]
    ccB = corrB @ qc1600["v"]
    gB = qc1600["p"] ** 2 * np.abs(lbB) ** 2 * np.abs(ccB) ** 2
    fxB = qc1600["ker"] * gB
    QB = float(np.sum(0.5 * (fxB[1:] + fxB[:-1]) * HH_CTRL))
    tier = {"d_base_rel": float(np.max(np.abs(baseB - base))
                                / np.max(np.abs(base))),
            "d_corr_rel": float(np.max(np.abs(corrB - corr))
                                / np.max(np.abs(corr))),
            "Q_1600_tierB": QB,
            "Q_shift_rel": abs(QB / qc1600["Q"] - 1.0)}
    print("tier-B: d_base %.3e d_corr %.3e  Q %s shift rel %.3e"
          % (tier["d_base_rel"], tier["d_corr_rel"], QB,
             tier["Q_shift_rel"]), flush=True)
    sec["tierB_diagnostic"] = tier

    # C4 was exercised on the S1 pool; keep a fresh, explicit reading here
    sec["C4_span_equivalence"] = controls_c4(model, workers)

    # ------------------------------------------------ S2 fine grid m=1600
    g_com, gpp, edges = fine_grid(fam, xw1600, base, corr, rho_o, dxi_g,
                                  workers, "m=1600")
    gmax_com = float(np.max(np.abs(g_com)))
    sec["fine_grid_1600"] = {"dxi": dxi_g, "points": len(g_com),
                             "gmax": gmax_com}

    # ------------------------------------------------------- S3 the rungs
    rows = []
    _PC = {"model": model}
    phase_pool(workers)
    for h in ladder:
        n_pan = int(round(2 * XI_MAX / h))
        row = r51.run_rung(model, h, dxi_g, g_com, gpp, n_pan, t0,
                           C_book, C1_book, c_k, om_k)
        rows.append(row)
    a1_ok = all(r_["a1_abs_max"] <= 1e-9 * gmax_com for r_ in rows)
    a2a_ok = all(r_["a2_violations"] == 0 for r_ in rows)
    b4_ok = all(np.isfinite(r_[k]) and r_[k] >= 0.0 for r_ in rows
                for k in ("charge_L3", "charge_agg", "agg_main",
                          "agg_theta", "agg_corr", "sum_U"))
    mins = [(min(r_["charge_L3"], r_["charge_agg"]), r_["h"]) for r_ in rows]
    best_min, h_best = min(mins)
    row_best = [r_ for r_ in rows if r_["h"] == h_best][0]
    print("rungs done; A1 %s A2a %s | best h %g min %.6e (L3 %.6e agg "
          "%.6e) [%.1fs]"
          % (a1_ok, a2a_ok, h_best, best_min, row_best["charge_L3"],
             row_best["charge_agg"], time.time() - t0), flush=True)
    sec["rungs_1600"] = rows
    sec["best_rung"] = {"h": h_best, "min": best_min,
                        "charge_L3": row_best["charge_L3"],
                        "charge_agg": row_best["charge_agg"]}

    # A7 aggregate pricing (reported; h = 0.002, 48 panels)
    a7 = None
    if not smoke:
        _PC = {"model": model}
        phase_pool(workers)
        a7 = r51.agg_pricing(model, 0.002, dxi_g, edges, g_com, gpp, c_k,
                             om_k, C_book, C1_book)
        print("A7 loss_vs_crude med %.4g (mass %.4g) rigorous_over_"
              "measured med %.4g (mass %.4g)"
              % (a7["loss_vs_crude_median"],
                 a7["loss_vs_crude_median_mass"],
                 a7["rigorous_over_measured_median"],
                 a7["rigorous_over_measured_median_mass"]), flush=True)
        sec["A7_aggregate_pricing"] = a7

    # ------------------------------------------------ S4 L1 nodal at h*
    t4 = time.time()
    n_best = int(round(2 * XI_MAX / h_best))
    nodes_h = np.linspace(-XI_MAX, XI_MAX, n_best + 1)
    _PC = {"model": model, "nodes": nodes_h, "xw": xw1600,
           "l1chunk": l1chunk}
    phase_pool(workers)
    spans = [(lo, min(lo + SPAN_JET, len(nodes_h)))
             for lo in range(0, len(nodes_h), SPAN_JET)]
    parts = pmap(_task_l1, spans)
    C = np.concatenate([p[0] for p in parts])
    EG = np.concatenate([p[1] for p in parts])
    coef, tot = r52.coef1_nodes(om_k, c_k, nodes_h, h_best)
    sum_cj = float(np.sum(coef))
    charge_e = float(np.sum(coef * EG))
    gmax_nodes = float(np.max(np.abs(C)))
    echo = tot * r52.ECHO_REL * gmax_nodes * r52.INS
    charge_L1 = charge_e + echo
    b4_ok = b4_ok and all(np.isfinite(v) and v >= 0.0
                          for v in (charge_e, echo, charge_L1, tot)) \
        and abs(sum_cj / tot - 1.0) <= 1e-9
    l1row = {"h": h_best, "Coef1": tot, "Coef1_sum_nodes": sum_cj,
             "C_max": gmax_nodes, "e_g_max": float(np.max(EG)),
             "e_g_median": float(np.median(EG)),
             "charge_nodal": charge_e, "charge_echo": echo,
             "charge_L1": charge_L1}
    print("L1 h* %g: Coef1 %.6g e_g max %.4g med %.4g | charge_nodal "
          "%.6g echo %.6g L1 %.6g [%.1fs]"
          % (h_best, tot, l1row["e_g_max"], l1row["e_g_median"], charge_e,
             echo, charge_L1, time.time() - t4), flush=True)
    sec["L1_nodal_1600"] = l1row

    b1 = None
    if not smoke:
        t5 = time.time()
        b1 = r52.containment_b1(model, h_best, nodes_h, C, EG, xw1600,
                                PICKS_B1)
        print("B1 containment %d/%d ok, worst ratio %.4f [%.1fs]"
              % (sum(r_["ok"] for r_ in b1), len(b1),
                 max(r_["ratio"] for r_ in b1), time.time() - t5),
              flush=True)
        sec["B1_containment"] = b1
    b1_ok = True if smoke else all(r_["ok"] for r_ in b1)

    b3 = r52.diag_b3(model, h_best, nodes_h, C, xw1600, PICKS_B1)
    sec["B3_ladder_vs_fine_diag"] = {"max_abs_diff":
                                     max(r_["abs_diff"] for r_ in b3)}

    # --------------------------------------- S5 C5 m=400 full-instrument
    c5 = {"pass": True, "skipped": True} if smoke else None
    if not smoke:
        t6 = time.time()
        gc4, gpp4, _ = fine_grid(fam, xw400, base, corr, rho_o, dxi_g,
                                 workers, "m=400")
        _PC = {"model": model400}
        phase_pool(1)
        row4 = r51.run_rung(model400, 0.002, dxi_g, gc4, gpp4, 2048, t0,
                            C_book, C1_book, c_k, om_k)
        l3_rel = abs(row4["charge_L3"] / L3_2051_0P002 - 1.0)
        ag_rel = abs(row4["charge_agg"] / AGG_2051_0P002 - 1.0)
        c5 = {"charge_L3_2054": row4["charge_L3"], "rel_L3": l3_rel,
              "charge_agg_2054": row4["charge_agg"], "rel_agg": ag_rel,
              "pass": bool(l3_rel <= TOL_C5 and ag_rel <= TOL_C5)}
        print("C5 m=400 cross-read: L3 rel %.3e agg rel %.3e [%.1fs]"
              % (l3_rel, ag_rel, time.time() - t6), flush=True)
        sec["C5_m400_crossread"] = {"row": {k: row4[k] for k in
                                            ("charge_L3", "charge_agg",
                                             "a1_abs_max", "a2_violations",
                                             "sum_U", "seconds")},
                                    "rel_L3": l3_rel, "rel_agg": ag_rel,
                                    "pass": c5["pass"]}

    # ----------------------------------------------------- S6 arch + A3
    t7 = time.time()
    ar = window_arch(fam, xw1600, base, corr, rho_o, ps)
    c6_ok = abs(ar["width_mean"] / ANCHOR_WIDTH_MEAN_2043 - 1.0) \
        <= ANCHOR_WIDTH_TOL
    print("arch: width_mean %.4f (ref %.3f, ok %s) arch_proj %.6e [%.1fs]"
          % (ar["width_mean"], ANCHOR_WIDTH_MEAN_2043, c6_ok,
             ar["arch_proj"], time.time() - t7), flush=True)
    sec["arch_1600"] = dict(ar, C6_width_ok=bool(c6_ok))

    a3 = {"pass": True, "skipped": True} if smoke else None
    if not smoke:
        t8 = time.time()
        _PC = {"model": model}
        phase_pool(1)
        a3 = r51.iv_containment(model)
        print("A3 iv containment %s [%.1fs]" % (a3["pass"],
                                                time.time() - t8), flush=True)
        sec["A3_iv_containment"] = {"pass": a3["pass"],
                                    "n": len(a3["sample"])}

    a6 = r51.selftest()
    b5 = r52.selftest()
    print("A6 %s B5 %s" % (a6["pass"], b5["pass"]), flush=True)
    sec["A6_jet_selftest"] = a6
    sec["B5_forward_selftest"] = b5

    # ------------------------------------------------------- S7 verdict
    gates = {
        "C1_Q400": bool(c1_ok), "C2_Q1600": bool(c2_ok),
        "C3_setup": bool(c3["pass"]), "C5_m400": bool(c5["pass"]),
        "A1_pipeline": bool(a1_ok), "A2a_enclosure": bool(a2a_ok),
        "A3_iv": bool(a3["pass"]), "A6_jet": bool(a6["pass"]),
        "B1_containment": bool(b1_ok), "B4_positivity": bool(b4_ok),
        "B5_forward": bool(b5["pass"]), "C6_width": bool(c6_ok),
    }
    # C4 read from the S1 pool exercise
    c4 = sec.get("C4_span_equivalence") or {"pass": False}
    gates["C4_span"] = bool(c4["pass"])
    if not all(gates.values()):
        verdict = "ANCHOR-FAIL"
    else:
        total = best_min + charge_L1 + ar["arch_proj"]
        if total < BAR10:
            verdict = "REDUCED-L2-VIABLE"
        elif total < BUDGET3:
            verdict = "REDUCED-L2-GRAY"
        else:
            verdict = "REDUCED-L2-FAIL"
    total = best_min + charge_L1 + ar["arch_proj"]
    out = {"record": 2054, "status": verdict, "gates": gates,
           "owner": "one-copy G8-H", "m_reduced": M_RED,
           "scope": "committed 2037-class float pipeline with the "
                    "phi-quadrature rule at m = 1600; stored floats exact; "
                    "L5 not touched; L4 kill stands (m-independent)",
           "constants": {"budget3": BUDGET3, "bar10": BAR10,
                         "Q400_frozen": Q400_FROZEN,
                         "Q1600_frozen": Q1600_FROZEN,
                         "L3_2051_0p002": L3_2051_0P002,
                         "AGG_2051_0p002": AGG_2051_0P002,
                         "C_book": C_book, "C1_book": C1_book,
                         "ECHO_REL": r52.ECHO_REL, "INS": r52.INS},
           "sections": sec,
           "assembly": {"best_min": best_min, "h_best": h_best,
                        "charge_L1": charge_L1,
                        "arch_proj": ar["arch_proj"], "total": total,
                        "total_over_budget3": total / BUDGET3,
                        "total_over_bar10": total / BAR10},
           "nonclaims": [
               "L5 (F construction, phi quadrature, eigh/min-h1, sigma) "
               "remains registered, not touched: the bound starts from the "
               "stored floats as exact; the tier-B diagnostic reads the "
               "eigh/min-h1 part of the movement but does not enclose it",
               "L4 (full-line tail) separate and standing: T_bnd(40) = "
               "6.515715e+41 from record 2053 describes the ideal object's "
               "own tail; this verdict prices the WINDOW node only",
               "the echo term is the 2052 disclosed proxy at 1e-15 of the "
               "nodal max",
               "the m = 1600 rule's own residual error (2053: m = 6400 "
               "cross-read rel 4.3e-12) is not charged here",
               "span-batched matmuls may differ from the sequential path "
               "at the ulp level; measured by C4",
               "not a producer theorem", "not RH"],
           "elapsed_s": None}
    sec["C4_span_equivalence"] = c4 if c4 else {"pass": False,
                                                "note": "not run"}
    path = os.path.join(ROOT, "results", "2054_reduced_evaluator.json")
    out["elapsed_s"] = round(time.time() - t0, 1)
    with open(path, "w", encoding="utf-8", newline="\n") as f:
        json.dump(out, f, indent=2, default=float)
        f.write("\n")
    print("VERDICT", verdict)
    print("total = best_min %.6e + L1 %.6e + arch %.6e = %.6e "
          "(%.4fx budget3, %.3fx bar10)"
          % (best_min, charge_L1, ar["arch_proj"], total, total / BUDGET3,
             total / BAR10))
    print("RESULT", path)
    print("elapsed", out["elapsed_s"], flush=True)
    if _POOL is not None:
        _POOL.terminate()
        _POOL.join()


if __name__ == "__main__":
    main()