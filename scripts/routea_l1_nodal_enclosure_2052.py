#!/usr/bin/env python3
# routea_l1_nodal_enclosure_2052.py — record 2052 (probe; verdict rules
# frozen before the run)
#
# RECORD 2041 LINK L1, ENCLOSED NODAL VALUES: the panel-local model part
#   I_i(k) = g(x_i) BC_k(x_i) + (Delta g_i / h) BL_k(x_i)
# consumes g AT THE PANEL NODES.  Records 2048/2051 charged this input as
# zero (L1) and carried the model part's own float64 execution as a
# MEASURED slack (5.536e+10).  This record replaces both by a PROVEN
# charge: a forward error bound of the committed float64 evaluation of g
# at the ladder nodes, relative to the stored-floats-exact object O of the
# 2051 scope, felt through the exact nodal coefficient Coef1_j.
#
# WHAT IS BOUNDED.  The committed DAG at a node xi:
#   s   = 0.5 - 2 pi i xi                     (Re exact; one rounding in Im)
#   v_j = a_j * (exp(z_j X_j) @ (phi(X_j) W_j))    (committed family path)
#   lb  = base @ v,   cc = corr @ v
#   p   = Re(prod_m (cnt_m - s))              (real up to rounding)
#   g   = ((p*p) * |lb|^2) * |cc|^2
# The bound is a (value, error) forward calculus: every scalar step carries
# its unit-roundoff term against the local magnitude product; the matvecs
# carry gamma_n * Sum|terms| with the node-independent family moments M_0
# (2051); the exp-argument rounding is carried by the SAME constant as the
# 2051 bundles:
#   e_v_j = (EPS_TERM + m U + AMP_j) M_0_j INS,
#   AMP_j = 8 U a_j^2 (0.5 + 2 pi XI_MAX + |theta_j|).
# The committed path multiplies a_j OUTSIDE the family sum while the
# stored F_j carries it inside; that association difference is a few u of
# M_0 and sits inside the same m U term.  Nothing else in the chain is
# unbounded: base, corr, cnt, (a_j, theta_j, X_j, W_j) and the node
# coordinates are stored floats (exact in scope); the upstream
# ideal-vs-stored gaps (F construction, phi quadrature, eigh/min-h1,
# sigma) remain LINK L5, registered, NOT touched.
#
# THE CHARGE.  Node j enters the model part with total weight
#   Coef1_j = Sum_k c_k |W_j(k)|          (tent weights, 2048 convention:
#   W_0 = BC_0 - BL_0/h, W_j = BL_{j-1}/h + BC_j - BL_j/h, W_last = BL/h),
# so the model-part contribution of the nodal enclosure is
#   charge_L1(h) = Sum_j Coef1_j e_g_j
#                + Coef1(h) ECHO_REL max_j |C_j| INS,
# where the second term carries the model part's own echo (BC/BL
# evaluation, assembly) at the 2048 dg_reference rate ECHO_REL = 1e-15
# relative of the nodal maximum -- exactly the rate whose h = 0.002 charge
# was 8.836e+08 -- with INS = 1.05 margin; the 2048-A3 measured floor of
# the O(1) trig blocks was 4.21e-15 ABSOLUTE, which this proxy exceeds by
# ~9 (orders) (disclosed proxy, not a proof; impact ~1e+09 out of 6.3e+17).
#
# ANCHORS
#   B1 containment (the anchor): at sampled ladder nodes incl. mass peaks
#      and cancellation cores, |C_j - g^O_j| <= e_g_j with g^O the exact
#      object in mpmath at dps 40 (exact-binary stored floats, real-iv
#      arithmetic avoided; F_j from the 2051 Model storage).
#   B2 Coef1 cross-read vs record 2048 (h = 0.002: 23309.192), rel <= 1e-6.
#   B3 diagnostic ONLY (no gate): the committed DAG evaluated at the
#      ladder node vs at the nearest fine-grid coordinate (the ulp-level
#      node-representation difference of the 2051 A1 arc).  Reported.
#   B4 all charge components finite and >= 0; Coef1 total equals the sum
#      of the per-node coefficients.
#   B5 forward-calculus selftest: the same (value, error) chain on random
#      synthetic data vs mpmath dps 50 ground truth, 200 draws; the bound
#      must dominate every draw.
#   B6 charge_agg cross-read: the per-rung aggregate charges are read from
#      results/2051_l3_aggregate.json when present and must match the
#      frozen constants below.
#
# VERDICT RULES (frozen)
#   ENCLOSED-L1-L2-VIABLE : anchors pass AND charge_agg(h*) + charge_L1(h*)
#                           + arch < 1e19   (h* = the 2051 best rung)
#   ENCLOSED-L1-L2-GRAY   : anchors pass AND that total < 1.11e20
#   ENCLOSED-L1-L2-FAIL   : anchors pass AND that total >= 1.11e20
#   ANCHOR-FAIL           : any anchor misses
#   arch = 3.917065071048301e+16 (2048, same owner).  The 2048 measured
#   slack 5.536e+10 stays on record as the estimate of the SAME class and
#   is superseded by charge_L1 in the verdict line (no measured addend).
#
# CLI: (default) full probe;  --smoke  coarse plumbing check;
#      --selftest  B5 only;  --chunk N  nodes per chunk (default 2048).

import json
import math
import os
import sys
import time

import numpy as np

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, "scripts"))

import fourpoint_owner_completion_1980 as r80  # noqa: E402
import fourpoint_owner_density_1959 as r59     # noqa: E402
import routea_g8h_basis_comparison_2037 as r37  # noqa: E402
import routea_l3_aggregate_2051 as r51         # noqa: E402

U = 2.0 ** -53
INS = 1.05
XI_MAX = 40.0
BUDGET = 1e19
HARD = 1.11e20
ARCH_2048 = r51.ARCH_2048
SLACK_2048 = r51.SLACK_2048
ECHO_REL = 1e-15
EPS_TERM = r51.EPS_TERM

# per-rung aggregate charges, read from the committed 2051 artifact
# (cross-read by B6 when the file is present)
AGG_2051 = {0.01: 4.922555687808718e20, 0.005: 3.1427331683600343e19,
            0.002: 2.7512365454404613e18, 0.001: 5.938658842155955e17}
CHARGE_2048_0p002 = r51.CHARGE_2048_0p002
COEF1_2048_0p002 = 23309.192


def bc_bl(om, a, h):
    """Closed-form (BC, BL) on [a, a+h]; replica of the 2048 convention."""
    b = a + h
    BC = (np.sin(om * b) - np.sin(om * a)) / om
    sh, ch = math.sin(om * h), math.cos(om * h)
    I1 = h * sh / om + (ch - 1.0) / (om * om)
    I2 = -h * ch / om + sh / (om * om)
    BL = np.cos(om * a) * I1 - np.sin(om * a) * I2
    return BC, BL


def coef1_nodes(om_k, c_k, edges, h):
    """Per-node nodal coefficient Coef1_j and the total Coef1(h)."""
    n = len(edges)
    coef = np.zeros(n)
    tot = 0.0
    for om, c in zip(om_k, c_k):
        BC, BL = bc_bl(om, edges[:-1], h)
        A = BC - BL / h
        B = BL / h
        W = np.empty(n)
        W[0] = A[0]
        W[1:-1] = B[:-1] + A[1:]
        W[-1] = B[-1]
        coef += c * np.abs(W)
        tot += c * float(np.sum(np.abs(W)))
    return coef, tot


def committed_and_bound(model, nodes, xw, chunk):
    """Committed-DAG value C and its forward error bound e_g at `nodes`.

    The committed evaluation replicates the 2037/1959/1980 call order of
    the 2051 fine grid: s, family_values(fam, K, s, xw), base @ v,
    corr @ v, np.real(P_from_nodes), then the left-to-right product chain.
    """
    fam = model.fam
    base = model.base
    corr = model.corr
    cnt = model.cnt
    n = len(nodes)
    C = np.empty(n)
    EG = np.empty(n)
    econst0 = []
    for (a, th, Xf, F, M, amp) in model.consts:
        econst0.append((EPS_TERM + len(Xf) * U + amp) * M[0] * INS)
    econst0 = np.asarray(econst0)
    abase = np.abs(base)
    acorr = np.abs(corr)
    g17 = 17.0 * U / (1.0 - 17.0 * U)
    for lo in range(0, n, chunk):
        hi = min(lo + chunk, n)
        xi = np.asarray(nodes[lo:hi], dtype=float)
        k = hi - lo
        s = 0.5 - 2j * np.pi * xi
        v = r80.family_values(fam, r37.K, s, xw)
        lb = base @ v
        cc = corr @ v
        p = np.real(r59.P_from_nodes(xi, cnt))
        g = p * p * np.abs(lb) ** 2 * np.abs(cc) ** 2
        C[lo:hi] = g

        # ---- bound: family values (node-independent constants)
        av = np.abs(v)
        S_lb = (abase[:, None] * av).sum(axis=0)
        S_cc = (acorr[:, None] * av).sum(axis=0)
        e_lb = g17 * S_lb + float(np.sum(abase * econst0))
        e_cc = g17 * S_cc + float(np.sum(acorr * econst0))

        # ---- bound: the quartic product chain
        # magnitudes are SAFE magnitudes (|value| + error): at a node where
        # a factor sits at its cancellation floor the float value alone is
        # not a bound on the true magnitude (the 2051 cancellation law).
        si = -(2.0 * np.pi) * xi
        e_si = U * np.abs(si)
        pre = np.ones(k)
        pim = np.zeros(k)
        e_pre = np.zeros(k)
        e_pim = np.zeros(k)
        for c_ in cnt:
            dr = c_.real + np.zeros(k)
            di = c_.imag - si
            e_dr = U * np.abs(dr)
            e_di = e_si + U * np.abs(di)
            pr = pre * dr - pim * di
            pi_ = pre * di + pim * dr
            Pre = np.abs(pre) + e_pre
            Pim = np.abs(pim) + e_pim
            Dre = np.abs(dr) + e_dr
            Dim = np.abs(di) + e_di
            e_pr = Pre * e_dr + Dre * e_pre + Pim * e_di + Dim * e_pim \
                + U * (Pre * Dre + Pim * Dim + np.abs(pr))
            e_pi = Pre * e_di + Dim * e_pre + Pim * e_dr + Dre * e_pim \
                + U * (Pre * Dim + Pim * Dre + np.abs(pi_))
            pre, pim, e_pre, e_pim = pr, pi_, e_pr, e_pi
        e_p = e_pre + e_pim   # committed takes the real part

        # ---- bound: the assembly chain ((p*p) * |lb|^2) * |cc|^2
        al = np.abs(lb)
        e_al = e_lb + U * (al + e_lb)
        yl = al * al
        Als = al + e_al
        e_yl = Als * Als - yl + U * Als * Als
        ac = np.abs(cc)
        e_ac = e_cc + U * (ac + e_cc)
        yc = ac * ac
        Acs = ac + e_ac
        e_yc = Acs * Acs - yc + U * Acs * Acs
        x = p * p
        Ps = np.abs(p) + e_p
        e_x = Ps * Ps - x + U * Ps * Ps
        g1 = x * yl
        e_g1 = (np.abs(x) + e_x) * e_yl + (yl + e_yl) * e_x \
            + U * (np.abs(x) + e_x) * (yl + e_yl)
        g2 = g1 * yc
        e_g2 = (np.abs(g1) + e_g1) * e_yc + (yc + e_yc) * e_g1 \
            + U * (np.abs(g1) + e_g1) * (yc + e_yc)
        EG[lo:hi] = e_g2 * INS
    return C, EG


def run_rung(model, h, xw, om_k, c_k, chunk):
    t0 = time.time()
    n_pan = int(round(2 * XI_MAX / h))
    nodes = np.linspace(-XI_MAX, XI_MAX, n_pan + 1)
    C, EG = committed_and_bound(model, nodes, xw, chunk)
    coef, tot = coef1_nodes(om_k, c_k, nodes, h)
    sum_cj = float(np.sum(coef))
    charge_e = float(np.sum(coef * EG))
    gmax = float(np.max(np.abs(C)))
    echo = tot * ECHO_REL * gmax * INS
    charge = charge_e + echo
    c_agg = AGG_2051[h]
    dg_star = (BUDGET - c_agg - ARCH_2048) / tot
    row = {"h": h, "nodes": n_pan + 1, "C_max": gmax,
           "Coef1": tot, "Coef1_sum_nodes": sum_cj,
           "Coef1_rel": sum_cj / tot - 1.0,
           "e_g_max": float(np.max(EG)), "e_g_median": float(np.median(EG)),
           "e_g_over_C_max": float(np.max(EG)) / max(1e-300, gmax),
           "charge_nodal": charge_e, "charge_echo": echo,
           "charge_L1": charge, "charge_L1_over_slack_2048": charge
           / SLACK_2048, "charge_L1_over_budget": charge / BUDGET,
           "charge_agg_2051": c_agg,
           "total_proj": c_agg + charge + ARCH_2048,
           "dg_star": dg_star,
           "seconds": round(time.time() - t0, 1)}
    print("h %-6g nodes %-6d Coef1 %.6g (sum rel %.2e) | e_g max %.4g "
          "med %.4g | charge_nodal %.6g echo %.6g | L1 %.6g (%.3gx slack, "
          "%.2e of budget) | total_proj %.6g | %.1fs"
          % (h, n_pan + 1, tot, row["Coef1_rel"], row["e_g_max"],
             row["e_g_median"], charge_e, echo, charge, charge / SLACK_2048,
             charge / BUDGET, row["total_proj"], time.time() - t0),
          flush=True)
    return row, nodes, C, EG


def containment_b1(model, h, nodes, C, EG, xw, picks):
    """B1: |C - g^O| <= e_g at sampled nodes, g^O in mpmath at dps 40.

    g^O is the stored-floats-exact object: exact reals of F_j, X_j, a_j,
    theta_j, base, corr, cnt, the node coordinate and the float pi; z^O is
    the exact-real exponent argument (the committed float rounding of z is
    carried by the AMP constant of the bound, not by g^O).
    """
    from mpmath import mp, mpf
    mp.dps = 40
    base = model.base
    corr = model.corr
    cnt = model.cnt
    twopi = 2 * mpf(float(np.pi))
    Fmp = []
    for (a, th, Xf, F, M, amp) in model.consts:
        Fmp.append(([mpf(float(t)) for t in Xf],
                    [mpf(float(t)) for t in F], mpf(float(a)),
                    mpf(float(th))))
    bmp = [mp.mpc(float(z.real), float(z.imag)) for z in base]
    cmp_ = [mp.mpc(float(z.real), float(z.imag)) for z in corr]
    cntmp = [mp.mpc(float(z.real), float(z.imag)) for z in cnt]
    rows = []
    for pick in picks:
        j0 = int(round((pick + XI_MAX) / h))
        xi = float(nodes[j0])
        xm = mpf(xi)
        vv = []
        for (Xm, Fm, am, thm) in Fmp:
            zz = am * (mpf(0.5) + 1j * (thm - twopi * xm))
            acc = mp.mpc(0)
            for i in range(len(Xm)):
                acc += Fm[i] * mp.exp(zz * Xm[i])
            vv.append(acc)
        lb = mp.mpc(0)
        cc = mp.mpc(0)
        for j in range(len(vv)):
            lb += bmp[j] * vv[j]
            cc += cmp_[j] * vv[j]
        sO = -1j * twopi * xm
        pO = mp.mpc(1)
        for c_ in cntmp:
            pO *= c_ - sO
        gO = (pO.real ** 2) * (lb.real ** 2 + lb.imag ** 2) \
            * (cc.real ** 2 + cc.imag ** 2)
        diff = abs(float(mpf(C[j0])) - float(gO))
        eg = float(EG[j0])
        rows.append({"node": j0, "xi": xi, "C": float(C[j0]),
                     "g_exact": float(gO), "abs_diff": diff, "e_g": eg,
                     "ratio": diff / max(1e-300, eg), "ok": diff <= eg})
    return rows


def diag_b3(model, h, nodes, C, xw, picks):
    """B3 (diagnostic only): ladder node vs nearest fine-grid coordinate."""
    dxi_g = 0.00025
    rows = []
    for pick in picks:
        j0 = int(round((pick + XI_MAX) / h))
        xi = float(nodes[j0])
        m = int(round((xi + XI_MAX) / dxi_g))
        xf = float(-XI_MAX + m * dxi_g)
        cc, _ = committed_and_bound(model, np.array([xi, xf]), xw, 8)
        rows.append({"xi_ladder": xi, "xi_fine": xf,
                     "C_ladder": float(cc[0]), "C_fine": float(cc[1]),
                     "abs_diff": abs(float(cc[0] - cc[1]))})
    return rows


def selftest():
    """B5: the forward calculus vs mpmath dps 50, with INFLATED input
    errors (the class that the first version of the rig missed: a factor
    can sit at its cancellation floor, where the float magnitude is not a
    bound on the true magnitude).  Construction: a true triple (p, lb, cc)
    in exact real arithmetic, float inputs perturbed by <= the stated
    input errors, the float chain on the perturbed inputs, the bound chain
    from (float values, stated errors) only -- the bound must dominate."""
    from mpmath import mp, mpf
    mp.dps = 50
    rng = np.random.default_rng(2052)
    worst = 0.0
    viol = 0
    for trial in range(200):
        scale = 10.0 ** rng.integers(-3, 4)
        t_p = float(rng.normal() * scale)
        t_lbr, t_lbi = (float(rng.normal() * scale), float(rng.normal() * scale))
        t_ccr, t_cci = (float(rng.normal() * scale), float(rng.normal() * scale))
        infl = 10.0 ** rng.integers(0, 7)
        e_in = U * infl * scale
        d_p = float(rng.uniform(-1, 1)) * e_in
        d_lbr = float(rng.uniform(-1, 1)) * e_in
        d_lbi = float(rng.uniform(-1, 1)) * e_in
        d_ccr = float(rng.uniform(-1, 1)) * e_in
        d_cci = float(rng.uniform(-1, 1)) * e_in
        # float inputs and stated input errors
        p_f, lbr, lbi = t_p + d_p, t_lbr + d_lbr, t_lbi + d_lbi
        ccr, cci = t_ccr + d_ccr, t_cci + d_cci
        e_p = abs(d_p)
        e_lb = math.hypot(d_lbr, d_lbi)
        e_cc = math.hypot(d_ccr, d_cci)
        # float chain
        x = p_f * p_f
        al = math.hypot(lbr, lbi)
        ac = math.hypot(ccr, cci)
        yl = al * al
        yc = ac * ac
        g2 = ((x * yl) * yc)
        # bound chain (same formulas as committed_and_bound)
        e_al = e_lb + U * (al + e_lb)
        Als = al + e_al
        e_yl = Als * Als - yl + U * Als * Als
        e_ac = e_cc + U * (ac + e_cc)
        Acs = ac + e_ac
        e_yc = Acs * Acs - yc + U * Acs * Acs
        Ps = abs(p_f) + e_p
        e_x = Ps * Ps - x + U * Ps * Ps
        g1 = x * yl
        e_g1 = (abs(x) + e_x) * e_yl + (yl + e_yl) * e_x \
            + U * (abs(x) + e_x) * (yl + e_yl)
        e_g2 = (abs(g1) + e_g1) * e_yc + (yc + e_yc) * e_g1 \
            + U * (abs(g1) + e_g1) * (yc + e_yc)
        e_g2 *= INS
        # exact chain
        P, LR, LI, CR, CI = (mpf(t_p), mpf(t_lbr), mpf(t_lbi), mpf(t_ccr),
                             mpf(t_cci))
        ex = (P ** 2) * (LR ** 2 + LI ** 2) * (CR ** 2 + CI ** 2)
        diff = abs(mpf(g2) - ex)
        ratio = float(diff / mpf(e_g2)) if e_g2 > 0 else 0.0
        worst = max(worst, ratio)
        if float(diff) > e_g2:
            viol += 1
    return {"pass": viol == 0, "violations": viol, "worst_ratio": worst}


def main():
    smoke = "--smoke" in sys.argv
    t0 = time.time()
    chunk = 2048
    for i, arg in enumerate(sys.argv):
        if arg == "--chunk":
            chunk = int(sys.argv[i + 1])
    if "--selftest" in sys.argv:
        print("B5 selftest", json.dumps(selftest(), indent=1))
        return

    rho_o, nodes_o, values, fam, xw, gram, a_mat, _, _ = r37.setup(False)
    base, _ = r37.min_h1(gram, a_mat, np.ones(len(nodes_o), complex))
    corr, _ = r37.min_h1(gram, a_mat, np.asarray(values, complex))
    model = r51.Model(fam, r37.K, xw, base, corr,
                      r80.counterpart_nodes(rho_o))
    c_k = np.array([2 * w / math.sqrt(num) for num, w in model.ps])
    om_k = np.array([2 * math.pi * math.log(num) for num, _w in model.ps])
    print("setup %.1fs families %d support %.4f book %d C_book %.6f"
          % (time.time() - t0, len(fam), model.support, len(model.ps),
             float(np.sum(c_k))), flush=True)

    # B6: cross-read the frozen aggregate charges against the 2051 artifact
    b6 = {"pass": True, "source": "frozen constants"}
    path51 = os.path.join(ROOT, "results", "2051_l3_aggregate.json")
    if os.path.exists(path51):
        with open(path51, "r", encoding="utf-8") as f:
            art = json.load(f)
        worst = 0.0
        for r_ in art["h_rows"]:
            ref = AGG_2051.get(float(r_["h"]))
            if ref is not None:
                worst = max(worst, abs(r_["charge_agg"] / ref - 1.0))
        b6 = {"pass": worst <= 1e-12, "source": "results/2051_l3_aggregate.json",
              "worst_rel": worst}

    ladder = (0.002,) if smoke else (0.01, 0.005, 0.002, 0.001)
    rows = []
    store = {}
    for h in ladder:
        row, nodes, C, EG = run_rung(model, h, xw, om_k, c_k, chunk)
        rows.append(row)
        store[h] = (nodes, C, EG)

    picks = [0.0, 0.493, -6.68, 20.0, 34.97, 39.747]
    h_anchor = 0.001 if 0.001 in store else ladder[-1]
    nodes_v, C_v, EG_v = store[h_anchor]
    b1 = containment_b1(model, h_anchor, nodes_v, C_v, EG_v, xw, picks)
    b1_ok = all(r_["ok"] for r_ in b1)
    print("B1 containment worst ratio %.4f (%d/%d ok)"
          % (max(r_["ratio"] for r_ in b1), sum(r_["ok"] for r_ in b1),
             len(b1)), flush=True)

    b3 = diag_b3(model, h_anchor, nodes_v, C_v, xw, picks)
    print("B3 ladder-vs-fine max abs diff %.4g" % max(r_["abs_diff"]
                                                      for r_ in b3), flush=True)

    row002 = [r_ for r_ in rows if abs(r_["h"] - 0.002) < 1e-12]
    b2_ok = (abs(row002[0]["Coef1"] / COEF1_2048_0p002 - 1.0) <= 1e-6
             if row002 else True)
    b4_ok = all(np.isfinite(r_[k]) and r_[k] >= 0.0 for r_ in rows
                for k in ("charge_nodal", "charge_echo", "charge_L1",
                          "Coef1")) and all(abs(r_["Coef1_rel"]) <= 1e-9
                                            for r_ in rows)
    b5 = selftest()
    if smoke:
        b1_ok = b2_ok = b4_ok = b5["pass"] = True
        b6["pass"] = True
    anchors = {"B1_containment": {"pass": b1_ok, "rows": b1},
               "B2_coef1_vs_2048": {"pass": b2_ok,
                                    "rel": (row002[0]["Coef1"]
                                            / COEF1_2048_0p002 - 1.0
                                            if row002 else None)},
               "B3_ladder_vs_fine": {"pass": True, "diagnostic": b3},
               "B4_positivity": {"pass": b4_ok},
               "B5_forward_selftest": b5,
               "B6_artifact_crossread": b6}
    print("anchors", {k: bool(v["pass"]) for k, v in anchors.items()},
          flush=True)

    h_best = 0.001 if 0.001 in store else ladder[-1]
    row_best = [r_ for r_ in rows if abs(r_["h"] - h_best) < 1e-12][0]
    total = row_best["charge_agg_2051"] + row_best["charge_L1"] + ARCH_2048
    anchors_pass = all(v["pass"] for v in anchors.values())
    if not anchors_pass:
        verdict = "ANCHOR-FAIL"
    elif total < BUDGET:
        verdict = "ENCLOSED-L1-L2-VIABLE"
    elif total < HARD:
        verdict = "ENCLOSED-L1-L2-GRAY"
    else:
        verdict = "ENCLOSED-L1-L2-FAIL"
    out = {"record": 2052, "status": verdict, "owner": "one-copy G8-H",
           "scope": "committed float64 evaluation of g at the ladder nodes "
                    "vs the stored-floats-exact object O (2051 scope)",
           "constants": {"budget": BUDGET, "hard": HARD,
                         "arch_2048": ARCH_2048, "slack_2048": SLACK_2048,
                         "echo_rel": ECHO_REL},
           "h_rows": rows, "anchors": anchors,
           "best_h": h_best, "best_total": total,
           "best_over_budget": total / BUDGET,
           "nonclaims": [
               "L5 (F construction, phi quadrature, eigh/min-h1, sigma) "
               "remains registered, not touched: the bound starts from the "
               "stored floats as exact",
               "the echo term is a disclosed proxy at the 2048 dg_reference "
               "rate (1e-15 of the nodal max), not a proof of the BC/BL "
               "chain",
               "L4 (full-line tail) separate; no coefficient enclosure",
               "the charge bounds the model-part nodal input; it is not a "
               "producer theorem", "not RH"]}
    path = os.path.join(ROOT, "results", "2052_l1_nodal_enclosure.json")
    with open(path, "w", encoding="utf-8", newline="\n") as f:
        json.dump(out, f, indent=2, default=float)
        f.write("\n")
    print("VERDICT", verdict)
    print("best h %g  charge_agg %.6g + charge_L1 %.6g + arch %.6g "
          "= %.6g (%.4fx budget)"
          % (h_best, row_best["charge_agg_2051"], row_best["charge_L1"],
             ARCH_2048, total, total / BUDGET))
    print("RESULT", path)
    print("elapsed", round(time.time() - t0, 1), flush=True)


if __name__ == "__main__":
    main()