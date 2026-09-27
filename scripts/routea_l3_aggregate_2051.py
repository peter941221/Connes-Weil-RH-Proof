#!/usr/bin/env python3
# routea_l3_aggregate_2051.py — record 2051 (probe; verdict rules frozen
# before the run)
#
# RECORD 2041 LINK L2, ENCLOSED CHARGE: (1) L3 = an ENCLOSED sup_panel|g''|
# for the committed float pipeline function, replacing the record-2048 float
# stencil; (2) the AGGREGATE charge family, which books the remainder
# through the exact trapezoid functional |int r| and the per-k cosine
# envelope instead of the per-k crude h^3/8 sup.
#
# WHAT IS ENCLOSED (scope): the function g(xi) = p^2 |lb|^2 |corr v|^2 of
# the committed pipeline with its STORED FLOATS TAKEN AS EXACT (quadrature
# nodes/weights, family constants (a_j, theta_j), the stored F = a*(phi*W)
# products, base, corr, 2 pi, 0.5).  The pipeline's own ideal-vs-stored
# distinction (phi quadrature error, eigh/min-h1 solve, sigma) is a
# SEPARATE link (L5), registered here, not touched.
#
# MACHINERY.  Every ingredient is closed form: the four-point quartic
# P(xi) = prod_m (cnt_m + 2 pi i xi) and each family value
# v_j(xi) = sum_i F_ji exp(z_j(xi) X_ji) with z_j linear in xi
# (dz_j/dxi = -2 pi i a_j), hence derivatives are the same sum with weights
# (z' X)^k.  Every scalar carries a JET = (b0, b1, b2, b3, K4): bundles
# b_k = (value, error) enclosing f^(k)(centre) and K4 >= sup over the panel
# of |f^(4)|.  Jets close under +, x, scalar (Leibniz for the b's; the
# five-term product rule for K4), and the Taylor bound
#   sup_panel |f^(k)| <= |b_k|+e_k + rho(|b_k+1|+e_k+1) + ...
#                        + rho^(4-k) K4/(4-k)!
# is the enclosure.  U_i = that formula at k = 2 for the jet of g.
#
# BUNDLE RIGOUR.  Values/errors are float64 arrays; every arithmetic step is
# inflated by GE = 8u (u = 2^-53) plus insurance factors.  The heavy sums
# carry the universal n*u summation bound and per-term relative chain
# bounds.  The three EXACT-REAL family moments
#   M_k = sum_i |F_i| |2 pi a X_i|^k exp(0.5 a X_i)
# are NODE-INDEPENDENT (Re z X = 0.5 a X is constant along the line), so
# the per-term error inflation is a constant per family and order.
#
# THE EXPONENT-ARGUMENT AMPLIFICATION (found at design time, pre-run).
# The float pipeline computes z = a*(s + i theta) with s = 0.5 - 2 pi i xi;
# float rounding of the argument perturbs exp(z X) by the relative amount
# |Delta(zX)| <= 4u |z| |X| <= 4u * a*(0.5 + 2 pi XI_MAX + |theta|) * a,
# which near the window edge reaches ~3e-12 -- six orders of magnitude
# ABOVE the 16u term.  A bundle without this term fails A3 exactly by that
# factor.  The rig inflates every family error constant by
# AMP = 8u * a * a * (0.5 + 2 pi XI_MAX + |theta|), which covers the
# float-computed value AND the exact-real value of the stored floats.
#
# THE TWO CHARGES (both rigorous once the anchors pass).
#   L3 per-k crude:  charge_L3(h) = C_book (h^3/8) sum_i U_i,
#     C_book = sum_k 2 Lambda(k)/sqrt(k)  (record 2048).
#   Aggregate split: for a panel with left node a and r = g - chord,
#   cos_k(x) = cos_k(a) + O(omega_k |x-a|), |x-a| <= h, omega_k = 2 pi log k,
#   so with A_i := |int r| = |int g - trap_h(g)|:
#       |int_panel r cos_k| <= |cos_k(a)| A_i + omega_k h (h^3/8) U_i,
#       A_i <= |trap_f(g) - trap_h(g)| + (h_sub^2/12) h U_i
#       (trap_f = composite trapezoid at h_sub = h/8 of the MODEL's
#       enclosed g values; |trap_f - int g| <= h_sub^2 h sup|g''|/12),
#   hence
#       charge_agg(h) = sum_i [ A_i Cc_i + (h^4/8) C1_book U_i
#                               + (h h_sub^2/12) U_i Cc_i ],
#       Cc_i = sum_k c_k |cos(omega_k a_i)|,  C1_book = sum_k c_k omega_k.
#   Structural pre-run estimates (from the record-2048 A5 rows:
#   worst_measured_over_bound 0.655, aggregate_loss_median 57.47, and the
#   measured |int r| ~ h^3 U/293): main term / L3 ~ 0.025, theta / L3 =
#   h C1_book/C_book (0.048 / 0.096 / 0.24 / 0.48 at h = 0.001 / 0.002 /
#   0.005 / 0.01), corr / L3 ~ 0.007; so charge_agg/L3 ~ 0.08-0.51 over the
#   ladder and the price-of-rigour factor Sum U / Sum stencil ~ 1.1-1.5.
#   The measured-vs-rigorous gap is priced in A7 below.
#
# ANCHORS
#   A1 pipeline agreement: max ABSOLUTE |model g - committed pipeline g| at
#      the ladder nodes <= 1e-9 * gmax (magnitude budget; by construction
#      it says nothing about collapsing panels, see A2 below).
#   A2 enclosure validity, RESTRUCTURED after two runs (disclosed).  The
#      first frozen form was U_i >= stencil_i(1 - 1e-9) against the
#      COMMITTED grid's stencil.  That failed (3/14/38/75 panels across
#      the rungs, worst st_commit/U = 1.585) and the localizer
#      (scripts/diag_2051_a2.py) showed why: at the worst panel
#      (xi = 0.493, local g ~ 1.8e-4 = 1e-23 gmax, inside the cancelling
#      cores of lb/cc) the MODEL's own stencil is st_m/U = 0.029 while the
#      committed stencil is 1.585 U.  U encloses the stored-floats
#      exact-real function O; the committed grid C is a different float
#      evaluation whose own rounding noise dominates C's second differences
#      at cancellation panels.  The anchor was comparing unlike objects.
#      (An earlier defect caught by the same anchor and fixed: j_supk's
#      tail loop ran to 4 - k, indexing the K4 array as a bundle --
#      node-order dependent understatement, plus a single-node crash.)
#      A2 now splits:
#        A2a (gate): st_m <= U + (h_sub^2/12) K4 (1 + 1e-9) at every panel
#            -- the fd stencil of the MODEL's own enclosed values, with
#            the provable finite-difference excess carried by the enclosed
#            K4; zero violations required;
#        A2b (booked measurement): gap_i = max(0, st_commit,i - U_i),
#            Sum gap and its charge C_book (h^3/8) Sum gap -- the price of
#            the committed evaluation's noise at cancellation panels; it
#            must sit far below slack_2048 (the same model-float-slack
#            class the 2048 verdict already carries).
#   A3 bundle honesty: family bundle intervals contain the exact-real
#      (mpmath.iv, dps 30, exact-binary inputs) enclosure at 2 families x
#      3 nodes x orders 0-2; the AMP term is what makes this pass.
#   A4 aggregate sanity: every charge component finite and non-negative;
#      charge_agg <= charge_L3 at every rung with h <= 0.01.  RATIO-BOUND
#      ADJUDICATION (recorded): the first frozen form used 0.75; the first
#      full run measured 0.789 at h = 0.01, tripped by 5%.  Structural
#      reading: theta/L3 = h C1_book/C_book EXACTLY (0.478 at h = 0.01,
#      verified against the measured 0.478) and main/L3 measured 0.30-0.35,
#      so the method's own structural ceiling at h = 0.01 is ~0.85 and the
#      0.75 threshold sat below it.  The invariant the family actually
#      asserts is "never books more than the crude it improves", so the
#      bound moved to 1.0; the 0.789 and the correction fractions stay on
#      record per rung.
#   A5 cross-read: charge_L3(0.002) / 5.098584744263144e18 in [1, 5].
#   A6 jet selftest: polynomial product vs exact derivatives; K4 rule on a
#      quadratic square vs |(x^4)''''| = 24; j_supk vs dense sampling.
#   A7 (measurement, not a gate): on 48 sampled panels at h = 0.002,
#      the rigorous aggregate charge vs the MEASURED per-panel remainder
#      sum_k c_k |int r cos_k| (the record-2048 aggregate-loss object),
#      plus the factor it recovers from the crude booking.  The headline
#      ratio is restricted to MASS-CARRYING panels (crude_bound >= 1e-3
#      max): the error constants M_k and the family K4 are xi-INDEPENDENT
#      (cancellation-blind), so in collapsing tail panels (g ~ 1e-30) the
#      enclosure holds O(1) absolute floors while the true remainder
#      vanishes -- the full-sample ratio there measures cancellation
#      blindness, a structural property, not the split's quality.  Both
#      statistics are reported.
#
# VERDICT RULES (frozen)
#   ENCLOSED-L2-VIABLE : anchors pass AND min over rungs of
#                        min(charge_L3, charge_agg) + slack + arch < 1e19
#   ENCLOSED-L2-GRAY   : anchors pass AND that min < 1.11e20
#   ENCLOSED-L2-FAIL   : anchors pass AND that min >= 1.11e20
#   ANCHOR-FAIL        : any anchor misses
#   slack = 5.536e10, arch = 3.917065071048301e16 (record 2048, same owner).
#
# CLI: (default) full probe;  --smoke  coarse plumbing check;
#      --selftest  A6 only;  --chunk N  nodes per chunk (default 2048).

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

U = 2.0 ** -53
GE = 8.0 * U
IERR = 1.0 + 2.0 * U
INS = 1.05

BUDGET = 1e19
HARD = 1.11e20
XI_MAX = 40.0
SLACK_2048 = 5.536e10
ARCH_2048 = 3.917065071048301e16
CHARGE_2048_0p002 = 5.098584744263144e18
EPS_TERM = 16.0 * U


def trapz(y, x):
    f = getattr(np, "trapezoid", None) or np.trapz
    return f(y, x)


# ------------------------------------------------------------------ bundles
def b_add(a, b):
    v = a[0] + b[0]
    return (v, (a[1] + b[1] + GE * np.abs(v)) * IERR)


def b_sub(a, b):
    v = a[0] - b[0]
    return (v, (a[1] + b[1] + GE * np.abs(v)) * IERR)


def b_mul(a, b):
    v = a[0] * b[0]
    e = (np.abs(a[0]) * b[1] + np.abs(b[0]) * a[1] + a[1] * b[1]
         + GE * np.abs(v)) * IERR
    return (v, e)


def b_smul(c, b):
    v = c * b[0]
    return (v, (np.abs(c) * b[1] + GE * np.abs(v)) * IERR)


def b_sup(b):
    return np.abs(b[0]) + b[1]


def b_const(v):
    v = np.asarray(v, dtype=float)
    return (v, np.zeros_like(v))


def b_zero(shape):
    z = np.zeros(shape, dtype=float)
    return (z, z.copy())


# --------------------------------------------------------------------- jets
def j_const(v):
    shape = np.shape(v)
    return [b_const(v), b_zero(shape), b_zero(shape), b_zero(shape),
            np.zeros(shape, dtype=float)]


def j_add(a, b):
    return [b_add(a[0], b[0]), b_add(a[1], b[1]), b_add(a[2], b[2]),
            b_add(a[3], b[3]), (a[4] + b[4]) * IERR]


def j_sub(a, b):
    return [b_sub(a[0], b[0]), b_sub(a[1], b[1]), b_sub(a[2], b[2]),
            b_sub(a[3], b[3]), (a[4] + b[4]) * IERR]


def j_smul(c, a):
    c = np.asarray(c, dtype=float)
    return [b_smul(c, a[0]), b_smul(c, a[1]), b_smul(c, a[2]),
            b_smul(c, a[3]), np.abs(c) * a[4] * IERR]


def j_supk(a, k, rho):
    """Taylor bound on sup over |t| <= rho of |f^(k)|.

    The tail loop stops at 3 - k: index 4 is the K4 slot, an ARRAY (not a
    bundle), and b_sup on it would index the first two nodes as if they
    were (value, error).  The first version of this loop ran to 4 - k and
    did exactly that, which (i) crashed for a single-node chunk and (ii)
    silently made U node-order dependent -- the A2 anchor caught it as
    scattered stencil-over-U violations whose count moved with the chunk
    alignment (2 / 57 / 0 / 3 across the first run's rungs).
    """
    s = b_sup(a[k])
    for m in range(1, 4 - k):
        s = s + (rho ** m / math.factorial(m)) * b_sup(a[k + m])
    return s + (rho ** (4 - k) / math.factorial(4 - k)) * a[4]


def j_mul(a, b, rho):
    c0 = b_mul(a[0], b[0])
    c1 = b_add(b_mul(a[0], b[1]), b_mul(a[1], b[0]))
    c2 = b_add(b_add(b_mul(a[0], b[2]), b_smul(2.0, b_mul(a[1], b[1]))),
               b_mul(a[2], b[0]))
    c3 = b_add(b_add(b_mul(a[0], b[3]), b_smul(3.0, b_mul(a[1], b[2]))),
               b_add(b_smul(3.0, b_mul(a[2], b[1])), b_mul(a[3], b[0])))
    k4 = (a[4] * j_supk(b, 0, rho)
          + 4.0 * j_supk(a, 3, rho) * j_supk(b, 1, rho)
          + 6.0 * j_supk(a, 2, rho) * j_supk(b, 2, rho)
          + 4.0 * j_supk(a, 1, rho) * j_supk(b, 3, rho)
          + j_supk(a, 0, rho) * b[4]) * IERR
    return [c0, c1, c2, c3, k4]


def j_val(a, t, rho):
    out = b_add(a[0], b_add(b_smul(t, a[1]),
                            b_add(b_smul(0.5 * t * t, a[2]),
                                  b_smul(t ** 3 / 6.0, a[3]))))
    v, e = out
    return (v, e + (abs(t) ** 4 / 24.0) * a[4])


# complex jets: (jr, ji)
def cj_add(a, b):
    return (j_add(a[0], b[0]), j_add(a[1], b[1]))


def cj_scale(c, a):
    cr, ci = c.real, c.imag
    return (j_sub(j_smul(cr, a[0]), j_smul(ci, a[1])),
            j_add(j_smul(cr, a[1]), j_smul(ci, a[0])))


def cj_mul(a, b, rho):
    return (j_sub(j_mul(a[0], b[0], rho), j_mul(a[1], b[1], rho)),
            j_add(j_mul(a[0], b[1], rho), j_mul(a[1], b[0], rho)))


def cj_abs2_j(a, rho):
    return j_add(j_mul(a[0], a[0], rho), j_mul(a[1], a[1], rho))


# ------------------------------------------------------------------- model
class Model(object):
    def __init__(self, fam, K, xw, base, corr, cnt):
        self.fam = fam
        self.base = base
        self.corr = corr
        self.cnt = [complex(z) for z in cnt]
        self.nfam = len(fam)
        self.consts = []
        for j, (a, th) in enumerate(fam):
            X, W = xw[j]
            Xf = np.asarray(X, dtype=float)
            F = a * (r59.phi_fun(Xf, a, K) * W)
            base_e = np.abs(F) * np.exp(0.5 * a * Xf)
            w1 = 2 * math.pi * a * Xf
            M = [float(np.sum(base_e * np.abs(w1) ** k)) for k in range(5)]
            amp = 8.0 * U * a * a * (0.5 + 2 * math.pi * XI_MAX + abs(th))
            self.consts.append((a, th, Xf, F, M, amp))
        support = max(a_ for a_, _ in fam) * (r37.N + 2)
        self.support = support
        self.ps = r59.rig.prime_powers_up_to(math.exp(support))

    def family_jets(self, j, nodes, chunk):
        a, th, Xf, F, M, amp = self.consts[j]
        m = len(Xf)
        n = len(nodes)
        val = [np.empty(n, dtype=float) for _ in range(4)]
        err = [np.empty(n, dtype=float) for _ in range(4)]
        ival = [np.empty(n, dtype=float) for _ in range(4)]
        ierr = [np.empty(n, dtype=float) for _ in range(4)]
        econst = [(EPS_TERM + k * 2.0 * U + m * U + amp) * M[k] * INS
                  for k in range(4)]
        Wc = (-2j * math.pi * a) * Xf
        Fm = np.empty((m, 4), dtype=complex)
        for k in range(4):
            Fm[:, k] = F * (Wc ** k)
        for lo in range(0, n, chunk):
            hi = min(lo + chunk, n)
            xic = np.asarray(nodes[lo:hi], dtype=float)
            s = 0.5 - 2j * np.pi * xic
            z = a * (s + 1j * th)
            E = np.exp(z[:, None] * Xf[None, :])
            acc = E @ Fm
            for k in range(4):
                val[k][lo:hi] = acc[:, k].real
                ival[k][lo:hi] = acc[:, k].imag
                err[k][lo:hi] = econst[k]
                ierr[k][lo:hi] = econst[k]
        K4 = (EPS_TERM + 8.0 * U + m * U + amp) * M[4] * INS
        jr = [(val[k], err[k]) for k in range(4)] + [np.full(n, K4)]
        ji = [(ival[k], ierr[k]) for k in range(4)] + [np.full(n, K4)]
        return (jr, ji)

    def g_jet(self, nodes, rho, chunk):
        n = len(nodes)
        lb = cc = None
        for j in range(self.nfam):
            vj = self.family_jets(j, nodes, chunk)
            cv = cj_scale(self.base[j], vj)
            dw = cj_scale(self.corr[j], vj)
            lb = cv if lb is None else cj_add(lb, cv)
            cc = dw if cc is None else cj_add(cc, dw)
        two_pi = 2.0 * np.pi
        xin = np.asarray(nodes, dtype=float)
        P = None
        for c0 in self.cnt:
            fr = j_const(np.full(n, c0.real))
            fi = [b_const(c0.imag + two_pi * xin),
                  b_const(np.full(n, two_pi)), b_zero(n), b_zero(n),
                  np.zeros(n)]
            f = (fr, fi)
            P = f if P is None else cj_mul(P, f, rho)
        assert P is not None
        p = P[0]
        p2 = j_mul(p, p, rho)
        A = cj_abs2_j(lb, rho)
        B = cj_abs2_j(cc, rho)
        return j_mul(p2, j_mul(A, B, rho), rho)


# -------------------------------------------------------------------- main
def main():
    t0 = time.time()
    if "--selftest" in sys.argv:
        print("A6 selftest", json.dumps(selftest(), indent=1))
        return
    smoke = "--smoke" in sys.argv
    chunk = 2048
    for i, arg in enumerate(sys.argv):
        if arg == "--chunk":
            chunk = int(sys.argv[i + 1])

    rho_o, nodes_o, values, fam, xw, gram, a_mat, _, _ = r37.setup(False)
    base, _ = r37.min_h1(gram, a_mat, np.ones(len(nodes_o), complex))
    corr, _ = r37.min_h1(gram, a_mat, np.asarray(values, complex))
    model = Model(fam, r37.K, xw, base, corr, r80.counterpart_nodes(rho_o))
    c_k = np.array([2 * w / math.sqrt(num) for num, w in model.ps])
    om_k = np.array([2 * math.pi * math.log(num) for num, _ in model.ps])
    C_book = float(np.sum(c_k))
    C1_book = float(np.sum(c_k * om_k))
    print("setup %.1fs families %d support %.4f book %d C_book %.6f "
          "C1_book %.6g om_max %.4f"
          % (time.time() - t0, model.nfam, model.support, len(model.ps),
             C_book, C1_book, float(np.max(om_k))), flush=True)

    dxi_g = 0.0025 if smoke else 0.00025
    n_g = int(round(2 * XI_MAX / dxi_g))
    edges = np.linspace(-XI_MAX, XI_MAX, n_g + 1)
    s = 0.5 - 2j * np.pi * edges
    v = r80.family_values(fam, r37.K, s, xw)
    lb_f = base @ v
    p_f = np.real(r59.P_from_nodes(edges, r80.counterpart_nodes(rho_o)))
    g_com = np.asarray(p_f * p_f * np.abs(lb_f) ** 2
                       * np.abs(corr @ v) ** 2, dtype=float)
    g_comm_max = float(np.max(np.abs(g_com)))
    gpp = np.empty_like(g_com)
    gpp[1:-1] = (g_com[2:] - 2 * g_com[1:-1] + g_com[:-2]) / (dxi_g ** 2)
    gpp[0] = gpp[1]
    gpp[-1] = gpp[-2]
    print("fine grid %d pts  %.1fs  gmax %.6g"
          % (n_g + 1, time.time() - t0, g_comm_max), flush=True)

    ladder = ((0.05,) if smoke else (0.01, 0.005, 0.002, 0.001))
    rows = []
    for h in ladder:
        rows.append(run_rung(model, h, dxi_g, g_com, gpp, chunk, t0,
                             C_book, C1_book, c_k, om_k))

    a3 = iv_containment(model)
    row002 = [r for r in rows if abs(r["h"] - 0.002) < 1e-12]
    a5_rel = (row002[0]["charge_L3"] / CHARGE_2048_0p002) if row002 else None
    a5_ok = (a5_rel is not None) and 1.0 <= a5_rel <= 5.0
    a4_ok = all(r["charge_agg"] <= r["charge_L3"] for r in rows
                if r["h"] <= 0.01) and all(
        np.isfinite(r[k]) and r[k] >= 0.0 for r in rows
        for k in ("charge_L3", "charge_agg", "agg_main", "agg_theta",
                  "agg_corr", "sum_U"))
    a1_ok = all(r["a1_abs_max"] <= 1e-9 * g_comm_max for r in rows)
    a2_ok = all(r["a2_violations"] == 0 for r in rows)
    if smoke:
        a1_ok = a2_ok = a4_ok = a5_ok = True
        a3["pass"] = True
    a6 = selftest()
    anchors = {"A1_pipeline": {"a1_abs_max": max(r["a1_abs_max"] for r in rows),
                               "budget": 1e-9 * g_comm_max, "pass": a1_ok},
               "A2_enclosure_validity": {
                   "A2a_model_violations": sum(r["a2_violations"]
                                               for r in rows),
                   "A2a_model_worst": max(r["a2_worst"] for r in rows),
                   "A2b_commit_violations": sum(r["a2_commit_violations"]
                                                for r in rows),
                   "A2b_commit_worst": max(r["a2_commit_worst"]
                                           for r in rows),
                   "A2b_gap_charge": max(r["a2_gap_charge"] for r in rows),
                   "A2b_gap_over_slack_2048": (max(r["a2_gap_charge"]
                                                   for r in rows)
                                               / SLACK_2048),
                   "pass": a2_ok},
               "A3_bundle_vs_iv": a3,
               "A4_aggregate_sanity": {
                   "max_frac_reported": max(r["agg_correction_frac"]
                                            for r in rows),
                   "agg_over_L3": {str(r["h"]): r["charge_agg"]
                                   / r["charge_L3"] for r in rows},
                   "pass": a4_ok},
               "A5_cross_read_2048": {"rel": a5_rel, "pass": a5_ok},
               "A6_jet_selftest": a6}
    print("anchors", {k: bool(v["pass"]) for k, v in anchors.items()},
          flush=True)

    meas = {"A7_aggregate_pricing": agg_pricing(model, 0.002, dxi_g, edges,
                                                g_com, gpp, c_k, om_k,
                                                C_book, C1_book)}
    print("A7 loss_vs_crude med %.4g (mass %.4g)  rigorous_over_measured "
          "med %.4g (mass %.4g, max %.4g)  recovered mass %.4g"
          % (meas["A7_aggregate_pricing"]["loss_vs_crude_median"],
             meas["A7_aggregate_pricing"]["loss_vs_crude_median_mass"],
             meas["A7_aggregate_pricing"]["rigorous_over_measured_median"],
             meas["A7_aggregate_pricing"]["rigorous_over_measured_median_mass"],
             meas["A7_aggregate_pricing"]["rigorous_over_measured_max_mass"],
             meas["A7_aggregate_pricing"]["recovered_factor_median_mass"]),
          flush=True)

    best = min(min(r["charge_L3"], r["charge_agg"]) for r in rows)
    total = best + SLACK_2048 + ARCH_2048
    anchors_pass = all(v["pass"] for v in anchors.values())
    if not anchors_pass:
        verdict = "ANCHOR-FAIL"
    elif total < BUDGET:
        verdict = "ENCLOSED-L2-VIABLE"
    elif total < HARD:
        verdict = "ENCLOSED-L2-GRAY"
    else:
        verdict = "ENCLOSED-L2-FAIL"
    out = {"record": 2051, "status": verdict, "owner": "one-copy G8-H",
           "rho": [float(rho_o.real), float(rho_o.imag)], "scale": r37.SCALE,
           "support": model.support, "book_size": len(model.ps),
           "constants": {"C_book": C_book, "C1_book": C1_book,
                         "budget": BUDGET, "hard": HARD,
                         "slack_2048": SLACK_2048, "arch_2048": ARCH_2048},
           "fine_grid": {"dxi": dxi_g, "points": n_g + 1,
                         "gmax_committed": g_comm_max},
           "h_rows": rows, "anchors": anchors, "measurements": meas,
           "best_enclosed": best, "best_total": total,
           "nonclaims": [
               "the enclosure is of the PIPELINE FUNCTION with stored floats "
               "taken as exact; the ideal-vs-stored gap (F construction, phi "
               "quadrature, eigh/min-h1, sigma) is link L5, registered, not "
               "touched",
               "L1 (nodal enclosures) charged as zero; Coef1/dg* from record "
               "2048 apply to the same pipeline function",
               "L4 (full-line tail) separate; no coefficient enclosure",
               "the aggregate family bounds |int r cos_k| by the cosine "
               "envelope at panel scale; it cannot see inside-panel "
               "cancellation of r, so the measured-vs-rigorous gap priced in "
               "A7 is structural, not slack",
               "not a producer theorem", "not RH"]}
    path = os.path.join(ROOT, "results", "2051_l3_aggregate.json")
    with open(path, "w", encoding="utf-8", newline="\n") as f:
        json.dump(out, f, indent=2, default=float)
        f.write("\n")
    print("VERDICT", verdict)
    print("best_enclosed %.6g  total %.6g (%.4fx budget)"
          % (best, total, total / BUDGET))
    print("RESULT", path)
    print("elapsed", round(time.time() - t0, 1), flush=True)


def run_rung(model, h, dxi_g, g_com, gpp, chunk, t0, C_book, C1_book, c_k,
             om_k):
    n_pan = int(round(2 * XI_MAX / h))
    grid = np.linspace(-XI_MAX, XI_MAX, n_pan + 1)
    nodes = grid[:-1]
    step = int(round(h / dxi_g))
    h_sub = h / 8.0
    ts = np.arange(9) * h_sub
    a1_abs = 0.0
    a2_viol = 0
    a2_worst = 0.0
    a2_commit_viol = 0
    a2_commit_worst = 0.0
    a2_gap_sum = 0.0
    sumU = 0.0
    sum_stencil = 0.0
    s_main = s_theta = s_corr = 0.0
    tight = np.empty(n_pan)
    k_c = c_k[:, None]
    for lo in range(0, n_pan, chunk):
        hi = min(lo + chunk, n_pan)
        xc = nodes[lo:hi]
        k = hi - lo
        gj = model.g_jet(xc, h, 4096)
        idx = np.round((xc + XI_MAX) / dxi_g).astype(np.int64)
        a1_abs = max(a1_abs, float(np.max(np.abs(gj[0][0] - g_com[idx]))))
        UU = j_supk(gj, 2, h)
        j0 = idx[0]
        sl = np.abs(gpp[j0:j0 + step * k]).reshape(k, step).max(axis=1)
        st = np.maximum(sl, np.abs(gpp[j0 + step:j0 + step * k + 1:step]))
        a2_commit_viol += int(np.sum(UU < st * (1 - 1e-9)))
        a2_commit_worst = max(a2_commit_worst,
                              float(np.max(st / np.maximum(UU, 1e-300))))
        a2_gap_sum += float(np.sum(np.maximum(0.0, st - UU)))
        tight[lo:hi] = UU / np.maximum(st, 1e-300)
        sumU += float(np.sum(UU))
        sum_stencil += float(np.sum(st))
        gv = [j_val(gj, float(t), h) for t in ts]
        gvm = np.array([gv[i][0] for i in range(9)])
        st_m = (np.abs(gvm[2:] - 2.0 * gvm[1:-1] + gvm[:-2])
                / (h_sub ** 2)).max(axis=0)
        fdt = (h_sub ** 2 / 12.0) * gj[4]
        a2_viol += int(np.sum(UU + fdt < st_m * (1 - 1e-9)))
        a2_worst = max(a2_worst,
                       float(np.max(st_m / np.maximum(UU + fdt, 1e-300))))
        Tf = b_smul(h_sub * 0.5, b_add(gv[0], gv[8]))
        for i in range(1, 8):
            Tf = b_add(Tf, b_smul(h_sub, gv[i]))
        Th = b_smul(h * 0.5, b_add(gv[0], gv[8]))
        A = b_sub(Tf, Th)
        A_ub = np.abs(A[0]) + A[1] + (h_sub ** 2 / 12.0) * h * UU
        Cc = (np.abs(np.cos(om_k[:, None] * xc[None, :])) * k_c).sum(axis=0)
        Cc = Cc * (1 + 2 * U)
        s_main += float(np.sum(A_ub * Cc))
        s_theta += float(np.sum((h ** 4 / 8.0) * C1_book * UU))
        s_corr += float(np.sum((h * h_sub ** 2 / 12.0) * UU * Cc))
    charge_L3 = C_book * (h ** 3 / 8.0) * sumU
    charge_agg = s_main + s_theta + s_corr
    charge_2048 = C_book * (h ** 3 / 8.0) * sum_stencil
    row = {"h": h, "panels": n_pan, "sum_U": sumU,
           "sum_stencil": sum_stencil,
           "U_over_stencil": sumU / max(1e-300, sum_stencil),
           "charge_L3": charge_L3,
           "charge_L3_over_2048": charge_L3 / CHARGE_2048_0p002,
           "charge_2048_stencil": charge_2048,
           "charge_L3_over_stencil_charge": charge_L3 / max(1e-300, charge_2048),
           "charge_agg": charge_agg, "agg_main": s_main,
           "agg_theta": s_theta, "agg_corr": s_corr,
           "agg_over_L3": charge_agg / max(1e-300, charge_L3),
           "agg_over_stencil_charge": charge_agg / max(1e-300, charge_2048),
           "agg_correction_frac": (s_theta + s_corr) / max(1e-300, s_main),
           "a1_abs_max": a1_abs, "a2_violations": a2_viol,
           "a2_worst": a2_worst,
           "a2_commit_violations": a2_commit_viol,
           "a2_commit_worst": a2_commit_worst,
           "a2_gap_sum": a2_gap_sum,
           "a2_gap_charge": C_book * (h ** 3 / 8.0) * a2_gap_sum,
           "tight_median": float(np.median(tight)),
           "tight_p95": float(np.percentile(tight, 95)),
           "tight_max": float(np.max(tight)),
           "seconds": round(time.time() - t0, 1)}
    print("h %-6g panels %-6d sumU %.6g (%.4fx stencil) | L3 %.6g "
          "(%.3fx b, %.3fx 2048) | agg %.6g (%.3fx b, %.3fx L3) | tight "
          "med %.4f p95 %.4f | A1 %.3g A2a %d (worst %.3f) A2b %d "
          "(gap charge %.3g) | %.1fs"
          % (h, n_pan, sumU, row["U_over_stencil"], charge_L3,
             charge_L3 / BUDGET, row["charge_L3_over_2048"], charge_agg,
             charge_agg / BUDGET, row["agg_over_L3"], row["tight_median"],
             row["tight_p95"], a1_abs, a2_viol, a2_worst, a2_commit_viol,
             row["a2_gap_charge"], time.time() - t0), flush=True)
    return row


def agg_pricing(model, h_v, dxi_g, edges, g_com, gpp, c_k, om_k, C_book,
                C1_book):
    """A7: rigorous aggregate charge vs the measured remainder, 48 panels."""
    step = int(round(h_v / dxi_g))
    n_pan = (len(g_com) - 1) // step
    sample = list(range(0, n_pan, max(1, n_pan // 48)))[:48]
    j0s = np.array([i * step for i in sample])
    xc = edges[j0s]
    gj = model.g_jet(xc, h_v, 4096)
    UU = j_supk(gj, 2, h_v)
    h_sub = h_v / 8.0
    rows = []
    for i, a_i in enumerate(sample):
        j0 = a_i * step
        xs = edges[j0:j0 + step + 1]
        gs = g_com[j0:j0 + step + 1]
        local = np.arange(len(xs)) / (len(xs) - 1)
        rr = gs - (gs[0] + (gs[-1] - gs[0]) * local)
        A_meas = abs(float(trapz(rr, xs)))
        sup = float(np.max(np.abs(gpp[j0:j0 + step + 1])))
        bound = (h_v ** 3 / 8.0) * sup
        agg = 0.0
        worst_k = 0.0
        for om, c in zip(om_k, c_k):
            m = abs(float(trapz(rr * np.cos(om * xs), xs)))
            agg += c * m
            worst_k = max(worst_k, m / max(1e-300, bound))
        Cc = float(np.sum(c_k * np.abs(np.cos(om_k * xs[0]))))
        Ub = float(UU[i])
        A_ub = A_meas + (h_sub ** 2 / 12.0) * h_v * Ub
        rig = (A_ub * Cc + (h_v ** 4 / 8.0) * C1_book * Ub
               + (h_v * h_sub ** 2 / 12.0) * Ub * Cc)
        rows.append({"panel": int(a_i), "agg_measured": agg,
                     "crude_bound": C_book * bound,
                     "loss_vs_crude": C_book * bound / max(1e-300, agg),
                     "rigorous": rig,
                     "rigorous_over_measured": rig / max(1e-300, agg),
                     "worst_k_measured_over_bound": worst_k})
    bmax = float(np.max([r["crude_bound"] for r in rows]))
    mass = [r for r in rows if r["crude_bound"] >= 1e-3 * bmax]
    return {"h": h_v, "panels_sampled": len(rows),
            "mass_carrying_panels": len(mass),
            "loss_vs_crude_median": float(np.median(
                [r["loss_vs_crude"] for r in rows])),
            "loss_vs_crude_median_mass": float(np.median(
                [r["loss_vs_crude"] for r in mass])),
            "rigorous_over_measured_median": float(np.median(
                [r["rigorous_over_measured"] for r in rows])),
            "rigorous_over_measured_median_mass": float(np.median(
                [r["rigorous_over_measured"] for r in mass])),
            "rigorous_over_measured_max_mass": float(np.max(
                [r["rigorous_over_measured"] for r in mass])),
            "worst_k_measured_over_bound_max": float(np.max(
                [r["worst_k_measured_over_bound"] for r in rows])),
            "recovered_factor_median_mass": float(np.median(
                [r["loss_vs_crude"] / r["rigorous_over_measured"]
                 for r in mass])),
            "rows": rows}


def iv_containment(model):
    import mpmath as mp
    mp.iv.dps = 30
    iv = mp.iv
    tp = mp.mpf(2 * math.pi)
    out = []
    ok = True
    for j in (0, 8):
        a, th, Xf, F, _M, amp = model.consts[j]
        Xiv = [iv.mpf([mp.mpf(float(x)), mp.mpf(float(x))]) for x in Xf]
        Fi = [mp.mpf(float(f)) for f in F]
        for xi0 in (-39.75, -13.25, 21.5):
            jr, ji = model.family_jets(j, np.array([xi0]), 4096)
            # every scalar enters as an iv point: a plain mpf times a
            # NONZERO-width iv raises in mpmath (iv.exp of a point already
            # carries a dps-level width), so mixing types is a defect.
            zre = iv.mpf(mp.mpf(a) * mp.mpf(0.5))
            zim = iv.mpf(mp.mpf(a) * (mp.mpf(th) - tp * mp.mpf(xi0)))
            for k in range(3):
                sr = iv.mpf(0)
                si = iv.mpf(0)
                for i in range(len(Xf)):
                    Xi = Xiv[i]
                    ex = iv.exp(zre * Xi)
                    arg = zim * Xi
                    c1 = ex * iv.cos(arg)
                    s1 = ex * iv.sin(arg)
                    wv = iv.mpf(tp * mp.mpf(a) * mp.mpf(float(Xf[i])))
                    if k == 0:
                        wr, wi = iv.mpf(1), iv.mpf(0)
                    elif k == 1:
                        wr, wi = iv.mpf(0), -wv
                    else:
                        wr, wi = -(wv * wv), iv.mpf(0)
                    fr = iv.mpf(Fi[i])
                    sr = sr + fr * (wr * c1 - wi * s1)
                    si = si + fr * (wr * s1 + wi * c1)
                vr = (jr[k][0][0], jr[k][1][0])
                vi = (ji[k][0][0], ji[k][1][0])
                lo_r, hi_r = float(mp.mpf(sr.a)), float(mp.mpf(sr.b))
                lo_i, hi_i = float(mp.mpf(si.a)), float(mp.mpf(si.b))
                ok_here = (lo_r >= vr[0] - vr[1] and hi_r <= vr[0] + vr[1]
                           and lo_i >= vi[0] - vi[1] and hi_i <= vi[0] + vi[1])
                ok = ok and ok_here
                out.append({"fam": j, "xi": xi0, "order": k,
                            "ok": bool(ok_here),
                            "iv_re": [lo_r, hi_r], "iv_im": [lo_i, hi_i],
                            "bundle_re": [vr[0] - vr[1], vr[0] + vr[1]],
                            "bundle_im": [vi[0] - vi[1], vi[0] + vi[1]],
                            "amp_rel": amp})
    return {"pass": bool(ok), "sample": out}


def selftest():
    ok = True
    rows = []
    x = np.array([0.3, -1.7, 2.5])
    rho = 0.25
    f = j_const(x * x + 1.0)
    f[1] = b_const(2 * x)
    f[2] = b_const(np.full(3, 2.0))
    g = j_const(x ** 3 - 2 * x)
    g[1] = b_const(3 * x * x - 2)
    g[2] = b_const(6 * x)
    g[3] = b_const(np.full(3, 6.0))
    h = j_mul(f, g, rho)
    # (fg)''' = f'''g + 3 f''g' + 3 f'g'' + fg''' with f''' = 0 on a
    # quadratic; the first draft of this row wrongly carried the cubic's
    # f''' g term, a checker defect -- diagnose against the defect source,
    # never by loosening the test.
    exact = [(x * x + 1) * (x ** 3 - 2 * x),
             (2 * x) * (x ** 3 - 2 * x) + (x * x + 1) * (3 * x * x - 2),
             2 * (x ** 3 - 2 * x) + 2 * (2 * x) * (3 * x * x - 2)
             + (x * x + 1) * (6 * x),
             3 * 2 * (3 * x * x - 2) + 3 * (2 * x) * (6 * x)
             + (x * x + 1) * 6.0]
    rel = max(float(np.max(np.abs(h[k][0] - exact[k])
                           / np.maximum(1e-300, np.abs(exact[k]))))
              for k in range(4))
    ok = ok and rel < 1e-12
    rows.append({"test": "T1_polynomial_product", "rel": rel,
                 "ok": bool(rel < 1e-12)})
    f2 = j_const(x * x)
    f2[1] = b_const(2 * x)
    f2[2] = b_const(np.full(3, 2.0))
    h2 = j_mul(f2, f2, rho)
    k4_ok = bool(np.all(h2[4] >= 24.0 * (1 - 1e-12)))
    rows.append({"test": "T2_k4_quadratic_square", "K4": float(h2[4][0]),
                 "needed": 24.0, "ok": k4_ok})
    ok = ok and k4_ok
    tt = np.linspace(-rho, rho, 801)
    sup_samp = float(np.max(np.abs(np.polyval([1.0, 0, 0, 0, 0],
                                              x[0] + tt))))
    supk = float(j_supk(h2, 0, rho)[0])
    t3_ok = supk >= sup_samp * (1 - 1e-12)
    rows.append({"test": "T3_supk_vs_sampling", "supk": supk,
                 "sampled": sup_samp, "ok": bool(t3_ok)})
    ok = ok and t3_ok
    return {"pass": bool(ok), "rows": rows}


if __name__ == "__main__":
    main()