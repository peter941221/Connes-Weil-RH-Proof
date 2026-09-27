#!/usr/bin/env python3
# routea_interval_kernel_model_2048.py — record 2048 (probe; verdict rules
# frozen before the run)
#
# RECORD 2041 LINK L2, THIRD ARCHITECTURE: panel-local MODEL (registerd by
# record 2046 section 4 as the next reopen).
#
# Architecture.  Enclose g, not the kernel.  On a uniform panel grid of
# width h, write g = M_h + r with M_h the panelwise linear interpolant
# through the nodal values g(xi_i):
#
#   QW_book = sum_k c_k int g cos(omega_k xi) dxi,  c_k = 2 Lambda(k)/sqrt(k)
#           = sum_k c_k int M_h cos  +  sum_k c_k int r cos .
#
# Model part:  int_panel M_h cos is CLOSED FORM in the two nodal values,
#              int_a^{a+h} M cos = g_a BC + ((g_b - g_a)/h) BL,
#              BC = (sin(om b) - sin(om a))/om,   BL = int_a^b (xi-a) cos,
#              BL = cos(om a) I1 - sin(om a) I2 with t = xi - a,
#              I1 = h sin(om h)/om + (cos(om h) - 1)/om^2,
#              I2 = -h cos(om h)/om + sin(om h)/om^2.
#              Its enclosure width, given nodal enclosures of width dg_i, is
#              <= sum_i dg_i |W_i(k)| with W_i the tent integral at node i
#              (partition of unity: sum_i W_i = int cos over the window);
#              with uniform dg this is dg * Coef1(h), Coef1 = sum_k c_k
#              sum_i |W_i(k)| - measured here.
# Remainder:   |int_panel r cos| <= int_panel |r| <= (h^3/8) sup_panel |g''|
#              (linear-interpolation error bound, midpoint-tight), so the
#              book-side remainder width is the per-panel DOUBLE SUM
#              sum_panels sum_k c_k (h^3/8) sup_panel |g''|
#                = C_book (h^2/8) TV_sup2(h),  C_book = sum_k c_k = 458.05,
#              TV_sup2(h) = sum_panels h sup_panel |g''|   [factorized;
#              the factorization identity is verified in the artifact].
#              This is the CRUDE L1 form (no omega_k oscillation used); at
#              panel scale h omega_max << 1 the crude form is already the
#              min of the two classical bounds, so it is the form to price.
# Archimedean: charged by the committed direct interval method (record 2043
#              pipeline) at dxi = 0.05; sigma is smooth, this term is small.
#
# dxi-INDEPENDENT: the panel endpoints ARE the evaluation points, so the
# charge is a function of h alone (the record-2041 link's finite-difference
# grid decouples from the width budget, as in record 2046).
#
# g, g' are FLOATS from the committed 2037 pipeline on the same one-copy
# G8-H owner as records 2043/2046.  sup_panel |g''| is a float stencil
# estimate: link L3 (enclosed sup) is NOT implemented here; the charge
# below is a budget price with the standard convention (L1: nodal
# enclosures charged as zero, headroom reported; L3: float estimate).
#
# ANCHORS
#   A1  direct-architecture dxi = 0.05 row reproduces record 2043/2046
#       width_mean 569.087 within 2% (shared pipeline + kernels)
#   A2  interval sigma contains the committed float r59.rig.sigma_vec at
#       u in {0, 2 pi, 20 pi, 80 pi}       [as in records 2043/2046]
#   A3  closed-form blocks (BC, BL) vs mpmath high-precision quadrature on
#       sampled (om, a, h) triples: the mpmath side must close to 1e-20
#       relative (and 1e-20 against an independently derived product-rule
#       form, plus the structural ceiling |h sin(om b)/om| <= h/om on its
#       first term); the FLOAT64 echo is gated on its ABSOLUTE floor: BC, BL
#       are differences of O(1) trigonometric evaluations, so the float64
#       absolute error is a few ulps of 1 (~1e-15) independent of h and om,
#       while relative-to-block measures blow up when a block passes through
#       a zero (phase-dependent, measured up to 5e-12 at h = 2.5e-4) - a
#       presentation effect, not an assembly defect.  Interval
#       implementations track radii and do not have this issue.
#       INCIDENT (kept as evidence): the first version of the independent
#       form was transcribed WITHOUT the /om on its first term and read
#       rel_ind up to 47.6 - ANCHOR-FAIL while the checked closed form
#       agreed with quadrature at 2.4e-27.  The coded term (1.97e-3)
#       exceeded its analytic ceiling (h/om = 4.6e-4), which identified the
#       CHECKER as the defect.  Diagnose against structural bounds, never by
#       loosening the gate.
#   A4  tent partition identity sum_i W_i(om) = int_window cos = 2 sin(40 om)/om
#       on sampled k: residual <= 1e-12 * sum_i |W_i|   [closed-form algebra]
#   A5  remainder-bound VALIDITY on the real g: for sampled panels x the
#       full book, measured |int_panel r cos| <= (h^3/8) sup_panel |g''|
#       must hold with ZERO violations, and the intermediate bound
#       |int_panel r cos| <= int_panel |r| must hold panelwise; tightness
#       ratios are recorded (informative)
#   A6  TV_sup2 grid stability: at h in {0.002, 0.001} the value measured on
#       the dxi grid and on 2 dxi must agree to 3%; TV_sup2 must be
#       monotone NON-DECREASING in h (sup over larger panels)
#   A7  cross-read: TV_sup2(0.01) vs the committed record-2046 stencil
#       value 2.5264e22 (relative within 10%, finer sup sampling only
#       increases it)
#
# VERDICT RULES (frozen)
#   MODEL-L2-VIABLE : anchors pass AND min over the h ladder of
#                     (remainder + model float slack + arch) < 1e19
#   MODEL-L2-FAIL   : anchors pass AND min over the ladder > 1.11e20
#   MODEL-L2-GRAY   : otherwise
#   ANCHOR-FAIL     : any anchor misses
#
# Nyquist per AGENTS.md §5: the float assemblies run on the dxi grid
# (--grid, default 2.5e-4, resolves log k <= 2000); the committed book has
# max log k = log(13383) = 9.50.  Panel endpoints are grid nodes; the
# closed forms carry no quadrature error.
#
# CLI: (default) full probe;  --smoke  coarse plumbing check;
#      --grid H  fine-grid spacing;  --a3only  diagnostic fast path (0.3 s
#      vs 285 s): A3 in the FULL run's call order (quadrature first, product
#      form after) with raw values and the ambient dps -- this path is what
#      localized the transcription incident above.

import json
import math
import os
import sys
import time

import numpy as np
import mpmath as mp

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, "scripts"))

import fourpoint_owner_completion_1980 as r80  # noqa: E402
import fourpoint_owner_density_1959 as r59     # noqa: E402
import routea_g8h_basis_comparison_2037 as r37  # noqa: E402
import routea_interval_kernel_2043 as r43      # noqa: E402

mp.iv.dps = 20
# A3 gates at the design's own floor: mp.quad at the default 15 dps carries
# an absolute error ~1e-15 relative to the O(1) integrand, which shows up as
# 1e-11 relative on the O(h^2) block BL - far ABOVE the 1e-12 gate.  At 30
# dps the quadrature-vs-closed-form agreement measured 4e-27, and the
# independent product-rule form agrees to the same order (see A3 rows).
mp.mp.dps = 30
XI_MAX = 40.0
BUDGET = 1e19
HARD = 1.11e20
ANCHOR_DXI = 0.05
ANCHOR_WIDTH_MEAN_2043 = 569.087
ANCHOR_WIDTH_TOL = 0.02
TV2_STENCIL_2046_0p01 = 2.5263722116765306e22
TV2_CROSS_TOL = 0.10
GRID_DXI = 0.00025
GRID_TOL = 0.03
H_LADDER = (0.05, 0.02, 0.01, 0.005, 0.002, 0.001)
COEF1_H = (0.01, 0.005, 0.002)
DG_REFERENCE_REL = 1e-15          # realistic float-ish nodal enclosure


def _san(o):
    if isinstance(o, np.bool_):
        return bool(o)
    if isinstance(o, np.integer):
        return int(o)
    if isinstance(o, np.floating):
        return float(o)
    raise TypeError(str(type(o)))


def trapz(y, x):
    f = getattr(np, "trapezoid", None) or np.trapz
    return float(f(y, x))


def stencils(g, h):
    gp = np.empty_like(g)
    gp[1:-1] = (g[2:] - g[:-2]) / (2 * h)
    gp[0] = (g[1] - g[0]) / h
    gp[-1] = (g[-1] - g[-2]) / h
    gpp = np.empty_like(g)
    gpp[1:-1] = (g[2:] - 2 * g[1:-1] + g[:-2]) / (h * h)
    gpp[0] = gpp[1]
    gpp[-1] = gpp[-2]
    return gp, gpp


def bc_bl(om, a, h):
    """Closed-form (BC, BL) on [a, a+h], vectorized over the array a."""
    b = a + h
    BC = (np.sin(om * b) - np.sin(om * a)) / om
    sh, ch = math.sin(om * h), math.cos(om * h)
    I1 = h * sh / om + (ch - 1.0) / (om * om)
    I2 = -h * ch / om + sh / (om * om)
    BL = np.cos(om * a) * I1 - np.sin(om * a) * I2
    return BC, BL


def bc_bl_mp(om, a, h):
    """mpmath mpf companion of bc_bl (single a)."""
    b = a + h
    BC = (mp.sin(om * b) - mp.sin(om * a)) / om
    sh, ch = mp.sin(om * h), mp.cos(om * h)
    I1 = h * sh / om + (ch - 1) / (om * om)
    I2 = -h * ch / om + sh / (om * om)
    BL = mp.cos(om * a) * I1 - mp.sin(om * a) * I2
    return BC, BL


def tent_sums(om, edges, h):
    """sum_i |W_i(om)| and the W vector on the uniform panel grid."""
    a = edges[:-1]
    BC, BL = bc_bl(om, a, h)
    W = np.empty(len(edges))
    W[0] = BC[0] - BL[0] / h                    # left boundary node
    W[1:-1] = BL[:-1] / h + (BC[1:] - BL[1:] / h)
    W[-1] = BL[-1] / h                          # right boundary node
    return float(np.sum(np.abs(W))), W


def panel_sups(gpp, dxi_g, h):
    """Per-panel sup |g''| on the uniform panel grid of width h."""
    step = int(round(h / dxi_g))
    if step < 1:
        raise ValueError("panel width below the grid spacing")
    ng = len(gpp)
    npan = (ng - 1) // step
    sups = np.empty(npan)
    for i in range(npan):
        j0 = i * step
        j1 = min(j0 + step, ng - 1)
        sups[i] = float(np.max(np.abs(gpp[j0:j1 + 1])))
    return sups


def main():
    iv = mp.iv
    smoke = "--smoke" in sys.argv
    dxi_g = None
    for i, arg in enumerate(sys.argv):
        if arg == "--grid":
            dxi_g = float(sys.argv[i + 1])
    if dxi_g is None:
        dxi_g = 0.0025 if smoke else GRID_DXI
    t0 = time.time()
    rho, nodes, values, fam, xw, gram, a, _, _ = r37.setup(False)
    base, _ = r37.min_h1(gram, a, np.ones(len(nodes), complex))
    corr, _ = r37.min_h1(gram, a, np.asarray(values, complex))
    support = max(a_ for a_, _ in fam) * (r37.N + 2)
    ps = r59.rig.prime_powers_up_to(math.exp(support))
    if smoke:
        ps = ps[:300]
    # uniform panel ladder must divide the window: coarsen if needed
    win = 2 * XI_MAX
    h_list = tuple(h for h in H_LADDER if abs(round(win / h) * h - win) < 1e-9
                   and h >= 4 * dxi_g)
    print("setup %.1fs book %d dxi_g %g h_ladder %s"
          % (time.time() - t0, len(ps), dxi_g, h_list), flush=True)

    c_k = [2 * w / math.sqrt(num) for num, w in ps]
    om_k = [2 * math.pi * math.log(num) for num, _ in ps]
    C_book = float(sum(c_k))
    B2 = float(sum(c / om ** 2 for c, om in zip(c_k, om_k)))

    if "--a3only" in sys.argv:
        # diagnostic fast path: replicate the A3 call ORDER (quad first,
        # product form after) and dump raw values plus the ambient dps
        probes_d = [(om_k[j], -XI_MAX + (j % 17) * 40.0 / 17.0, 0.002)
                    for j in range(0, len(ps), max(1, len(ps) // 9))][:9]
        print("A3ONLY dps mp %s iv %s probes %d"
              % (mp.mp.dps, mp.iv.dps, len(probes_d)), flush=True)
        for om_f, a_f, h_f in probes_d:
            om_m, a_m, h_m = (mp.mpf(repr(om_f)), mp.mpf(repr(a_f)),
                              mp.mpf(repr(h_f)))
            BC_m = mp.quad(lambda t: mp.cos(om_m * t), [a_m, a_m + h_m])
            BL_m = mp.quad(lambda t: (t - a_m) * mp.cos(om_m * t),
                           [a_m, a_m + h_m])
            BC_c, BL_c = bc_bl_mp(om_m, a_m, h_m)
            b_m = a_m + h_m
            BC_i = (mp.sin(om_m * b_m) - mp.sin(om_m * a_m)) / om_m
            BL_i = (h_m * mp.sin(om_m * b_m) / om_m
                    - (mp.cos(om_m * a_m) - mp.cos(om_m * b_m))
                    / om_m ** 2)
            scale = max(mp.mpf(1e-300), abs(BC_m), abs(BL_m))
            rel = max(abs(BC_c - BC_m), abs(BL_c - BL_m)) / scale
            rel_ind = max(abs(BC_c - BC_i), abs(BL_c - BL_i)) / scale
            print(" om %r a %r h %r dps %s/%s"
                  % (om_f, a_f, h_f, mp.mp.dps, mp.iv.dps), flush=True)
            print("   BC_c %s" % mp.nstr(BC_c, 30), flush=True)
            print("   BC_i %s" % mp.nstr(BC_i, 30), flush=True)
            print("   BL_c %s" % mp.nstr(BL_c, 30), flush=True)
            print("   BL_i %s" % mp.nstr(BL_i, 30), flush=True)
            t1 = h_m * mp.sin(om_m * b_m)
            t2 = (mp.cos(om_m * a_m) - mp.cos(om_m * b_m)) / om_m ** 2
            print("   t1 %s" % mp.nstr(t1, 30), flush=True)
            print("   t2 %s" % mp.nstr(t2, 30), flush=True)
            print("   t1-t2 %s" % mp.nstr(t1 - t2, 30), flush=True)
            print("   om**2 %s  om*om %s  b_m %s"
                  % (mp.nstr(om_m ** 2, 30), mp.nstr(om_m * om_m, 30),
                     mp.nstr(b_m, 30)), flush=True)
            print("   rel %.6g rel_ind %.6g" % (float(rel), float(rel_ind)),
                  flush=True)
        return

    # A2: interval sigma containment (the committed float path)
    anch = []
    for u_f in (0.0, 2 * np.pi, 20 * np.pi, 80 * np.pi):
        s_iv = r43.sigma_arch_iv(iv.mpf([repr(u_f), repr(u_f)]))
        s_float = float(r59.rig.sigma_vec(np.array([u_f]))[0])
        anch.append({"u": u_f,
                     "contained": bool(mp.mpf(s_iv.a) <= s_float
                                       <= mp.mpf(s_iv.b))})
    a2_ok = all(r_["contained"] for r_ in anch)

    # A1: direct-architecture 0.05 row (pipeline provenance + arch charge)
    n_pan = int(round(win / ANCHOR_DXI))
    edges_a = np.linspace(-XI_MAX, XI_MAX, n_pan + 1)
    ker_a, g_a = r43.float_kernel_and_g(edges_a, fam, xw, base, corr, rho, ps)
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
    arch_proj = float(np.sum(w_arch * g_mid_a * ANCHOR_DXI))
    a1_ok = abs(width_mean - ANCHOR_WIDTH_MEAN_2043) \
        <= ANCHOR_WIDTH_TOL * ANCHOR_WIDTH_MEAN_2043
    if smoke:
        a1_ok = True
    print("A1 width_mean %.4f (ref %.3f) arch_proj %.4g %.1fs"
          % (width_mean, ANCHOR_WIDTH_MEAN_2043, arch_proj,
             time.time() - t0), flush=True)

    # fine grid: g and the g'' stencil
    n_g = int(round(win / dxi_g))
    edges = np.linspace(-XI_MAX, XI_MAX, n_g + 1)
    _ker, g_only = r43.float_kernel_and_g(edges, fam, xw, base, corr, rho, ps)
    gp, gpp = stencils(g_only, dxi_g)
    int_g = trapz(g_only, edges)
    g_max = float(np.max(np.abs(g_only)))
    print("fine grid %d pts  int_g %.6g  gmax %.6g  %.1fs"
          % (n_g + 1, int_g, g_max, time.time() - t0), flush=True)

    # A3: closed-form blocks vs mpmath quadrature
    a3_rows = []
    a3_ok = True
    probes = [(om_k[j], -XI_MAX + (j % 17) * 40.0 / 17.0,
               GRID_DXI if smoke else 0.002)
              for j in range(0, len(ps), max(1, len(ps) // 9))][:9]
    for om_f, a_f, h_f in probes:
        om_m, a_m, h_m = mp.mpf(repr(om_f)), mp.mpf(repr(a_f)), mp.mpf(repr(h_f))
        BC_m = mp.quad(lambda t: mp.cos(om_m * t), [a_m, a_m + h_m])
        BL_m = mp.quad(lambda t: (t - a_m) * mp.cos(om_m * t),
                       [a_m, a_m + h_m])
        BC_c, BL_c = bc_bl_mp(om_m, a_m, h_m)
        # independently derived form (product rule, no small-angle rewrite):
        #   int cos = [sin]/om
        #   int (t-a) cos = h sin(om b)/om - (cos(om a) - cos(om b))/om^2
        b_m = a_m + h_m
        BC_i = (mp.sin(om_m * b_m) - mp.sin(om_m * a_m)) / om_m
        BL_i = (h_m * mp.sin(om_m * b_m) / om_m
                - (mp.cos(om_m * a_m) - mp.cos(om_m * b_m)) / om_m ** 2)
        # structural ceiling: |h sin(om b)/om| <= h/om.  This caught the
        # transcription bug in the first version of BL_i (a missing /om);
        # a tolerance alone would have blamed the checked closed form.
        t1_ceiling = abs(h_m * mp.sin(om_m * b_m) / om_m) <= \
            h_m / om_m * (1 + mp.mpf('1e-25'))
        scale = max(mp.mpf(1e-300), abs(BC_m), abs(BL_m))
        rel = max(abs(BC_c - BC_m), abs(BL_c - BL_m)) / scale
        rel_ind = max(abs(BC_c - BC_i), abs(BL_c - BL_i)) / scale
        a3_rows.append({"om": om_f, "a": a_f, "h": h_f, "rel": float(rel),
                        "rel_independent": float(rel_ind),
                        "t1_ceiling": bool(t1_ceiling)})
        a3_ok = a3_ok and rel < 1e-20 and rel_ind < 1e-20 and t1_ceiling
    # float64 echo on the same triples (the assembly the rig actually uses)
    a3f = 0.0        # relative to max(|BC|, |BL|) - presentation, see header
    a3f_abs = 0.0    # absolute - the gated quantity
    for om_f, a_f, h_f in probes:
        BC_c, BL_c = bc_bl(om_f, np.array([a_f]), h_f)
        BC_m, BL_m = bc_bl_mp(mp.mpf(repr(om_f)), mp.mpf(repr(a_f)),
                              mp.mpf(repr(h_f)))
        scale = max(1e-300, float(abs(BC_m)), float(abs(BL_m)))
        err = max(float(abs(BC_c[0] - BC_m)), float(abs(BL_c[0] - BL_m)))
        a3f_abs = max(a3f_abs, err)
        a3f = max(a3f, err / scale)
    a3f_ok = a3f_abs < 1e-13
    if smoke:
        a3_ok = a3f_ok = True
    a3_ok = a3_ok and a3f_ok
    print("A3 closed-form mp %.3g float abs %.3g rel %.3g"
          % (max(r_["rel"] for r_ in a3_rows), a3f_abs, a3f), flush=True)

    # per-h rows: TV_sup2, factorization, divisor identity, charge
    rows = []
    sups_by_h = {}
    for h in h_list:
        sups = panel_sups(gpp, dxi_g, h)
        tv = float(np.sum(sups) * h)
        charge = C_book * float(np.sum(sups)) * (h ** 3 / 8.0)
        fact = C_book * (h ** 2 / 8.0) * tv
        rows.append({"h": h, "panels": len(sups), "TV_sup2": tv,
                     "charge_remainder": charge,
                     "factorization_rel": abs(charge - fact) / max(1e-300, charge),
                     "over_budget": charge / BUDGET})
        sups_by_h[h] = sups
        print("h %-6g panels %-7d TV_sup2 %.6g charge %.6g %.3fx budget"
              % (h, len(sups), tv, charge, charge / BUDGET), flush=True)

    # A6: TV_sup2 grid stability at the two finest rungs (2 dxi nodes)
    a6_rows = []
    a6_ok = True
    if not smoke:
        for h in (0.002, 0.001):
            if h not in sups_by_h or dxi_g * 2 > h / 2:
                continue
            gpp2 = gpp[::2]
            sups2 = panel_sups(gpp2, 2 * dxi_g, h)
            tv2 = float(np.sum(sups2) * h)
            rel = abs(tv2 - sups_by_h[h].sum() * h) \
                / max(1e-300, sups_by_h[h].sum() * h)
            a6_rows.append({"h": h, "TV_sup2_coarse_grid": tv2, "rel": rel})
            a6_ok = a6_ok and rel <= GRID_TOL
    # TV_sup2 = sum_panels h sup_panel |g''| is non-decreasing in h: a double
    # panel contributes 2h max(a, b) >= h a + h b.  The ladder runs in
    # DECREASING h, so the row values must be non-increasing along the list.
    mono = all(rows[i]["TV_sup2"] >= rows[i + 1]["TV_sup2"]
               for i in range(len(rows) - 1))
    a6_ok = a6_ok and mono
    # A7: cross-read against the committed 2046 stencil TV2 at 0.01
    a7_rel = abs(rows[[r_["h"] for r_ in rows].index(0.01)]["TV_sup2"]
                 - TV2_STENCIL_2046_0p01) / TV2_STENCIL_2046_0p01
    a7_ok = a7_rel <= TV2_CROSS_TOL
    print("A6 grid-stability %s mono %s | A7 rel %.4g"
          % (a6_rows, mono, a7_rel), flush=True)

    # A4: tent partition identity on sampled k
    a4_ok = True
    a4_worst = 0.0
    h_probe = 0.002 if 0.002 in h_list else h_list[-1]
    edges_p = np.linspace(-XI_MAX, XI_MAX, int(round(win / h_probe)) + 1)
    for j in range(0, len(ps), max(1, len(ps) // 9)):
        om = om_k[j]
        s_abs, W = tent_sums(om, edges_p, h_probe)
        exact = 2 * math.sin(XI_MAX * om) / om
        res = abs(float(np.sum(W)) - exact)
        a4_worst = max(a4_worst, res / max(1e-300, s_abs))
        a4_ok = a4_ok and res <= 1e-12 * max(1e-300, s_abs)
    if smoke:
        a4_ok = True
    print("A4 tent partition worst rel %.3g" % a4_worst, flush=True)

    # Coef1(h): nodal-enclosure coefficient (the L1 requirement)
    coef1_rows = []
    for h in COEF1_H:
        if h not in h_list:
            continue
        edges_p = np.linspace(-XI_MAX, XI_MAX, int(round(win / h)) + 1)
        tot = 0.0
        for om, c in zip(om_k, c_k):
            s_abs, _W = tent_sums(om, edges_p, h)
            tot += c * s_abs
        coef1_rows.append({"h": h, "Coef1": tot,
                           "dg_headroom": (BUDGET - next(
                               r_["charge_remainder"] for r_ in rows
                               if r_["h"] == h)) / tot})
        print("Coef1 h %-6g %.6g  dg* %.4g"
              % (h, tot, coef1_rows[-1]["dg_headroom"]), flush=True)

    # A5: remainder-bound validity on the real g (sampled panels x full book)
    a5_ok = True
    h_v = 0.002 if 0.002 in h_list else h_list[-1]
    step = int(round(h_v / dxi_g))
    npan_v = (len(g_only) - 1) // step
    sample = list(range(0, npan_v, max(1, npan_v // 48)))[:48]
    worst_k = 0.0
    worst_abs = 0.0
    violations = 0
    agg_rows = []
    for i in sample:
        j0 = i * step
        j1 = min(j0 + step, len(g_only) - 1)
        xs = edges[j0:j1 + 1]
        gs = g_only[j0:j1 + 1]
        local = np.arange(len(xs)) / (len(xs) - 1)
        rr = gs - (gs[0] + (gs[-1] - gs[0]) * local)
        int_abs_r = trapz(np.abs(rr), xs)
        sup = float(np.max(np.abs(gpp[j0:j1 + 1])))
        bound = (h_v ** 3 / 8.0) * sup
        agg = 0.0
        for om, c in zip(om_k, c_k):
            m = abs(trapz(rr * np.cos(om * xs), xs))
            worst_k = max(worst_k, m / max(1e-300, bound))
            if m > bound * (1 + 1e-9):
                violations += 1
            worst_abs = max(worst_abs, m / max(1e-300, int_abs_r))
            agg += c * m
        agg_rows.append({"panel": i, "agg_measured": agg,
                         "agg_crude_bound": C_book * bound,
                         "agg_loss": C_book * bound / max(1e-300, agg)})
    if smoke:
        a5_ok = True
    else:
        a5_ok = (violations == 0) and worst_abs <= 1 + 1e-6
    agg_loss_med = float(np.median([r_["agg_loss"] for r_ in agg_rows])) \
        if agg_rows else None
    print("A5 violations %d  worst |int r cos|/bound %.4g  "
          "worst/int|r| %.4g  agg-loss median %.4g"
          % (violations, worst_k, worst_abs, agg_loss_med or 0.0), flush=True)

    # model-part float slack: closed form assembled in float over the whole
    # window vs mpmath on sampled panels (per-k, magnitude-budgeted)
    h_s = 0.002 if 0.002 in h_list else h_list[-1]
    edges_s = np.linspace(-XI_MAX, XI_MAX, int(round(win / h_s)) + 1)
    npan_s = len(edges_s) - 1
    g_s = np.interp(edges_s, edges, g_only)
    slack = 0.0
    for j in range(0, len(ps), max(1, len(ps) // 12)):
        om = om_k[j]
        BC, BL = bc_bl(om, edges_s[:-1], h_s)
        dg = np.diff(g_s)
        model_f = float(np.sum(g_s[:-1] * BC + (dg / h_s) * BL))
        pan_sel = list(range(0, npan_s, max(1, npan_s // 200)))[:200]
        err = 0.0
        for i in pan_sel:
            ga_m, gb_m = mp.mpf(repr(float(g_s[i]))), mp.mpf(repr(float(g_s[i + 1])))
            BC_m, BL_m = bc_bl_mp(mp.mpf(repr(om)), mp.mpf(repr(float(edges_s[i]))),
                                  mp.mpf(repr(h_s)))
            v_m = ga_m * BC_m + ((gb_m - ga_m) / mp.mpf(repr(h_s))) * BL_m
            BC_f, BL_f = bc_bl(om, np.array([edges_s[i]]), h_s)
            v_f = g_s[i] * BC_f[0] + (dg[i] / h_s) * BL_f[0]
            err = max(err, abs(float(v_f - v_m)) / max(1e-300, float(abs(v_m))))
        slack += c_k[j] * (npan_s * err) * max(1e-300, abs(model_f) / npan_s)
    slack *= C_book / max(1e-300, sum(c_k[j] for j in
                                      range(0, len(ps), max(1, len(ps) // 12))))
    print("model float slack %.4g" % slack, flush=True)

    # verdict ladder
    best = min(r_["charge_remainder"] for r_ in rows) + slack + arch_proj
    anchors_pass = (a1_ok and a2_ok and a3_ok and a4_ok and a5_ok
                    and a6_ok and a7_ok)
    if not anchors_pass:
        verdict = "ANCHOR-FAIL"
    elif best < BUDGET:
        verdict = "MODEL-L2-VIABLE"
    elif best > HARD:
        verdict = "MODEL-L2-FAIL"
    else:
        verdict = "MODEL-L2-GRAY"
    out = {
        "record": 2048, "status": verdict, "owner": "one-copy G8-H",
        "rho": [float(rho.real), float(rho.imag)], "scale": r37.SCALE,
        "support": support, "book_size": len(ps),
        "constants": {"C_book": C_book, "B2": B2,
                      "budget": BUDGET, "arch_proj_at_0.05": arch_proj},
        "anchors": {
            "A1_direct_0.05": {"width_mean": width_mean,
                               "reference_2043": ANCHOR_WIDTH_MEAN_2043,
                               "pass": a1_ok},
            "A2_sigma_containment": {"rows": anch, "pass": a2_ok},
            "A3_closed_form_blocks": {"mp_rows": a3_rows, "mp_pass": a3_ok,
                                      "float_rel_max": a3f,
                                      "float_abs_max": a3f_abs,
                                      "float_gate": 1e-13,
                                      "float_pass": a3f_ok},
            "A4_tent_partition": {"worst_rel": a4_worst, "pass": a4_ok},
            "A5_remainder_validity": {
                "sampled_panels": len(sample), "violations": violations,
                "worst_measured_over_bound": worst_k,
                "worst_measured_over_int_abs_r": worst_abs,
                "aggregate_loss_median": agg_loss_med, "pass": a5_ok},
            "A6_grid_stability": {"rows": a6_rows, "monotone_in_h": mono,
                                  "pass": a6_ok},
            "A7_cross_read_2046": {"rel": a7_rel,
                                   "reference": TV2_STENCIL_2046_0p01,
                                   "pass": a7_ok}},
        "h_rows": rows,
        "coef1_rows": coef1_rows,
        "model_float_slack": slack,
        "best_total": best,
        "dg_reference": {"rel_assumed": DG_REFERENCE_REL,
                         "abs": DG_REFERENCE_REL * g_max,
                         "charge_at_h_0.002": (
                             DG_REFERENCE_REL * g_max
                             * next((r_["Coef1"] for r_ in coef1_rows
                                     if r_["h"] == 0.002), 0.0))},
        "fine_grid": {"dxi": dxi_g, "points": n_g + 1, "int_g": int_g,
                      "gmax": g_max},
        "nonclaims": [
            "float g, g' from the committed 2037 pipeline; sup|g''| is a "
            "float stencil estimate - link L3 (enclosed sup) NOT implemented",
            "nodal enclosures (L1) charged as zero; the coefficient Coef1 and "
            "the headroom dg* are reported instead",
            "the archimedean term uses the committed direct interval method "
            "at dxi = 0.05 only (smooth; small)",
            "no full-line tail (L4 separate)", "no coefficient enclosure",
            "not a producer theorem", "not RH",
        ],
    }
    path = os.path.join(ROOT, "results", "2048_interval_kernel_model.json")
    with open(path, "w", encoding="utf-8", newline="\n") as f:
        json.dump(out, f, indent=2, default=_san)
        f.write("\n")
    print("VERDICT", verdict)
    print("best h %.6g charge %.6g slack %.4g arch %.4g total %.6g (%.3fx)"
          % (min(rows, key=lambda r_: r_["charge_remainder"])["h"],
             min(r_["charge_remainder"] for r_ in rows), slack, arch_proj,
             best, best / BUDGET))
    print("RESULT", path)
    print("elapsed", round(time.time() - t0, 1), flush=True)


if __name__ == "__main__":
    main()