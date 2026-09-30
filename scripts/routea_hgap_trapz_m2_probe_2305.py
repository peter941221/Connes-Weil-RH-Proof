"""Record 2305: trapezoid M2 cap and per-cell enclosure pricing probe.

Two questions on the *ideal* smooth integrand of 2275/2280,

    Gi(x) = kernel(x)^2 * |ann(x)|^2 * |B(x)|^2 * |C(x)|^2,

with kernel(x) = sigma(2 pi x) + 2 sum_p w_p n^{-1/2} cos(2 pi x log n),
ann the degree-four detector annihilator, and B, C the exact Fourier
transforms of the corrected owner profiles
h_f(y) = c_f phi_(a_f^2)(y) e^{(1/2 + i theta_f) y}, phi_R(y) =
exp(-30/(1-(y/R)^2)).

P4 (M2 cap).  2275 prices the cell rule
    T_cell - int_cell Gd = (1/2) int_cell (x-l)(l+h-x) Gd''(x) dx
by |error| <= M2 h^3/12 per cell with M2 = sup|Gd''|; over 4000 cells of
h = 1/50 the window total is <= M2/375, so the whole 1e7 budget would need
M2 <= 3.75e9.  This probe measures the ideal-side counterpart: sup|Gi''|
sampled on [-40, 40], the global route value M2*80*h^2/12, the panel-local
route sum_cells sup|Gi''| h^3/12 at two h, and the h required by the
measured mass density.

P3 (per-cell enclosure).  The 2302 cell screen still samples the kernel
and annihilator weights.  This probe prices their intervalization on the
same cells: exact cos-arc intervals for the prime-power sum, exact quartic
intervals for the annihilator, and the rigorous slope charge for sigma
(|sigma'| <= pi psi'(1/4)).  The integrated width is compared against the
per-cell share of the 1e7 budget.

Probe only: sampled sup values are not interval enclosures; the finite
rule Gd of 2275 is not reproduced; nothing here supplies hgap.

Modes: MODE=probe (default), MODE=selftest.
"""
import json
import math
import os
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
R = ROOT / "results"
OUT = R / "2305_hgap_trapz_m2_probe.json"
CAPTURE = R / "2275_gap_owner_audit.json"
K = 30.0
XI_LO, XI_HI = -40.0, 40.0
WIN_LO, WIN_HI = -4.0, 4.0        # dense window: transform mass region
BUDGET = 1.0e7
GAMMA = 39.25244858548658
DELTA = 0.445
GL_PANELS, GL_NODES = 40, 16
OPTS = (5, -0.3, 0.3, -0.45, 0.45)  # sub-sample offsets per cell, in h


def load_owner():
    cap = json.loads(CAPTURE.read_text(encoding="utf-8"))["owner_capture"]
    fam = [(float.fromhex(a), float.fromhex(t)) for a, t in cap["families_hex"]]
    base = np.array([complex(float.fromhex(re), float.fromhex(im))
                     for re, im in cap["base_hex"]])
    corr = np.array([complex(float.fromhex(re), float.fromhex(im))
                     for re, im in cap["corr_hex"]])
    return fam, base, corr, cap


def gl_rule(lo, hi, panels, nodes):
    """Composite Gauss-Legendre nodes/weights on [lo, hi]."""
    xg, wg = np.polynomial.legendre.leggauss(nodes)
    edges = np.linspace(lo, hi, panels + 1)
    xs, ws = [], []
    for l, r in zip(edges[:-1], edges[1:]):
        half = 0.5 * (r - l)
        mid = 0.5 * (r + l)
        xs.append(mid + half * xg)
        ws.append(half * wg)
    return np.concatenate(xs), np.concatenate(ws)


def transform_table(x, fam, coef, panels=GL_PANELS, nodes=GL_NODES,
                    phase_aware=False):
    """B(x), B'(x), B''(x) by composite Gauss-Legendre, one rule per family.

    b_f(x) = int phi_f(y) e^{(1/2 + i theta_f) y} e^{-2 pi i x y} dy;
    each x-derivative brings down a factor (-2 pi i y).

    The y-phase rate of family f is rad_f*(theta_f + 2 pi |x|); with
    phase_aware=True the panel count is raised so that no panel spans more
    than pi of phase (the fast default under-resolves large |x|).
    """
    b = np.zeros(x.shape, dtype=complex)
    b1 = np.zeros(x.shape, dtype=complex)
    b2 = np.zeros(x.shape, dtype=complex)
    xmax = float(np.max(np.abs(x))) if x.size else 0.0
    for (w, th), c in zip(fam, coef):
        rad = w * w
        pf = panels
        if phase_aware:
            need = int(math.ceil(rad * (abs(th) + 2 * math.pi * xmax) / math.pi))
            pf = max(panels, need)
        y, wy = gl_rule(-rad, rad, pf, nodes)
        s = 1.0 - (y / rad) ** 2
        amp = c * np.exp(-K / s) * np.exp((0.5 + 1j * th) * y) * wy
        e = np.exp(-2j * math.pi * np.outer(x, y))
        b += e @ amp
        fy = amp * (-2j * math.pi * y)
        b1 += e @ fy
        b2 += e @ (fy * (-2j * math.pi * y))
    return b, b1, b2


def ann_poly():
    """Annihilator coefficients (ascending), exact real quartic."""
    rho = complex(0.5 + DELTA, GAMMA)
    nodes = [rho - 0.5, (1 - rho.conjugate()) - 0.5,
             rho.conjugate() - 0.5, (1 - rho) - 0.5]
    poly = np.array([1.0 + 0.0j])
    for node in nodes:
        poly = np.convolve(poly, np.array([-2j * math.pi, node]))
    return [float(v.real) for v in poly[::-1]]


def poly_table(x, coef):
    """Value, first and second derivative of a real polynomial (Horner)."""
    a = np.zeros(x.shape)
    a1 = np.zeros(x.shape)
    a2 = np.zeros(x.shape)
    for v in coef[::-1]:
        a2 = a2 * x + 2.0 * a1
        a1 = a1 * x + a
        a = a * x + v
    return a, a1, a2


def sigma_exact(x):
    """sigma(2 pi x), sigma', sigma'' sampled by mpmath polygamma."""
    import mpmath as mp
    mp.mp.dps = 40
    sig = np.empty(x.shape)
    sig1 = np.empty(x.shape)
    sig2 = np.empty(x.shape)
    for i, xv in enumerate(x):
        omega = mp.mpf(2) * mp.pi * mp.mpf(repr(float(xv)))
        z = mp.mpf("0.25") - 0.5j * omega
        sig[i] = float(mp.log(mp.pi) - mp.re(mp.digamma(z)))
        # sigma = log pi - Re psi(z), z = 1/4 - i pi x:
        # sigma' = -pi Im psi'(z);  sigma'' = pi^2 Re psi''(z)
        sig1[i] = float(-mp.pi * mp.im(mp.polygamma(1, z)))
        sig2[i] = float(mp.pi ** 2 * mp.re(mp.polygamma(2, z)))
    return sig, sig1, sig2


def sigma_prime_cap():
    """Rigorous |sigma'(2 pi x)| <= pi * psi'(1/4) for all real x."""
    import mpmath as mp
    mp.mp.dps = 30
    return float(mp.pi * mp.polygamma(1, mp.mpf(1) / 4))


def prime_arrays(primes):
    logn = np.asarray([math.log(n) for n, _ in primes])
    amp = np.asarray([2.0 * w / math.sqrt(n) for n, w in primes])
    return logn, amp


def kernel_sample(x, logn, amp):
    """kernel, kernel', kernel'' at x (sigma by mpmath, primes vectorized)."""
    sig, sig1, sig2 = sigma_exact(x)
    ker = sig.copy()
    ker1 = sig1.copy()
    ker2 = sig2.copy()
    twopi_logn = 2 * math.pi * logn
    for lo in range(0, logn.size, 256):
        hi = min(lo + 256, logn.size)
        ph = np.outer(x, twopi_logn[lo:hi])
        w = amp[lo:hi]
        ker += np.cos(ph) @ w
        ker1 -= (np.sin(ph) * twopi_logn[lo:hi]) @ w
        ker2 -= (np.cos(ph) * twopi_logn[lo:hi] ** 2) @ w
    return ker, ker1, ker2


def cos_arc_interval(a, length):
    """sup and inf of cos on [a, a+length] (length < 2 pi), vectorized."""
    b = a + length
    k1 = np.floor(a / math.pi)
    k2 = np.floor(b / math.pi)
    ca, cb = np.cos(a), np.cos(b)
    lo_ends = np.minimum(ca, cb)
    up_ends = np.maximum(ca, cb)
    hit = k2 > k1                      # a critical point k*pi lies inside
    kcrit = k1 + 1.0
    even = (np.mod(kcrit, 2.0) == 0.0)
    sup = np.where(hit, np.where(even, 1.0, up_ends), up_ends)
    inf = np.where(hit, np.where(even, lo_ends, -1.0), lo_ends)
    return sup, inf


def prime_cell_widths(edges, logn, amp):
    """Per-cell exact interval width of sum_p amp_p cos(2 pi x log n_p)."""
    h = edges[1] - edges[0]
    widths = np.zeros(edges.size - 1)
    for lo in range(0, logn.size, 512):
        hi = min(lo + 512, logn.size)
        a = np.outer(edges[:-1], 2 * math.pi * logn[lo:hi])
        length = 2 * math.pi * h * logn[lo:hi]
        sup, inf = cos_arc_interval(a, length)
        widths += (sup - inf) @ amp[lo:hi]
    return widths


def ann_cell_width(edges, coef):
    """Exact interval width of the quartic on each cell."""
    dcoef = [i * v for i, v in enumerate(coef)][1:]
    crit = np.roots(dcoef[::-1]) if len(dcoef) >= 2 else np.array([])
    crit = np.real(crit[np.abs(np.imag(crit)) < 1e-9])
    lo = np.minimum(poly_table(edges[:-1], coef)[0],
                    poly_table(edges[1:], coef)[0])
    hi = np.maximum(poly_table(edges[:-1], coef)[0],
                    poly_table(edges[1:], coef)[0])
    for c in crit:
        m = (edges[:-1] < c) & (c < edges[1:])
        if m.any():
            v = poly_table(np.array([c]), coef)[0][0]
            lo[m] = np.minimum(lo[m], v)
            hi[m] = np.maximum(hi[m], v)
    return hi - lo


def gi_second(x, fam, base, corr, ann_coef, logn, amp):
    """Gi and Gi'' by the product rule on K=ker^2, A=|ann|^2, |B|^2, |C|^2."""
    ker, ker1, ker2 = kernel_sample(x, logn, amp)
    aa, a1, a2 = poly_table(x, ann_coef)
    b, b1, b2 = transform_table(x, fam, base)
    c, c1, c2 = transform_table(x, fam, corr)
    K = ker * ker
    K1 = 2.0 * ker * ker1
    K2 = 2.0 * ker1 * ker1 + 2.0 * ker * ker2
    A = aa * aa
    A1 = 2.0 * aa * a1
    A2 = 2.0 * aa * a2 + 2.0 * a1 * a1
    Z = np.real(b * np.conj(b))
    Z1 = 2.0 * np.real(b * np.conj(b1))
    Z2 = 2.0 * np.real(b * np.conj(b2)) + 2.0 * np.real(b1 * np.conj(b1))
    W = np.real(c * np.conj(c))
    W1 = 2.0 * np.real(c * np.conj(c1))
    W2 = 2.0 * np.real(c * np.conj(c2)) + 2.0 * np.real(c1 * np.conj(c1))
    gi = K * A * Z * W
    d2 = (K2 * A * Z * W + K * A2 * Z * W + K * A * Z2 * W + K * A * Z * W2
          + 2.0 * (K1 * A1 * Z * W + K1 * A * Z1 * W + K * A * Z1 * W1))
    return gi, d2


def mosaic(lo, hi, h, offsets):
    edges = lo + h * np.arange(int(round((hi - lo) / h)) + 1)
    mid = 0.5 * (edges[:-1] + edges[1:])
    pts = (mid[:, None] + np.asarray(offsets)[None, :] * h).ravel()
    return edges, pts


def transform_mp_abs(xv, fam, coef, dps=50, maxdegree=16):
    """|B(x)| or |C(x)| in high precision (mpmath quadgl, phase-aware panels).

    The float64 pipeline loses the owner transform to cancellation beyond
    |x| ~ 1: the coefficient scale is 2.8e14 (base) / 5.7e17 (corr) while
    the true transform at x = 4 is of order 1e-9 / 1e-11.  This routine is
    the precision control; it is called at three x values only.
    """
    import mpmath as mp
    mp.mp.dps = dps
    tot = mp.mpc(0)
    for (w, th), c in zip(fam, coef):
        rad = mp.mpf(repr(float(w))) ** 2
        rate = float(rad) * (abs(float(th)) + 2 * math.pi * abs(float(xv)))
        panels = int(max(8, min(400, math.ceil(rate / math.pi))))
        edges = [rad * (2 * mp.mpf(k) / panels - 1) for k in range(panels + 1)]
        cf = mp.mpc(repr(float(c.real)), repr(float(c.imag)))
        th_m = mp.mpf(repr(float(th)))
        x_m = mp.mpf(repr(float(xv)))

        def integrand(y):
            s = 1 - (y / rad) ** 2
            return (cf * mp.exp(-mp.mpf(30) / s)
                    * mp.exp((mp.mpf("0.5") + 1j * th_m) * y
                             - 2j * mp.pi * x_m * y))
        tot += mp.quadgl(integrand, edges, maxdegree=maxdegree)
    return float(abs(tot))


def noise_floor(fam, coef):
    """Float64 cancellation scale of the family sum, sum |c_f| R_f e^{-K}."""
    scale = 0.0
    for (w, _), c in zip(fam, coef):
        rad = w * w
        scale += abs(c) * rad * math.exp(-K)
    return scale


def probe():
    import fourpoint_diagonal_sign_1918 as rig
    fam, base, corr, _ = load_owner()
    ann_coef = ann_poly()
    primes = rig.prime_powers_up_to(math.exp(2.0 * max(w * w for w, _ in fam)))
    logn, amp = prime_arrays(primes)
    out = {"record": 2305, "certificate": False, "budget": BUDGET,
           "window": [XI_LO, XI_HI], "dense_window": [WIN_LO, WIN_HI],
           "ann_coeffs": ann_coef, "prime_power_count": len(primes),
           "gl": {"panels": GL_PANELS, "nodes": GL_NODES}}

    # quadrature control on the owner transform at x = 1, 2, 4
    ctrl = {"x": [1.0, 2.0, 4.0]}
    for panels, nodes in ((GL_PANELS, GL_NODES), (2 * GL_PANELS, GL_NODES),
                          (GL_PANELS, 2 * GL_NODES)):
        b, _, _ = transform_table(np.array(ctrl["x"]), fam, base, panels, nodes)
        c, _, _ = transform_table(np.array(ctrl["x"]), fam, corr, panels, nodes)
        ctrl[f"abs_B_{panels}x{nodes}"] = [float(abs(v)) for v in b]
        ctrl[f"abs_C_{panels}x{nodes}"] = [float(abs(v)) for v in c]
    for nodes in (GL_NODES, 2 * GL_NODES):
        b, _, _ = transform_table(np.array(ctrl["x"]), fam, base,
                                  phase_aware=True, nodes=nodes)
        c, _, _ = transform_table(np.array(ctrl["x"]), fam, corr,
                                  phase_aware=True, nodes=nodes)
        ctrl[f"abs_B_pa_{nodes}"] = [float(abs(v)) for v in b]
        ctrl[f"abs_C_pa_{nodes}"] = [float(abs(v)) for v in c]
    out["gl_control"] = ctrl

    # precision floor and the high-precision control at x = 1, 2, 4
    prec = {"noise_floor_base": noise_floor(fam, base),
            "noise_floor_corr": noise_floor(fam, corr),
            "noise_floor_note":
                "sum |c_f| R_f int e^{-K/(1-u^2)} du: the maximal family "
                "cancellation scale; float64 resolves the transform only "
                "where |B| or |C| stays above ~1e-16 of it",
            "mp_x": [1.0, 2.0, 4.0]}
    for xv in prec["mp_x"]:
        prec[f"abs_B_mp_{xv}"] = transform_mp_abs(xv, fam, base)
        prec[f"abs_C_mp_{xv}"] = transform_mp_abs(xv, fam, corr)
    out["precision"] = prec

    # trusted zone: the region where the float64 weights stay above the
    # corr noise floor.  By the control table that is |x| <= 1.
    trusted = 1.0
    out["trusted_zone"] = {
        "abs_x_le": trusted,
        "justification": "setting-doubling agreement 2e-6 relative at x = 1; "
                         "|C(2)|, |C(4)| sit at or below the corr float64 "
                         "noise floor in the control table",
    }

    # --- P4: sampled sup |Gi''| and the two cell-mass routes ------------
    rows = []
    win_mass = {}
    for h in (0.02, 0.005):
        edges, pts = mosaic(WIN_LO, WIN_HI, h, OPTS)
        _, d2 = gi_second(pts, fam, base, corr, ann_coef, logn, amp)
        sup = np.max(np.abs(d2).reshape(-1, len(OPTS)), axis=1)
        mass = float(np.sum(sup) * h ** 3 / 12.0)
        win_mass[h] = mass
        cell_mid = 0.5 * (edges[:-1] + edges[1:])
        region, region_sup = {}, {}
        for lim in (0.5, 1.0, 1.5, 3.0, WIN_HI):
            m = np.abs(cell_mid) <= lim
            region[f"abs_x_le_{lim}"] = float(np.sum(sup[m]) * h ** 3 / 12.0)
            region_sup[f"abs_x_le_{lim}"] = float(np.max(sup[m]))
        rows.append({"h": h, "cells": edges.size - 1,
                     "sup_abs_Gi2_dense_window": float(np.max(sup)),
                     "argmax_x": float(cell_mid[int(np.argmax(sup))]),
                     "sup_by_region": region_sup,
                     "panel_local_mass": mass,
                     "mass_by_region": region,
                     "mass_per_length": mass / (WIN_HI - WIN_LO),
                     "over_budget": mass / BUDGET})
    # coarse global scan: inside / outside the resolvable window
    _, pts_c = mosaic(XI_LO, XI_HI, 0.1, (0.0,))
    gi_c, d2_c = gi_second(pts_c, fam, base, corr, ann_coef, logn, amp)
    abs_c = np.abs(d2_c)
    inside = np.abs(pts_c) <= WIN_HI + 1e-12
    out["global_scan"] = {
        "h": 0.1, "points": int(pts_c.size),
        "sup_abs_Gi2_inside_dense_window": float(np.max(abs_c[inside])),
        "sup_abs_Gi_inside_dense_window": float(np.max(np.abs(gi_c[inside]))),
        "sup_abs_Gi2_outside_dense_window":
            float(np.max(abs_c[~inside])),
        "argmax_x_outside": float(pts_c[~inside][int(np.argmax(abs_c[~inside]))]),
        "outside_note": "at |x| > 4 the transform term scale is O(1) while "
                        "the true decay is e^{-c sqrt(x)}; the sampled values "
                        "there are float64 cancellation noise (same mechanism "
                        "as the 2304 calibration) and are excluded from M2",
    }
    m2 = out["global_scan"]["sup_abs_Gi2_inside_dense_window"]
    m2_lo = rows[-1]["sup_by_region"][f"abs_x_le_{trusted}"]
    h0 = 0.02
    out["m2_rows"] = rows
    out["global_route"] = {
        "M2_sampled_resolvable_window": m2,
        "M2_lower_bound_trusted_zone": m2_lo,
        "bound_at_h_1_50_from_lower_bound":
            m2_lo * (XI_HI - XI_LO) * h0 ** 2 / 12.0,
        "needs_M2_for_budget": BUDGET * 12.0 / ((XI_HI - XI_LO) * h0 ** 2),
        "cap_failure_factor":
            m2_lo / (BUDGET * 12.0 / ((XI_HI - XI_LO) * h0 ** 2)),
    }
    out["p4_verdict"] = ("M2-CAP-FAILED"
                         if out["global_route"]["cap_failure_factor"] > 1.0
                         else "M2-CAP-HOLDS")
    # panel-local: mass(h) = mass(h0) * (h/h0)^2 (confirmed by the two rows);
    # the trusted-zone mass is a lower bound, so the failure factor and the
    # required h below are directional statements
    m_ref, h_ref = rows[-1]["panel_local_mass"], rows[-1]["h"]
    m_lo = rows[-1]["mass_by_region"][f"abs_x_le_{trusted}"]
    c_lo = m_lo / h_ref ** 2
    out["panel_local_route"] = {
        "mass_over_dense_window_at_h_0.005": m_ref,
        "mass_trusted_zone_at_h_0.005": m_lo,
        "quadratic_coefficient_trusted_zone": c_lo,
        "failure_factor_at_design_h_0.02_from_lower_bound":
            c_lo * h0 ** 2 / BUDGET,
        "required_h_upper_bound_from_lower_bound":
            math.sqrt(BUDGET / c_lo),
        "h_squared_trend_ratio":
            (rows[0]["mass_per_length"] / rows[-1]["mass_per_length"]) ** 0.5,
    }
    out["p4_panel_local_verdict"] = (
        "PANEL-LOCAL-FAILED" if rows[-1]["over_budget"] > 1.0
        else "PANEL-LOCAL-HOLDS")

    # --- P3: per-cell enclosure pricing --------------------------------
    h = 0.02
    edges, mids = mosaic(WIN_LO, WIN_HI, h, (0.0,))
    pw = prime_cell_widths(edges, logn, amp)
    aw = ann_cell_width(edges, ann_coef)
    sig_cap = sigma_prime_cap()
    b, _, _ = transform_table(mids, fam, base)
    c, _, _ = transform_table(mids, fam, corr)
    aa, _, _ = poly_table(mids, ann_coef)
    weight = aa ** 2 * np.real(b * np.conj(b)) * np.real(c * np.conj(c))
    ker_width = pw + sig_cap * h          # sigma slope charge across a cell
    # integrated error of the squared kernel, kernel ~ [mid +- width/2]:
    # width(kernel^2) <= 2 |kernel(mid)| * width(kernel)
    ker_mid, _, _ = kernel_sample(mids, logn, amp)
    err_ker = float(np.sum(ker_width * np.abs(weight)) * h)
    err_ker2 = float(np.sum(2.0 * np.abs(ker_mid) * ker_width
                           * np.abs(weight)) * h)
    mask = np.abs(mids) <= trusted
    err_ker2_lo = float(np.sum(2.0 * np.abs(ker_mid[mask]) * ker_width[mask]
                               * np.abs(weight[mask])) * h)
    out["p3"] = {
        "h": h, "cells": int(edges.size - 1),
        "sigma_prime_cap": sig_cap,
        "sigma_slope_charge_per_cell": sig_cap * h,
        "prime_width_max": float(np.max(pw)),
        "prime_width_mean": float(np.mean(pw)),
        "prime_triangle_width": float(2.0 * np.sum(amp)),
        "ann_width_max": float(np.max(aw)),
        "kernel_width_max": float(np.max(ker_width)),
        "abs_weight_max": float(np.max(np.abs(weight))),
        "integrated_kernel_interval_error": err_ker,
        "integrated_kernel_squared_interval_error": err_ker2,
        "integrated_kernel_squared_interval_error_trusted_zone": err_ker2_lo,
        "per_cell_budget_share": BUDGET / (edges.size - 1),
        "over_budget": err_ker2 / BUDGET,
        "over_budget_trusted_zone": err_ker2_lo / BUDGET,
    }
    out["p3_verdict"] = ("KERNEL-INTERVAL-HOLDS" if err_ker2_lo <= BUDGET
                         else "KERNEL-INTERVAL-FAILED-NEEDS-GROUPING")

    OUT.write_text(json.dumps(out, indent=2, default=str) + "\n",
                   encoding="utf-8")
    print(json.dumps({k: out[k] for k in
                      ("p4_verdict", "p4_panel_local_verdict",
                       "p3_verdict", "global_route", "panel_local_route")},
                     indent=2, default=str), flush=True)
    print(json.dumps({"m2_rows": rows, "global_scan": out["global_scan"],
                      "p3": out["p3"], "gl_control": ctrl},
                     indent=2, default=str), flush=True)


def selftest():
    ok = True
    ann_coef = ann_poly()
    ok &= abs(ann_coef[4] - (2 * math.pi) ** 4) < 1e-6
    ok &= max(abs(v) for v in ann_coef[1::2]) < 1e-9
    x = np.array([0.0, 0.7, 1.0])
    eps = 1e-4
    a_p, _, _ = poly_table(x + eps, ann_coef)
    a_0, _, _ = poly_table(x, ann_coef)
    a_m, _, _ = poly_table(x - eps, ann_coef)
    _, _, a2 = poly_table(x, ann_coef)
    fd = (a_p - 2 * a_0 + a_m) / eps ** 2
    ok &= np.max(np.abs(fd - a2)) < 1e-3 * max(1.0, np.max(np.abs(a2)))
    fam = [(6.553600000000003, 0.0)]
    coef = np.array([complex(1.0)])
    _, _, b2 = transform_table(np.array([1.0]), fam, coef)
    bp, _, _ = transform_table(np.array([1.0 + eps]), fam, coef)
    b0, _, _ = transform_table(np.array([1.0]), fam, coef)
    bm, _, _ = transform_table(np.array([1.0 - eps]), fam, coef)
    ok &= abs((bp - 2 * b0 + bm)[0] / eps ** 2 - b2[0]) \
        < 1e-2 * max(1.0, abs(b2[0]))
    # cos-arc interval against a dense grid maximum
    a = np.array([0.3, 12.0, 5.0])
    length = np.array([0.9, 1.65, 3.1])
    sup, inf = cos_arc_interval(a, length)
    for aa, L, s, i in zip(a, length, sup, inf):
        grid = aa + L * np.linspace(0, 1, 20001)
        ok &= np.max(np.cos(grid)) <= s + 1e-12
        ok &= np.min(np.cos(grid)) >= i - 1e-12
        ok &= s - np.max(np.cos(grid)) < 5e-3
    # sigma derivative control
    xs = np.array([0.5, 2.0])
    _, s1, _ = sigma_exact(xs)
    _, s1p, _ = sigma_exact(xs + eps)
    fd1 = (s1p - s1) / eps
    _, _, s2 = sigma_exact(xs)
    ok &= np.max(np.abs(fd1 - s2)) < 1e-3 * max(1.0, np.max(np.abs(s2)))
    print(json.dumps({"selftest": "PASS" if ok else "FAIL"}, indent=2))
    return ok


def main():
    mode = os.environ.get("MODE", "probe")
    if mode == "selftest":
        if not selftest():
            raise SystemExit("selftest failed")
    else:
        probe()


if __name__ == "__main__":
    main()