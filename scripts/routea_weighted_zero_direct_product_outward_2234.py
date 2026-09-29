"""Record 2234: outward enclosure of the direct-product mass screen.

First brick for the low-shell / B_zm side of the weighted-zero C3' ladder.
It re-evaluates the record-2197 screen with 256-bit MPFR RNDN arithmetic plus
an explicit forward-error slack, and encloses the four strip-weighted L1
norms

    base_M0(sigma) = ||base||_1,      base_D2(sigma) = ||base''||_1,
    corr_M0(sigma) = ||corr||_1,      corr_D2(sigma) = ||corr''||_1

on the committed NX=240001 physical grid and the committed 101-point sigma
grid of record 2197, then prices

    C_out = min(db*mc, dc*mb)/(2*pi)^2

outward with four further allowances:

  slack   each RNDN evaluation carries an absolute forward-error slack of
          2^-200 x (sum of term magnitudes).  The exp chain's condition
          amplification is bounded by sup_q (K/q) exp(-K/q) = 30 e^-30
          = 2.8e-12, so at 256-bit the effective margin over the naive
          gamma_n accounting exceeds 2^100.
  panel   trapezoid error per norm <= L * (2 a_max) * dx / 4 with an
          analytic global majorant from |phi^(k)| <= e^-K * poly(K, 1/a)
          for k <= 3 (master bound sup_{q in (0,1]} q^-m e^-K/q = e^-K for
          m <= 29).
  sigma   between grid points a norm is Lipschitz in sigma with
          d ln N / d sigma <= a_max, so two factors inflate by
          exp(2 a_max d_sigma).
  coeff   the record-2201 solve radii are charged per family through
          per-family absolute mass bounds (provisional radii: 2201 is a
          preflight, not a certificate).

Modes (environment):
  MODE=build                      build the construction cache (slow setup)
  MODE=smoke                      three-node U vs numpy drift control
  MODE=chunk CHUNK=k              one x-chunk -> results/2234_chunk_k.npz
  MODE=sigma SIGMA_INDEX=j        one sigma weighted sum -> 2234_sigma_j.json
  MODE=reduce                     assemble C_out and the outward ratio
"""
import ctypes as C
import importlib.util
import json
import math
import os
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
R = ROOT / "results"

RNDN = 0
SLACK_EXP = 200
NCHUNK_DEFAULT = 12
BUILD_CACHE = R / "2234_build_cache.npz"
def CHUNK(k):
    return R / f"2234_chunk_{k}.npz"


def SIGMA_JSON(j):
    return R / f"2234_sigma_{j}.json"
OUT_JSON = R / "2234_direct_product_outward.json"

R_BASE_2201 = 1.725905221940381e8        # record 2201 Neumann radii
R_CORR_2201 = 3.536472115641207e11
SIGNED_MARGIN = 1675397327895.099
SCREEN_2197 = {"C_upper": 77444.14398633591, "B_upper": 3057372.2573045553,
               "tail_upper": 3691230708.643563,
               "tail_over_margin": 0.0022031972041408675}
UP = lambda v: math.nextafter(v, math.inf)


def up_many(v, n):
    for _ in range(n):
        v = math.nextafter(v, math.inf)
    return v


def _load(name, filename):
    sp = importlib.util.spec_from_file_location(name, ROOT / "scripts" / filename)
    assert sp is not None and sp.loader is not None
    mod = importlib.util.module_from_spec(sp)
    sp.loader.exec_module(mod)
    return mod


m23 = _load("mpfr2223b", "routea_weighted_zero_mpfr_exp_binding_2223.py")
lib = m23._lib
M = m23.M
for name in ("mpfr_add", "mpfr_sub", "mpfr_div"):
    getattr(lib, name).argtypes = [m23._P, m23._P, m23._P, C.c_int]


class WB:
    """MPFR workbench: explicit-slot helpers + a stack allocator."""

    def __init__(self, n=64):
        self.t = [M() for _ in range(n)]
        self.sp = 0

    def push(self):
        i = self.sp
        self.sp += 1
        return self.t[i]

    def clear(self):
        for obj in self.t:
            obj.clear()

    def set(self, o, v):
        lib.mpfr_set_d(C.byref(o.x), C.c_double(v), 0)
        return o

    def add(self, o, a, b):
        lib.mpfr_add(C.byref(o.x), C.byref(a.x), C.byref(b.x), RNDN)
        return o

    def sub(self, o, a, b):
        lib.mpfr_sub(C.byref(o.x), C.byref(a.x), C.byref(b.x), RNDN)
        return o

    def mul(self, o, a, b):
        lib.mpfr_mul(C.byref(o.x), C.byref(a.x), C.byref(b.x), RNDN)
        return o

    def div(self, o, a, b):
        lib.mpfr_div(C.byref(o.x), C.byref(a.x), C.byref(b.x), RNDN)
        return o

    def exp(self, o, a):
        lib.mpfr_exp(C.byref(o.x), C.byref(a.x), RNDN)
        return o

    def sin(self, o, a):
        lib.mpfr_sin(C.byref(o.x), C.byref(a.x), RNDN)
        return o

    def cos(self, o, a):
        lib.mpfr_cos(C.byref(o.x), C.byref(a.x), RNDN)
        return o


def build_construction():
    """Rebuild the 2197 base/corr construction (same calls, same floats)."""
    if BUILD_CACHE.exists():
        z = np.load(BUILD_CACHE)
        fam = list(zip(z["fam_a"].tolist(), z["fam_theta"].tolist()))
        return fam, z["base"], z["corr"], float(z["a_max"])
    s97 = _load("s97b", "routea_weighted_zero_direct_product_mass_screen_2197.py")
    nodes, values, fam = s97.owner_family()
    a_max = max(a for a, _ in fam)
    base_xw = [s97.r59.phi_weights(a, panels=6, m=s97.M) for a, _ in fam]
    a_mat = s97.r80.family_values(fam, s97.K, np.asarray(nodes, complex),
                                  base_xw).T
    base = np.linalg.solve(a_mat, np.ones(len(nodes), complex))
    corr = np.linalg.solve(a_mat, np.asarray(values, complex))
    np.savez(BUILD_CACHE,
             fam_a=np.asarray([a for a, _ in fam], float),
             fam_theta=np.asarray([t for _, t in fam], float),
             base=base, corr=corr, a_max=a_max)
    return fam, base, corr, float(a_max)


def x_grid(a_max):
    s97 = _load("s97c", "routea_weighted_zero_direct_product_mass_screen_2197.py")
    return np.linspace(-a_max, a_max, s97.NX)


def node_bounds(wb, xv, fam_par, K, acc):
    """One x node: accumulate the 8 MPFR sums; return (U4, sockets).

    acc = 8 MPFR accumulators, pre-zeroed.  Returns the four upper bounds
    and the four magnitude sums used for the slack.
    """
    mags = [0.0, 0.0, 0.0, 0.0]          # b_M0, b_D2, c_M0, c_D2 magnitudes
    for a, th, bc, cc in fam_par:
        sp0 = wb.sp
        u = wb.div(wb.push(), wb.set(wb.push(), xv), wb.set(wb.push(), a))
        one = wb.set(wb.push(), 1.0)
        q = wb.sub(wb.push(), one, wb.mul(wb.push(), u, u))
        if q.get_d(RNDN) <= 0.0:
            wb.sp = sp0
            continue
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
        gib = math.hypot(g_val.get_d(RNDN), h_val.get_d(RNDN)) + 1.0
        phi_f = phi.get_d(RNDN)
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
            mag = abs(cf) * phi_f
            mags[base_index] += mag
            mags[2 + base_index] += mag * gib
        wb.sp = sp0
    zero4 = [0.0, 0.0, 0.0, 0.0]
    return zero4, mags


def chunk_worker(k, nchunk):
    s97 = _load("s97d", "routea_weighted_zero_direct_product_mass_screen_2197.py")
    fam, base, corr, a_max = build_construction()
    x = x_grid(a_max)
    n = x.shape[0]
    i0 = (n * k) // nchunk
    i1 = (n * (k + 1)) // nchunk
    K = s97.K
    wb = WB(80)
    acc = [M() for _ in range(8)]
    fam_par = [(a, th, complex(bc), complex(cc))
               for (a, th), bc, cc in zip(fam, base, corr)]
    U = np.empty((4, i1 - i0))
    slack = np.zeros((4, i1 - i0))
    try:
        for row, i in enumerate(range(i0, i1)):
            xv = float(x[i])
            for o in acc:
                lib.mpfr_set_d(C.byref(o.x), C.c_double(0.0), 0)
            _, mags = node_bounds(wb, xv, fam_par, K, acc)
            s = [up_many((2.0 ** -SLACK_EXP) * mg, 3) for mg in mags]
            b = math.hypot(acc[0].get_d(RNDN), acc[1].get_d(RNDN))
            b2 = math.hypot(acc[2].get_d(RNDN), acc[3].get_d(RNDN))
            c = math.hypot(acc[4].get_d(RNDN), acc[5].get_d(RNDN))
            c2 = math.hypot(acc[6].get_d(RNDN), acc[7].get_d(RNDN))
            U[0, row] = up_many(b + s[0], 3)
            U[1, row] = up_many(b2 + s[1], 3)
            U[2, row] = up_many(c + s[2], 3)
            U[3, row] = up_many(c2 + s[3], 3)
            for q in range(4):
                slack[q, row] = s[q]
    finally:
        for o in acc:
            o.clear()
        wb.clear()
    np.savez(CHUNK(k), i0=np.asarray(i0), i1=np.asarray(i1), U=U,
             slack=slack, a_max=np.asarray(a_max))
    print(json.dumps({"mode": "chunk", "chunk": k, "i0": int(i0),
                      "i1": int(i1),
                      "max_U_base": float(U[0].max()),
                      "max_U_base_D2": float(U[1].max()),
                      "max_U_corr": float(U[2].max()),
                      "max_U_corr_D2": float(U[3].max()),
                      "max_slack": float(slack.max())}), flush=True)


def smoke():
    """Three-node drift control: MPFR U vs the committed numpy evaluation."""
    s97 = _load("s97s", "routea_weighted_zero_direct_product_mass_screen_2197.py")
    fam, base, corr, a_max = build_construction()
    x = x_grid(a_max)
    K = s97.K
    wb = WB(80)
    acc = [M() for _ in range(8)]
    fam_par = [(a, th, complex(bc), complex(cc))
               for (a, th), bc, cc in zip(fam, base, corr)]
    idx = [0, 1, 2, x.shape[0] // 3, x.shape[0] // 2, x.shape[0] - 1]
    rows = []
    try:
        for i in idx:
            xv = float(x[i])
            for o in acc:
                lib.mpfr_set_d(C.byref(o.x), C.c_double(0.0), 0)
            _, mags = node_bounds(wb, xv, fam_par, K, acc)
            u = (math.hypot(acc[0].get_d(RNDN), acc[1].get_d(RNDN)),
                 math.hypot(acc[2].get_d(RNDN), acc[3].get_d(RNDN)),
                 math.hypot(acc[4].get_d(RNDN), acc[5].get_d(RNDN)),
                 math.hypot(acc[6].get_d(RNDN), acc[7].get_d(RNDN)))
            # numpy reference on the same x node
            vals = np.zeros(4, dtype=float)
            bu = cu = 0j
            bu2 = cu2 = 0j
            xa = np.asarray([xv])
            for j, (a, th) in enumerate(fam):
                uu = xa / a
                qq = 1.0 - uu * uu
                if qq[0] <= 0.0:
                    continue
                ph = np.exp(-K / qq)
                e1 = -2.0 * K * uu / (a * qq ** 2)
                e2 = (-2.0 * K / (a * a) * (1.0 / qq ** 2
                                            + 4.0 * uu ** 2 / qq ** 3))
                phz = np.exp(1j * th * xa)
                bu += base[j] * ph * phz
                bu2 += base[j] * ph * (e2 + e1 * e1 + 2j * th * e1
                                       - th * th) * phz
                cu += corr[j] * ph * phz
                cu2 += corr[j] * ph * (e2 + e1 * e1 + 2j * th * e1
                                       - th * th) * phz
            vals = [float(np.ravel(np.abs(np.asarray(v)))[0])
                    for v in (bu, bu2, cu, cu2)]
            rows.append({"i": i, "x": xv,
                         "mpfr": u, "numpy_abs": vals,
                         "sockets": [up_many(b, 3) - v for b, v in zip(u, vals)],
                         "slack": [up_many((2.0 ** -SLACK_EXP) * mg, 3)
                                   for mg in mags]})
        print(json.dumps({"mode": "smoke", "K": K, "a_max": a_max,
                          "rows": rows}, indent=2), flush=True)
    finally:
        for o in acc:
            o.clear()
        wb.clear()


def sigma_worker(j):
    s97 = _load("s97e", "routea_weighted_zero_direct_product_mass_screen_2197.py")
    sigma = j / 100.0
    parts = []
    a_max = None
    n_total = 0
    for k in range(NCHUNK_DEFAULT):
        z = np.load(CHUNK(k))
        parts.append((int(z["i0"]), int(z["i1"]), z["U"]))
        a_max = float(z["a_max"])
        n_total += z["U"].shape[1]
    assert a_max is not None
    x = x_grid(a_max)
    dx = (2.0 * a_max) / (s97.NX - 1)
    wb = WB(8)
    accs = [M() for _ in range(4)]
    try:
        for o in accs:
            lib.mpfr_set_d(C.byref(o.x), C.c_double(0.0), 0)
        for i0, i1, U in sorted(parts):
            for row in range(U.shape[1]):
                i = i0 + row
                w = wb.exp(wb.t[0], wb.mul(wb.t[1],
                                           wb.set(wb.t[2], sigma),
                                           wb.set(wb.t[3], float(x[i]))))
                tw = 1.0 if (i == 0 or i == s97.NX - 1) else 2.0
                for q in range(4):
                    term = wb.mul(wb.t[4],
                                  wb.set(wb.t[5], float(U[q, row]) * tw), w)
                    lib.mpfr_add(C.byref(accs[q].x), C.byref(accs[q].x),
                                 C.byref(term.x), RNDN)
        factor = up_many(dx / 2.0, 4)
        out = {"record": 2234, "mode": "sigma", "sigma": sigma,
               "sigma_index": j, "nodes": n_total, "values": {}}
        for name, o in zip(("base_M0", "base_D2", "corr_M0", "corr_D2"), accs):
            out["values"][name] = up_many(o.get_d(RNDN) * factor, 4)
    finally:
        wb.clear()
        for o in accs:
            o.clear()
    SIGMA_JSON(j).write_text(json.dumps(out, indent=2) + "\n",
                                    encoding="utf-8")
    print(json.dumps({"sigma": sigma, "values": out["values"]}), flush=True)


def majorant_phi_le(k, K, a):
    """Global bound on sup |phi^(k)| on the support."""
    eK = math.exp(-K)
    if k == 0:
        return eK
    if k == 1:
        return (2.0 * K / a) * eK
    if k == 2:
        return eK * (10.0 * K + 4.0 * K * K) / (a * a)
    if k == 3:
        return eK * (72.0 * K + 30.0 * K * K + 8.0 * K ** 3) / (a ** 3)
    raise ValueError(k)


def integrand_lipschitz(coef, fam, K, a_max, sigma):
    m1 = m2 = m3 = 0.0
    for (a, th), c in zip(fam, coef):
        w = abs(complex(c))
        c0 = majorant_phi_le(0, K, a)
        c1 = majorant_phi_le(1, K, a)
        c2 = majorant_phi_le(2, K, a)
        c3 = majorant_phi_le(3, K, a)
        m1 += w * (c1 + abs(th) * c0)
        m2 += w * (c2 + 2.0 * abs(th) * c1 + th * th * c0)
        m3 += w * (c3 + 3.0 * abs(th) * c2 + 3.0 * th * th * c1
                   + abs(th) ** 3 * c0)
    g = math.exp(min(sigma, 1.0) * a_max)
    return g * m1, g * (m2 + m3)


def coeff_inflation(coef, fam, K, a_max, sigma, radius, order):
    s = 0.0
    for (a, _), _c in zip(fam, coef):
        s += 2.0 * a * math.exp(sigma * a_max) * majorant_phi_le(order, K, a)
    return radius * s


def reduce_worker():
    s97 = _load("s97f", "routea_weighted_zero_direct_product_mass_screen_2197.py")
    fam, base, corr, a_max = build_construction()
    d_sigma = 0.01
    cover1 = math.exp(a_max * d_sigma)
    rows = []
    missing = [j for j in range(101) if not SIGMA_JSON(j).exists()]
    for j in range(101):
        p = SIGMA_JSON(j)
        if p.exists():
            rows.append(json.loads(p.read_text(encoding="utf-8")))
    dx = (2.0 * a_max) / (s97.NX - 1)
    best = None
    for row in rows:
        sigma = row["sigma"]
        v = row["values"]
        L_b, L_b2 = integrand_lipschitz(base, fam, s97.K, a_max, sigma)
        L_c, L_c2 = integrand_lipschitz(corr, fam, s97.K, a_max, sigma)
        panel = lambda L: L * (2.0 * a_max) * dx / 4.0
        pb = panel(L_b)
        pb2 = panel(L_b2)
        pc = panel(L_c)
        pc2 = panel(L_c2)
        eb = coeff_inflation(base, fam, s97.K, a_max, sigma, R_BASE_2201, 0)
        ec = coeff_inflation(corr, fam, s97.K, a_max, sigma, R_CORR_2201, 0)
        eb2 = coeff_inflation(base, fam, s97.K, a_max, sigma, R_BASE_2201, 2)
        ec2 = coeff_inflation(corr, fam, s97.K, a_max, sigma, R_CORR_2201, 2)
        mb = up_many(up_many((v["base_M0"] + pb) * (1.0 + eb), 3) * cover1, 3)
        db = up_many(up_many((v["base_D2"] + pb2) * (1.0 + eb2), 3) * cover1,
                     3)
        mc = up_many(up_many((v["corr_M0"] + pc) * (1.0 + ec), 3) * cover1, 3)
        dc = up_many(up_many((v["corr_D2"] + pc2) * (1.0 + ec2), 3) * cover1,
                     3)
        tp2 = up_many((2.0 * math.pi) ** 2, 3)
        c1 = up_many(up_many(db * mc, 3) / tp2, 3)
        c2 = up_many(up_many(dc * mb, 3) / tp2, 3)
        row_out = {"sigma": sigma, "base_M0": mb, "base_D2": db,
                   "corr_M0": mc, "corr_D2": dc,
                   "panel_base": pb, "panel_base_D2": pb2,
                   "panel_corr": pc, "panel_corr_D2": pc2,
                   "coeff_infl_base": eb, "coeff_infl_corr": ec,
                   "coeff_infl_base_D2": eb2, "coeff_infl_corr_D2": ec2,
                   "C_channel_a": c1, "C_channel_b": c2,
                   "C_upper": min(c1, c2)}
        rows[rows.index(row)] = row_out
        if best is None or row_out["C_upper"] > best["C_upper"]:
            best = row_out
    xi2 = math.pi / 6.0
    kernel_small = (1.0 / math.pi) ** 0.25 * math.gamma(0.25)
    xi_tail = 2.0 / (1.0 - math.exp(-math.pi))
    xi_growth = 2.0 * xi_tail * (kernel_small + 1.0)
    mult = (xi_growth + 1.0 + abs(math.log(xi2)) + 192.0) / math.log(2.0)
    assert best is not None
    b_upper = up_many(up_many((2.0 * math.pi) ** 2, 3) * best["C_upper"], 3)
    tail_upper = up_many(up_many(4.0 * mult, 3) * b_upper, 3)
    result = {
        "record": 2234,
        "status": ("DIRECT-PRODUCT-OUTWARD-SCREEN" if not missing
                   else "DIRECT-PRODUCT-OUTWARD-INCOMPLETE"),
        "owner": {"gamma": s97.GAMMA, "delta": s97.DELTA, "scale": s97.SCALE,
                  "nodes": len(fam), "a_max": a_max},
        "grid": {"x_nodes": s97.NX, "sigma_nodes": len(rows), "dx": dx,
                 "d_sigma": d_sigma, "sigma_cover": cover1},
        "binding_row": best,
        "screen": {"C_upper": best["C_upper"], "B_upper": b_upper,
                   "spectralMultiplicityConstant_proxy": mult,
                   "high_shell_budget_upper": tail_upper,
                   "signed_margin_anchor": SIGNED_MARGIN,
                   "tail_upper_over_margin": tail_upper / SIGNED_MARGIN},
        "comparison_2197": SCREEN_2197,
        "inflation_over_2197": {"C": best["C_upper"] / SCREEN_2197["C_upper"],
                                "tail": tail_upper / SCREEN_2197["tail_upper"]},
        "allowances": {
            "slack": "2^-200 x term-magnitude sum per node; exp-chain "
                     "amplification <= 30 e^-30 = 2.8e-12 at 256-bit; margin "
                     "over naive gamma_n exceeds 2^100",
            "panel": "L * (2 a_max) * dx / 4 with analytic phi^(k) bounds",
            "sigma": "exp(a_max d_sigma) per norm between grid points",
            "coeff": "record-2201 provisional radii charged per family",
        },
        "missing_sigma": missing,
        "nonclaims": [
            "the multiplicity constant is still the 2197 diagnostic proxy",
            "the 2201 coefficient radii are provisional (preflight)",
            "complete-owner transfer, the signed producer margin, and the "
            "B_zm < epsilon gate remain open",
            "no producer or RH claim",
        ],
        "provenance": {
            "script": "scripts/routea_weighted_zero_direct_product_outward_2234.py",
            "base_screen": "scripts/routea_weighted_zero_direct_product_mass_screen_2197.py",
        },
    }
    result["sigma_rows"] = [{k: r[k] for k in
                             ("sigma", "C_upper", "C_channel_a", "C_channel_b")}
                            for r in rows]
    OUT_JSON.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": result["status"],
                      "binding_sigma": best["sigma"],
                      "C_upper": best["C_upper"],
                      "ratio": result["screen"]["tail_upper_over_margin"],
                      "inflation": result["inflation_over_2197"],
                      "missing_sigma": missing}, indent=2), flush=True)


def main():
    mode = os.environ.get("MODE", "reduce")
    if mode == "build":
        fam, base, corr, a_max = build_construction()
        print(json.dumps({"mode": "build", "cache": str(BUILD_CACHE),
                          "families": len(fam), "a_max": a_max}))
    elif mode == "smoke":
        smoke()
    elif mode == "chunk":
        chunk_worker(int(os.environ["CHUNK"]),
                     int(os.environ.get("NCHUNK", NCHUNK_DEFAULT)))
    elif mode == "sigma":
        sigma_worker(int(os.environ["SIGMA_INDEX"]))
    elif mode == "reduce":
        reduce_worker()
    else:
        raise SystemExit(f"unknown MODE={mode}")


if __name__ == "__main__":
    main()