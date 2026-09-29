"""Record 2249 -- L1 first brick: certified downward enclosure of the
finite-window functional q at the anchor candidate of record 2103.

Discrete object (defined by this script; convention A of record 2230 --
stored operands are exact):

    q_disc = sum_i w_i * G(x_i),  x_i = arange(-40, 40+dx/2, dx), dx=0.02,
    w_i = 1/50 interior, 1/100 endpoints (exact reals),
    G(x) = kernel(x) * p(x)^2 * |Lb(x)|^2 * |Lc(x)|^2,

with the stored operands: family (scale*width, -height) list from the
1980/1994/1981 chain, GL(6400) phi nodes/weights, the 52 prime powers of
the support, the four centred annihilator nodes, the grid, and the
binary64 coefficient vectors base/corr returned by the LAPACK solve of the
stored matrix and right-hand sides.  Every arithmetic operation is
evaluated together with a first-order forward-error shadow

    |fl_chain(inputs) - exact_chain(inputs)| <= E(x)   (per grid point),

so that q_lo = fl_sum - E_total is a certified lower bound of q_disc.
Charges: 2^-52 per elementary double op (2x machine eps, covers 1 ulp);
64 * 2^-53 * sum|terms| for each pairwise reduction of n terms (depth
bound log2(n)+1 <= 17 for 38400, charged 64); np.exp/cos/sin at most 1 ulp
(charged through the same 2^-52 plus the derivative term).  The model's
own float arithmetic is covered by a final relative inflation of 1e-6.

Modes: MODE=smoke (first SMOKE_F families, first SMOKE_X grid points).
Artifact: results/2249_l1_enclosure.json
"""
import hashlib
import json
import math
import os
import sys
import time
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import fourpoint_owner_completion_1980 as r80      # noqa: E402
import fourpoint_owner_density_1959 as r59         # noqa: E402
import routea_opposite_gates_height_1994 as r94    # noqa: E402
import fourpoint_offline_owner_1981 as r81         # noqa: E402

import mpmath as mp                                # noqa: E402

GAMMA = 39.25244858548658
DELTA = 0.445
SCALE = 0.80
K = 30.0
M = 6400
STEP = 0.02
XMAX = 40.0
CHUNK = 16

U = 2.0 ** -52          # per elementary op (2x machine eps)
SUMCHARGE = 64.0 * 2.0 ** -53   # pairwise reduction of ~38400 terms
INFLATE = 1.0 + 1e-6    # covers the model's own float arithmetic

MODE = os.environ.get("MODE", "reduce")
SMOKE_F = int(os.environ.get("SMOKE_F", "2"))
SMOKE_X = int(os.environ.get("SMOKE_X", "64"))
SMOKE_LO = int(os.environ.get("SMOKE_LO", "0"))


# ------------------------------------------------------------ op shadows

def m2(a, ea, b, eb):
    v = a * b
    return v, ea * np.abs(b) + np.abs(a) * eb + U * np.abs(v)


def a2(a, ea, b, eb):
    v = a + b
    return v, ea + eb + U * np.abs(v)


def s2(a, ea, b, eb):
    v = a - b
    return v, ea + eb + U * np.abs(v)


def exp_in(x, ex):
    v = np.exp(x)
    return v, np.abs(v) * ex + U * np.abs(v)


def cos_in(x, ex):
    v = np.cos(x)
    return v, ex + U * np.abs(v)        # |d cos| = |sin| <= 1


def sin_in(x, ex):
    v = np.sin(x)
    return v, ex + U * np.abs(v)


def sq_in(x, ex):
    return m2(x, ex, x, ex)


# ------------------------------------------------------------ operands

def build():
    rho = (0.5 + DELTA) + 1j * GAMMA
    nodes, values = r94.owner_nodes_ext(rho, GAMMA)
    radius = r80.ball_radius(rho, 0)
    mp.mp.dps = 50
    for index in range(1, 31):
        height = float(mp.im(mp.zetazero(index)))
        z = 0.5 + 1j * height
        if abs(z - rho) <= radius and all(
                abs(z - existing) > 1e-6 for existing in nodes):
            nodes.append(z)
            values.append(0j)
    plan = {"main": 0, "real": 0}
    fam = []
    for z in nodes:
        height = float(z.imag)
        if abs(abs(height) - GAMMA) < 1e-9:
            idx = plan["main"]
            plan["main"] += 1
            width = r81.WIDTHS_H1[idx]
        elif abs(height) < 1e-9:
            idx = plan["real"]
            plan["real"] += 1
            width = r81.WIDTHS_REAL[idx]
        else:
            width = 2.2
        fam.append((SCALE * width, -height))
    return rho, nodes, values, fam


_GL_XS = None
_GL_WS = None


def phi_weights_cached(a, panels=6):
    """bitwise copy of r59.phi_weights sharing one leggauss(M) call."""
    global _GL_XS, _GL_WS
    if _GL_XS is None:
        _GL_XS, _GL_WS = np.polynomial.legendre.leggauss(M)
    xs, ws = _GL_XS, _GL_WS
    edges = np.linspace(-a, a, panels + 1)
    X, W = [], []
    for j in range(panels):
        lo, hi = edges[j], edges[j + 1]
        X.append(0.5 * (hi - lo) * xs + 0.5 * (lo + hi))
        W.append(0.5 * (hi - lo) * ws)
    return np.concatenate(X), np.concatenate(W)


def phi_terms(a, XW):
    """(X, f, ef): stored GL nodes and instrumented phi*W weight f."""
    X, W = XW
    up = np.abs(X) / a
    eup = U * np.abs(up)
    sq, esq = sq_in(up, eup)
    one = np.ones_like(X)
    v, ev = s2(one, np.zeros_like(X), sq, esq)
    w = K / v
    ew = K / (v * v) * ev + U * np.abs(w)     # quotient derivative K/v^2
    y = -w
    ey = ew
    e, ee = exp_in(y, ey)
    f, ef = m2(e, ee, W, np.zeros_like(W))
    return X, f, ef


# ------------------------------------------------------------ components

def laplace_rows(a, th, X, f, ef, xs):
    """v_j(x) = a * sum_p f_p e^{sigma X_p} (cos psi + i sin psi),
    psi = a (th - 2 pi x) X_p, sigma = a/2 (exact).  Returns (16-ish, n)
    value/error matrices over xs."""
    sigma = 0.5 * a                                  # exact (a/2)
    t, et = m2(sigma, 0.0, X, np.zeros_like(X))
    e, ee = exp_in(t, et)                            # shared across xs
    om = 2.0 * math.pi * xs
    eom = U * np.abs(om)
    d, ed = s2(np.full_like(om, th), np.zeros_like(om), om, eom)
    wv, ewv = m2(a, 0.0, d, ed)
    psi, epsi = m2(wv[:, None], ewv[:, None], X[None, :],
                   np.zeros_like(X)[None, :])
    c, ec = cos_in(psi, epsi)
    s, es = sin_in(psi, epsi)
    g1, eg1 = m2(f[None, :], ef[None, :], e[None, :], ee[None, :])
    tre, etre = m2(g1, eg1, c, ec)
    tri, etri = m2(g1, eg1, s, es)
    sre = np.sum(tre, axis=1)
    esre = np.sum(etre, axis=1) + SUMCHARGE * np.sum(np.abs(tre), axis=1)
    sim = np.sum(tri, axis=1)
    esim = np.sum(etri, axis=1) + SUMCHARGE * np.sum(np.abs(tri), axis=1)
    vre, evre = m2(a, 0.0, sre, esre)
    vim, evim = m2(a, 0.0, sim, esim)
    return vre, evre, vim, evim


def dot30(re_mat, ere, im_mat, eim, coef):
    """complex sum over 30 rows with exact complex coefficients."""
    br = coef.real[:, None]
    bi = coef.imag[:, None]
    t1, e1 = m2(br, np.zeros_like(br), re_mat, ere)
    t2, e2 = m2(bi, np.zeros_like(bi), im_mat, eim)
    wre, ewre = s2(t1, e1, t2, e2)
    t3, e3 = m2(br, np.zeros_like(br), im_mat, eim)
    t4, e4 = m2(bi, np.zeros_like(bi), re_mat, ere)
    wim, ewim = a2(t3, e3, t4, e4)
    lre = np.sum(wre, axis=0)
    elre = np.sum(ewre, axis=0) + SUMCHARGE * np.sum(np.abs(wre), axis=0)
    lim = np.sum(wim, axis=0)
    elim = np.sum(ewim, axis=0) + SUMCHARGE * np.sum(np.abs(wim), axis=0)
    return lre, elre, lim, elim


def sq_abs(re, ere, im, eim):
    h1, eh1 = sq_in(re, ere)
    h2, eh2 = sq_in(im, eim)
    return a2(h1, eh1, h2, eh2)


def kernel_instrumented(xs):
    """copy of rig.sigma_vec + the 52 prime cosines, with shadows."""
    om = 2.0 * math.pi * xs
    eom = U * np.abs(om)
    zim = -0.5 * om
    ezim = 0.5 * eom + U * np.abs(zim)      # (-0.5)*om, one op
    sre = np.zeros_like(xs)
    esre = np.zeros_like(xs)
    sim = np.zeros_like(xs)
    esim = np.zeros_like(xs)
    for j in range(8):
        dre = 0.25 + j                       # exact
        dim = zim
        edim = ezim
        h, eh = a2(*sq_in(dre, np.zeros_like(xs)), *sq_in(dim, edim))
        ire = dre / h
        eire = np.abs(ire) * eh / h + U * np.abs(ire)
        iim = -dim / h
        wiim = dim / h
        eiim = (edim + np.abs(wiim) * eh) / h + U * np.abs(iim)
        sre, esre = a2(sre, esre, ire, eire)
        sim, esim = a2(sim, esim, iim, eiim)
    zre = 0.25 + 8.0                         # exact
    zc_re, ezc_re = (zre, np.zeros_like(xs))
    zc_im, ezc_im = (zim, ezim)
    # zz2 = zz * zz
    p1, ep1 = m2(zc_re, ezc_re, zc_re, ezc_re)
    p2, ep2 = m2(zc_im, ezc_im, zc_im, ezc_im)
    z2re, ez2re = s2(p1, ep1, p2, ep2)
    p3, ep3 = m2(zc_re, ezc_re, zc_im, ezc_im)
    z2im, ez2im = m2(2.0, 0.0, p3, ep3)
    # corr = sum b / pw, pw = zz2^k
    terms = [1 / 12, -1 / 120, 1 / 252, -1 / 240, 1 / 132, -691 / 32760]
    corr_re = np.zeros_like(xs)
    ecorr_re = np.zeros_like(xs)
    corr_im = np.zeros_like(xs)
    ecorr_im = np.zeros_like(xs)
    pwre, epwre = z2re, ez2re
    pwim, epwim = z2im, ez2im
    for b in terms:
        h, eh = a2(*sq_in(pwre, epwre), *sq_in(pwim, epwim))
        tre = b * pwre / h
        etre = np.abs(tre) * eh / h + 2.0 * U * np.abs(tre)
        tim = -b * pwim / h
        etim = np.abs(tim) * eh / h + 2.0 * U * np.abs(tim)
        corr_re, ecorr_re = a2(corr_re, ecorr_re, tre, etre)
        corr_im, ecorr_im = a2(corr_im, ecorr_im, tim, etim)
        t5, e5 = m2(pwre, epwre, z2re, ez2re)
        t6, e6 = m2(pwim, epwim, z2im, ez2im)
        nre, enre = s2(t5, e5, t6, e6)
        t7, e7 = m2(pwre, epwre, z2im, ez2im)
        t8, e8 = m2(pwim, epwim, z2re, ez2re)
        nim, enim = a2(t7, e7, t8, e8)
        pwre, epwre = nre, enre
        pwim, epwim = nim, enim
    # psi = log(zz) - 0.5/zz - corr - s
    h, eh = a2(*sq_in(zc_re, ezc_re), *sq_in(zc_im, ezc_im))
    lg = 0.5 * np.log(h)
    elg = 0.5 * (eh / h) + U * np.abs(lg)
    arg = np.arctan2(zc_im, zc_re)
    earg = (np.abs(zc_re) * ezc_im) / h + U * np.abs(arg)
    qre = 0.5 * zc_re / h
    eqre = np.abs(qre) * eh / h + U * np.abs(qre)
    qim = -0.5 * zc_im / h
    eqim = np.abs(qim) * eh / h + U * np.abs(qim)
    lre, elre = s2(lg, elg, qre, eqre)
    lim, elim = s2(arg, earg, qim, eqim)
    lre, elre = s2(lre, elre, corr_re, ecorr_re)
    lim, elim = s2(lim, elim, corr_im, ecorr_im)
    lre, elre = s2(lre, elre, sre, esre)
    lim, elim = s2(lim, elim, sim, esim)
    kern = r59.rig.LOGPI - lre
    ekern = elre + U * np.abs(kern)
    return kern, ekern


def kernel_full(xs, primes):
    kern, ekern = kernel_instrumented(xs)
    lnn = np.array([math.log(pair[0]) for pair in primes])
    cst = np.array([2.0 * w / math.sqrt(n) for n, w in primes])
    ecst = 2.0 * U * np.abs(cst)             # sqrt + division
    for idx in range(len(primes)):
        psi, epsi = m2(2.0 * math.pi * xs, U * np.abs(2.0 * math.pi * xs),
                       lnn[idx], 0.0)
        c, ec = cos_in(psi, epsi)
        term, eterm = m2(cst[idx], ecst[idx], c, ec)
        kern, ekern = a2(kern, ekern, term, eterm)
    return kern, ekern


def p_instrumented(xs, nodes4):
    sim = -2.0 * math.pi * xs
    esim = U * np.abs(sim)
    pre = np.ones_like(xs)
    epre = np.zeros_like(xs)
    pim = np.zeros_like(xs)
    epim = np.zeros_like(xs)
    for a in nodes4:
        fre = np.full_like(xs, a.real)
        efre = np.zeros_like(xs)
        fim, efim = s2(np.full_like(xs, a.imag), np.zeros_like(xs), sim, esim)
        # (pre + i pim) * (fre + i fim)
        t1, e1 = m2(pre, epre, fre, efre)
        t2, e2 = m2(pim, epim, fim, efim)
        nre, enre = s2(t1, e1, t2, e2)
        t3, e3 = m2(pre, epre, fim, efim)
        t4, e4 = m2(pim, epim, fre, efre)
        nim, enim = a2(t3, e3, t4, e4)
        pre, epre, pim, epim = nre, enre, nim, enim
    p = pre
    ep = epre + U * np.abs(p)                # Re() of the complex product
    return p, ep


# ------------------------------------------------------------ main

def main():
    t_start = time.time()
    rho, nodes, values, fam = build()
    grid = np.arange(-XMAX, XMAX + STEP / 2, STEP)
    if MODE == "smoke":
        grid = grid[SMOKE_LO:SMOKE_LO + SMOKE_X]
    npts = grid.shape[0]
    nfam = len(fam)
    xw_cache = {}
    xw = []
    for pair in fam:
        a = pair[0]
        if float(a) not in xw_cache:
            xw_cache[float(a)] = phi_weights_cached(a)
        xw.append(xw_cache[float(a)])
    # operand identity: the cached builder is bitwise r59.phi_weights
    ref_x, ref_w = r59.phi_weights(fam[0][0], panels=6, m=M)
    gl_identity_ok = (np.array_equal(ref_x, xw[0][0])
                      and np.array_equal(ref_w, xw[0][1]))
    a_mat = r80.family_values(fam, K, np.asarray(nodes, complex), xw).T
    base = np.linalg.solve(a_mat, np.ones(len(nodes), complex))
    corr = np.linalg.solve(a_mat, np.asarray(values, complex))
    base_md5 = hashlib.md5(np.ascontiguousarray(base).tobytes()).hexdigest()
    corr_md5 = hashlib.md5(np.ascontiguousarray(corr).tobytes()).hexdigest()

    # instrumented family tables
    tables = []
    for j, (a, th) in enumerate(fam):
        X, f, ef = phi_terms(a, xw[j])
        tables.append((a, th, X, f, ef))

    vre = np.zeros((nfam, npts))
    evre = np.zeros((nfam, npts))
    vim = np.zeros((nfam, npts))
    evim = np.zeros((nfam, npts))
    for j, (a, th, X, f, ef) in enumerate(tables):
        for lo in range(0, npts, CHUNK):
            hi = min(lo + CHUNK, npts)
            r0, er0, i0, ei0 = laplace_rows(a, th, X, f, ef, grid[lo:hi])
            vre[j, lo:hi] = r0
            evre[j, lo:hi] = er0
            vim[j, lo:hi] = i0
            evim[j, lo:hi] = ei0
        print("family %d/%d done  %.1fs" % (j + 1, nfam, time.time() - t_start),
              flush=True)

    lre, elre, lim, elim = dot30(vre, evre, vim, evim, base)
    cre, ecre, cim, ecim = dot30(vre, evre, vim, evim, corr)
    hb, ehb = sq_abs(lre, elre, lim, elim)
    hc, ehc = sq_abs(cre, ecre, cim, ecim)

    support = 2 * max(pair[0] for pair in fam)
    primes = r59.rig.prime_powers_up_to(math.exp(support))
    kern, ekern = kernel_full(grid, primes)
    p, ep = p_instrumented(grid, r80.counterpart_nodes(rho))
    p2, ep2 = m2(p, ep, p, ep)
    g, eg = m2(kern, ekern, p2, ep2)
    g, eg = m2(g, eg, hb, ehb)
    g, eg = m2(g, eg, hc, ehc)

    w = np.full(npts, 1.0 / 50.0)
    if npts > 1:
        w[0] = 1.0 / 100.0
        w[-1] = 1.0 / 100.0

    # cross-check: plain float pipeline of record 2103 on the same grid
    vp = r80.family_values(fam, K, 0.5 - 2j * np.pi * grid, xw)
    lbp = base @ vp
    lcp = corr @ vp
    pp = np.real(r59.P_from_nodes(grid, r80.counterpart_nodes(rho)))
    kp = r59.rig.sigma_vec(2.0 * np.pi * grid)
    for number, weight in primes:
        kp = kp + 2 * weight / math.sqrt(number) * np.cos(
            2 * np.pi * grid * math.log(number))
    gp = kp * pp * pp * np.abs(lbp) ** 2 * np.abs(lcp) ** 2
    q_plain = float(np.trapezoid(gp, grid))

    terms = [float(w[i] * g[i]) for i in range(npts)]
    q = math.fsum(terms)
    e_pts = [float(w[i] * eg[i]) for i in range(npts)]
    e_pts_round = U * math.fsum([abs(e_pts[i]) for i in range(npts)])
    e_prod = U * math.fsum([abs(t) for t in terms])
    e_sum = math.fsum(e_pts) + e_pts_round + e_prod + U * abs(q)
    e_total = INFLATE * e_sum
    q_lo = q - e_total
    q_hi = q + e_total

    # diagnostics
    diag = {
        "families": nfam, "points": npts,
        "gl_identity_ok": gl_identity_ok,
        "base_md5": base_md5, "corr_md5": corr_md5,
        "cond": float(np.linalg.cond(a_mat)),
        "base_abs_max": float(np.abs(base).max()),
        "corr_abs_max": float(np.abs(corr).max()),
        "q": q, "E_total": e_total, "E_over_abs_q": e_total / abs(q),
        "q_lo": q_lo, "q_hi": q_hi,
        "g_abs_max": float(np.abs(g).max()),
        "sum_abs_wg": float(math.fsum([abs(t) for t in terms])),
        "cancel_factor": float(math.fsum([abs(t) for t in terms]) / abs(q)),
        "abs_hb_min": float(hb.min()), "abs_hb_max": float(hb.max()),
        "abs_hc_min": float(hc.min()), "abs_hc_max": float(hc.max()),
        "eg_over_g_max": float((eg / np.abs(g)).max()),
        "q_plain_2103_pipeline": q_plain,
        "max_abs_g_diff_vs_plain": float(np.max(np.abs(g - gp))),
        "rel_g_diff_at_peak": float(
            np.abs(g - gp)[int(np.argmax(np.abs(g)))]
            / max(abs(gp[int(np.argmax(np.abs(g)))]), 1e-300)),
    }
    live = np.abs(g) > 1e-9 * float(np.abs(g).max())
    if live.any():
        diag["eg_over_g_max_live"] = float((eg[live] / np.abs(g[live])).max())
        diag["live_points"] = int(live.sum())
    jmid = npts // 2
    vm = vre[:, jmid] + 1j * vim[:, jmid]
    vd = np.abs(vm - vp[:, jmid]) / np.abs(vp[:, jmid])
    diag["rel_v_diff_mid"] = float(vd.max())
    jbad = int(np.argmax(vd))
    a_bad, th_bad, X_bad, f_bad, _ = tables[jbad]
    x_bad = float(grid[jmid])
    mp.mp.dps = 50
    re_ref = mp.mpf(0.5 * a_bad)
    im_ref = mp.mpf(a_bad) * (mp.mpf(th_bad)
                              - 2 * mp.mpf(math.pi) * mp.mpf(x_bad))
    acc = mp.mpc(0)
    for p_idx in range(X_bad.shape[0]):
        acc += (mp.mpf(f_bad[p_idx])
                * mp.exp((re_ref + 1j * im_ref) * mp.mpf(X_bad[p_idx])))
    v_ref = mp.mpf(a_bad) * acc
    diag["v_ref_worst_family"] = str(v_ref)
    diag["rel_v_mine_vs_ref"] = str(abs(vm[jbad] - complex(v_ref))
                                   / abs(complex(v_ref)))
    diag["rel_v_plain_vs_ref"] = str(
        abs(vp[jbad, jmid] - complex(v_ref)) / abs(complex(v_ref)))
    diag["abs_v_worst"] = float(abs(vp[jbad, jmid]))
    diag["rel_lb_diff_mid"] = float(
        np.abs((lre[jmid] + 1j * lim[jmid]) - lbp[jmid]) / np.abs(lbp[jmid]))
    diag["rel_lc_diff_mid"] = float(
        np.abs((cre[jmid] + 1j * cim[jmid]) - lcp[jmid]) / np.abs(lcp[jmid]))
    diag["abs_kern_diff_max"] = float(np.max(np.abs(kern - kp)))
    diag["rel_p_diff_mid"] = float(
        np.abs(p[jmid] - pp[jmid]) / np.abs(pp[jmid]))
    # channels: |Q| in [margin_lo, margin_hi] = [-q_hi, -q_lo]; the
    # certified standing uses the smallest |Q| in the enclosure.
    margin_lo = -q_hi
    margin_hi = -q_lo
    diag["margin_lo_certified"] = margin_lo
    diag["margin_hi_certified"] = margin_hi
    q_ledger = {
        "tail_2248": 4894093747.764274,
        "known_error_2109": 74601530.30234718,
        "ratio_uncond": 26.0 / 62.0,
        "ratio_import": 21.0 / 62.0,
    }
    for key, ratio in (("uncond", q_ledger["ratio_uncond"]),
                       ("import", q_ledger["ratio_import"])):
        total = q_ledger["tail_2248"] * ratio + q_ledger["known_error_2109"]
        reading = total / margin_lo
        diag["charge_%s" % key] = total
        diag["reading_%s" % key] = reading
        diag["slack_%s" % key] = 1.0 - reading
        diag["eps0_%s" % key] = margin_lo - total

    print(json.dumps(diag, indent=2), flush=True)
    if MODE != "smoke":
        out = {
            "record": 2249,
            "status": "L1-DISCRETE-ENCLOSURE",
            "object": ("q_disc = sum w_i G(x_i) on the 4001-point grid; "
                       "all stored operands exact (convention A, record 2230); "
                       "first-order forward-error shadow, U=2^-52 per op, "
                       "64*2^-53 per pairwise reduction, final 1e-6 inflation"),
            "diagnostics": diag,
            "nonclaims": [
                "encloses the discrete-defined functional only; the "
                "ideal-to-discrete gaps (GL phi quadrature choice, numerical "
                "owner list, [−40,40] window vs integral) remain registered",
                "the coefficient channel (float solve vs exact solve of the "
                "stored matrix) is NOT charged: the stored floats define the "
                "object",
                "screening-grade no producer GO, no gate sign change, no RH claim",
            ],
            "provenance": {
                "script": os.fspath(Path(__file__).relative_to(ROOT)),
                "candidate": {"gamma": GAMMA, "delta": DELTA, "scale": SCALE,
                              "K": K, "m": M, "step": STEP, "window": [-XMAX, XMAX]},
                "anchor_2103": -1675397327895.099,
            },
        }
        target = ROOT / "results" / "2249_l1_enclosure.json"
        with target.open("w", encoding="utf-8", newline="\n") as handle:
            json.dump(out, handle, indent=2)
            handle.write("\n")
        print("written", target, flush=True)


if __name__ == "__main__":
    main()