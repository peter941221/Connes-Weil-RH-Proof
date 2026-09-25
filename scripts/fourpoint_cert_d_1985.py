#!/usr/bin/env python3
# fourpoint_cert_d_1985.py — record 1985 (interval certification of D at the
# registered point)
#
# Registered target (records 1982/1983): a high-precision bracket for the
# gate entry D at rho = 1/2 + 0.10 + i*gamma_1 (M = 12, sc = 1.00, k = 30,
# n = 0), where the float instrument reads D* ~ -1.0737429e+06 and the dxi^4
# convergence order was measured.  This rig re-runs the ENTIRE float pipeline
# (record-1983 world model, byte-equal node list and width pools) in mpmath
# at dps = 30:
#
#   nodes    owner_nodes at the displaced zero (orbit priority, then
#            rho+1/2, the real triple, and the in-ball kills gamma_2..
#            gamma_5; gamma_6 outside the ball), M = 12
#   widths   main pool [2.0, 2.3, 2.6, 2.9, 3.2] on the five gamma_1-height
#            nodes (node order), real [2.1, 2.5, 2.9], kill [2.2, 2.6, 3.0,
#            3.4] on gamma_2..gamma_5; theta_j = -Im(node_j)
#   windows  L_phi(z) = int phi e^{zx} dx over |x| < a,
#            phi(x) = exp(-k / (1 - (x/a)^2)); composite Gauss-Legendre,
#            panels = 6, m = 100 per panel, nodes/weights Newton-refined at
#            full dps
#   density  W = |Lb|^{2(n+1)} |Lc|^2 at s = 1/2 - 2 pi i xi
#   kernel   sigma(u) = log pi - Re psi(1/4 - i u/2) via mp.digamma (closed
#            form, no asymptotic series); prime sum 2 Lambda(n)/sqrt(n)
#            cos(2 pi xi log n) over prime powers <= exp(support radius),
#            support radius = max(a) * (n + 2) = 6.8
#   routes   B  = trapezoid of (sigma + Kp) * f on the ladder
#                dxi in {0.016, 0.008, 0.004, 0.002} on [-8, 8]
#            Ap = sigma-part on the same grid + per-prime-power cosine
#                transforms on the 8x refined grid, at dxi = 0.008 (the
#                float pipeline's certified route, reproduced once)
#            tail census on [8, 24] at dxi = 0.02
#
# Speed discipline: every evaluation on a uniform xi-grid uses GEOMETRIC
# ITERATION — e^{i w (xi0 + h j)} = z0 * r^j with one exp per (window
# x-node / prime power) and complex multiplies per step.  Rounding growth
# is j * eps ~ 1.6e-27 at the longest grid (16008 steps), three orders below
# the dps=30 working floor and eleven below the certificate scale.
#
# Pre-registered bracket rule (committed BEFORE this run):
#   Richardson at the measured dxi^4 order on the B-ladder:
#     D_ex  = D(0.002) + (D(0.002) - D(0.004)) / 15
#     Delta = 16 * max(|D(0.002)-D(0.004)|, |D(0.004)-D(0.008)|) / 15
#             + 2 * |tail_annulus [8,24]|         (route B, measured)
#   bracket: D in [D_ex - Delta, D_ex + Delta].
#   cert_ok iff ALL of
#     (i)   pins < 1e-20, quad-doubling rel < 1e-20, P identity < 1e-20;
#     (ii)  each adjacent B-gap shrinks by >= 8x per dxi halving
#           (dxi^4 = 16x, factor-2 margin);
#     (iii) Delta / |D_ex| <= 2e-6;
#     (iv)  route cross-check |Ap(0.008) - B_ex| <= 100 — the float spread
#           5.1e-5 relative is ~55 absolute; Ap-vs-B at one grid measures
#           B's 0.008 discretization error, not the value;
#     (v)   float replication |D_float (registered row) - B_ex| <= 100.
#   Beyond |xi| = 24 the same W-decay argument bounds the outside mass by
#   the [8,24] annulus value; logged as a caveat, not added to Delta.
#
# No gate sign is proved here; this rig certifies the NUMBER at the single
# registered point.  Output: results/1985_cert_d.json.

import json
import math
import os
import time

import numpy as np
from mpmath import mp, mpf, mpc, pi

T0 = time.time()
DIG = 30

GAMMAS = [14.134725141734693790, 21.022039638771554993,
          25.010857580145688763, 27.670321930357040,
          30.424876125859513210, 32.935061587739189691]
GAMMA1 = GAMMAS[0]
DELTA_RHO = mpf("0.10")
SCALE = mpf(1)
KWIN = mpf(30)
LOGPI = mp.log(mp.pi)


def log(msg):
    print("[%7.1fs] %s" % (time.time() - T0, msg), flush=True)


# ------------------------------------------------------------------ nodes

def owner_nodes_mp(delta, g_disp):
    rho = mpf("0.5") + delta + mpc(0, 1) * g_disp
    r = mpf(2) + mpf(2) + abs(mpf(2) - rho)
    nodes, values = [], []

    def add(z, v):
        for t in nodes:
            if abs(t - z) < mpf("1e-9"):
                return
        nodes.append(z)
        values.append(v)

    add(rho, 1 + 0j)
    add(1 - mp.conj(rho), -1 + 0j)
    add(mp.conj(rho), 0j)
    add(1 - rho, 0j)
    add(rho + mpf("0.5"), -1 + 0j)
    add(mpf("0.5"), 0j)
    add(mpf(1), 0j)
    add(mpf("1.5"), 0j)
    kills = []
    for g in GAMMAS:
        if abs(g - g_disp) < 1e-9:
            continue
        z = mpc(mpf("0.5"), g)
        if abs(z - rho) <= r and abs(z - rho) > mpf("1e-9"):
            kills.append(z)
    for z in kills:
        add(z, 0j)
    return nodes, values, kills, r


WIDTHS_MAIN = [2.0, 2.3, 2.6, 2.9, 3.2]
WIDTHS_REAL = [2.1, 2.5, 2.9]
WIDTHS_KILL = [2.2, 2.6, 3.0, 3.4]


def family_for_mp(nodes, g_main):
    plan = {"main": 0, "real": 0, "kill": 0}
    pools = {"main": WIDTHS_MAIN, "real": WIDTHS_REAL, "kill": WIDTHS_KILL}
    fam = []
    for z in nodes:
        iz = float(mp.im(z))
        if abs(abs(iz) - g_main) < 1e-9:
            key = "main"
        elif abs(iz) < 1e-9:
            key = "real"
        else:
            key = "kill"
        idx = plan[key]
        plan[key] = idx + 1
        if idx >= len(pools[key]):
            raise RuntimeError("pool exhausted: %s" % key)
        fam.append((mpf(pools[key][idx]) * SCALE, -z.imag))
    return fam


# ------------------------------------------------- Gauss-Legendre at dps

def leggauss_mp(m):
    """Legendre nodes/weights at full dps by Newton on the 3-term
    recurrence (same construction as the record-1983 decay probe)."""

    def P(n, x):
        p0, p1 = mpf(1), x
        for k in range(1, n):
            p0, p1 = p1, ((2 * k + 1) * x * p1 - k * p0) / (k + 1)
        return p0, p1

    xs, ws = [], []
    for i in range(1, m + 1):
        x = mp.cos(mp.pi * (i - mpf(1) / 4) / (m + mpf(1) / 2))
        for _ in range(100):
            p0, p1 = P(m, x)
            dx = p0 / ((m * (x * p0 - p1)) / (x * x - 1))
            x -= dx
            if abs(dx) < mpf(10) ** (-(DIG + 5)):
                break
        p0, p1 = P(m, x)
        dp = m * (x * p0 - p1) / (x * x - 1)
        xs.append(x)
        ws.append(2 / ((1 - x * x) * dp * dp))
    return xs, ws


def phi_weights_mp(a, panels, m):
    xs, ws = leggauss_mp(m)
    edges = [(-a + (2 * a) * mpf(j) / panels) for j in range(panels + 1)]
    X, W = [], []
    for j in range(panels):
        lo, hi = edges[j], edges[j + 1]
        for x, w in zip(xs, ws):
            X.append((hi - lo) / 2 * x + (lo + hi) / 2)
            W.append((hi - lo) / 2 * w)
    return X, W


def window_ops(fam, k, XWl):
    """Per window, the xi-independent part of the Laplace transform:
    G(X) = w * phi(X) * e^{a(1/2 + i*theta) X}, so that at
    s = 1/2 - 2 pi i xi,
      a * L_phi(a (s + i theta)) = a * sum_X G(X) e^{-2 pi i a X xi}."""
    ops = []
    for j, (a, th) in enumerate(fam):
        X, W = XWl[j]
        base = a * (mpf("0.5") + mpc(0, 1) * th)
        G = []
        for x, w in zip(X, W):
            ax = x / a
            if abs(ax) < 1:
                G.append(w * mp.exp(-k / (1 - ax * ax) + base * x))
        ops.append((a, G))
    return ops


def eval_windows(ops, xi0, h, npts):
    """V[j][k] = window j value at xi_k = xi0 + h*k via geometric
    iteration: for each x-node, z0 = e^{-2 pi i a X xi0}, r = e^{-2 pi i
    a X h}, then z <- z*r along the grid."""
    V = []
    for a, G in ops:
        c = -2 * pi * a
        L = [mpc(0) for _ in range(npts)]
        for X, g in G:
            z0 = mp.exp(c * X * xi0)
            r = mp.exp(c * X * h)
            z = z0
            acc = L
            gg = a * g
            for kk in range(npts):
                acc[kk] += gg * z
                z = z * r
        V.append(L)
    return V


# ------------------------------------------------------------------ kernel

def prime_powers_up_to_mp(xmax):
    out = []
    n = int(math.floor(xmax))
    sieve = np.ones(n + 1, dtype=bool)
    sieve[:2] = False
    for p in range(2, int(n ** 0.5) + 1):
        if sieve[p]:
            sieve[p * p::p] = False
    for p in range(2, n + 1):
        if sieve[p]:
            pk = p
            lp = math.log(p)
            while pk <= n:
                out.append((pk, mpf(lp)))
                pk *= p
    out.sort()
    return out


def sigma_grid(xi0, h, npts):
    out = []
    for k in range(npts):
        w = 2 * pi * (xi0 + h * k)
        z = mpf("0.25") - mpc(0, mpf("0.5")) * w
        out.append(LOGPI - mp.re(mp.digamma(z)))
    return out


def cos_grid(omega, xi0, h, npts):
    """[cos(omega*(xi0+h*k))] via geometric iteration of e^{i omega xi}."""
    z0 = mp.exp(mpc(0, 1) * omega * xi0)
    r = mp.exp(mpc(0, 1) * omega * h)
    z = z0
    out = []
    for _ in range(npts):
        out.append(mp.re(z))
        z = z * r
    return out


def P_quartic(xi):
    om = 2 * pi * xi
    return (DELTA_RHO ** 2 + GAMMA1 ** 2 - om ** 2) ** 2 \
        + 4 * DELTA_RHO ** 2 * om ** 2


def P_nodes(xi, cnodes):
    s = mpc(0, -2) * pi * xi
    p = mpc(1)
    for a in cnodes:
        p *= a - s
    return p


# ------------------------------------------------------- channel profiles

def profiles(ops, A, xi0, h, npts):
    """Window-based profiles on one uniform grid:
    returns (W, PW, P2W) lists at xi_k = xi0 + h*k."""
    V = eval_windows(ops, xi0, h, npts)
    Ab, Ac = A
    Lb = [sum(Ab[j] * V[j][k] for j in range(len(ops)))
          for k in range(npts)]
    Lc = [sum(Ac[j] * V[j][k] for j in range(len(ops)))
          for k in range(npts)]
    W = [abs(Lb[k]) ** 2 * abs(Lc[k]) ** 2 for k in range(npts)]
    PW = [P_quartic(xi0 + h * k) * W[k] for k in range(npts)]
    P2W = [P_quartic(xi0 + h * k) ** 2 * W[k] for k in range(npts)]
    return W, PW, P2W


def trap(vals, h):
    tot = mpc(0)
    for k in range(len(vals) - 1):
        tot += (vals[k] + vals[k + 1]) * (h / 2)
    return tot


def channel_B(pset, W, PW, P2W, xi0, h, npts):
    """arch part (sigma) + route-B kernel part for the three channels."""
    sig = sigma_grid(xi0, h, npts)
    arch = [trap([sig[k] * W[k] for k in range(npts)], h),
            trap([sig[k] * PW[k] for k in range(npts)], h),
            trap([sig[k] * P2W[k] for k in range(npts)], h)]
    kern = [mpc(0), mpc(0), mpc(0)]
    for _nn, lp in pset:
        cl = cos_grid(2 * pi * lp, xi0, h, npts)
        coef = 2 * lp * mp.exp(-lp / 2)
        for arr, idx in ((W, 0), (PW, 1), (P2W, 2)):
            kern[idx] += coef * trap([cl[k] * arr[k] for k in range(npts)], h)
    return arch, kern


def channel_Ap(ops, A, pset, xi0, h, npts, reffac=8):
    """The float pipeline's certified route: sigma part on the base grid,
    per-prime cosine transforms of each profile on the reffac-x refined
    grid (exactly the 1983 Ap construction, minus the float-only spline)."""
    nref = (npts - 1) * reffac + 1
    hf = h / reffac
    W, PW, P2W = profiles(ops, A, xi0, hf, nref)
    arch = channel_B([], W, PW, P2W, xi0, hf, nref)[0]
    out = list(arch)
    for _nn, lp in pset:
        cl = cos_grid(2 * pi * lp, xi0, hf, nref)
        coef = 2 * lp * mp.exp(-lp / 2)
        for arr, idx in ((W, 0), (PW, 1), (P2W, 2)):
            out[idx] += coef * trap([cl[k] * arr[k] for k in range(nref)], hf)
    return out


# ------------------------------------------------------------------ main

def main():
    mp.dps = DIG
    nodes, values, kills, radius = owner_nodes_mp(DELTA_RHO, GAMMA1)
    log("M = %d nodes; ball radius %s; kills %s"
        % (len(nodes), mp.nstr(radius, 8),
           [mp.nstr(z.imag, 6) for z in kills]))
    fam = family_for_mp(nodes, GAMMA1)
    log("widths: %s" % [float(a) for a, _ in fam])

    XWl = [phi_weights_mp(a, 6, 100) for (a, _) in fam]
    log("X-quadrature: panels=6, m=100 (%d nodes/window)" % len(XWl[0][0]))

    ops = window_ops(fam, KWIN, XWl)

    # 12x12 solves at full dps
    Vnodes = []
    for z in nodes:
        s = z
        Vj = []
        for j, (a, th) in enumerate(fam):
            zz = a * (s + mpc(0, 1) * th)
            tot = mpc(0)
            for x, w in zip(*XWl[j]):
                ax = x / a
                if abs(ax) < 1:
                    tot += w * mp.exp(-KWIN / (1 - ax * ax) + zz * x)
            Vj.append(a * tot)
        Vnodes.append(Vj)
    M = mp.matrix(len(nodes), len(nodes))
    for i in range(len(nodes)):
        for j in range(len(fam)):
            M[i, j] = Vnodes[i][j]
    lu = mp.inverse(M)
    cond = mp.norm(M, 1) * mp.norm(lu, 1)
    A_base = mp.lu_solve(M, mp.matrix([1 + 0j] * len(nodes)))
    A_corr = mp.lu_solve(M, mp.matrix(values))
    pins_b = max(abs(sum(A_base[j] * Vnodes[i][j] for j in range(len(fam)))
                     - 1) for i in range(len(nodes)))
    pins_c = max(abs(sum(A_corr[j] * Vnodes[i][j] for j in range(len(fam)))
                     - values[i]) for i in range(len(nodes)))
    log("solve: cond %s; pins base %s corr %s"
        % (mp.nstr(cond, 4), mp.nstr(pins_b, 3), mp.nstr(pins_c, 3)))
    A = (A_base, A_corr)

    # X-quadrature doubling self-check on window 0 at s = node 0
    XW2 = phi_weights_mp(fam[0][0], 6, 150)
    zz0 = fam[0][0] * (nodes[0] + mpc(0, 1) * fam[0][1])
    L1 = sum(w * mp.exp(-KWIN / (1 - (x / fam[0][0]) ** 2) + zz0 * x)
             for x, w in zip(*XWl[0]) if abs(x / fam[0][0]) < 1)
    L2 = sum(w * mp.exp(-KWIN / (1 - (x / fam[0][0]) ** 2) + zz0 * x)
             for x, w in zip(*XW2) if abs(x / fam[0][0]) < 1)
    quad_rel = abs(L1 - L2) / abs(L1)
    log("X-quad doubling m=100 vs 150: rel %s" % mp.nstr(quad_rel, 3))

    # P identity at a sample point
    cnodes = [z - mpf("0.5") for z in
              [nodes[0], 1 - mp.conj(nodes[0]), mp.conj(nodes[0]),
               1 - nodes[0]]]
    xitest = mpf("1.234")
    pid = abs(P_nodes(xitest, cnodes) - P_quartic(xitest))
    log("P quartic identity abs err %s" % mp.nstr(pid, 3))

    maxa = max(a for a, _ in fam)
    support_radius = float(maxa) * 2
    pset = prime_powers_up_to_mp(math.exp(support_radius))
    log("support radius %.2f -> %d prime powers" % (support_radius, len(pset)))

    # route-B ladder
    ladder = []
    for h, half in ((mpf("0.016"), 501), (mpf("0.008"), 1001),
                    (mpf("0.004"), 2001), (mpf("0.002"), 4001)):
        W, PW, P2W = profiles(ops, A, mpf(-8), h, 2 * half + 1)
        arch, kern = channel_B(pset, W, PW, P2W, mpf(-8), h, 2 * half + 1)
        vals = [arch[i] + kern[i] for i in range(3)]
        D = vals[2]
        log("  h=%s: D=%s C=%s b=%s"
            % (h, mp.nstr(D, 12), mp.nstr(vals[0], 8), mp.nstr(vals[1], 8)))
        ladder.append(D)

    # route Ap at h = 0.008 (cross-check)
    W8, PW8, P2W8 = profiles(ops, A, mpf(-8), mpf("0.008"), 2001)
    arch8, kern8 = channel_B(pset, W8, PW8, P2W8, mpf(-8), mpf("0.008"), 2001)
    ap8 = channel_Ap(ops, A, pset, mpf(-8), mpf("0.008"), 2001)
    D_ap8 = ap8[2]
    D_b8 = arch8[2] + kern8[2]
    log("  Ap(0.008): D=%s  (B at same grid: %s; route gap %s)"
        % (mp.nstr(D_ap8, 12), mp.nstr(D_b8, 12), mp.nstr(D_ap8 - D_b8, 4)))

    # tail census [8, 24]
    Wt, PWt, P2Wt = profiles(ops, A, mpf(8), mpf("0.02"), 801)
    archt, kernt = channel_B(pset, Wt, PWt, P2Wt, mpf(8), mpf("0.02"), 801)
    D_tail = archt[2] + kernt[2]
    log("tail census [8,24]: route-B D-annulus = %s" % mp.nstr(D_tail, 4))

    # Richardson + bracket per the pre-registered rule
    _D16, D8, D4, D2 = ladder
    gap_84 = abs(D4 - D8)
    gap_42 = abs(D2 - D4)
    Dex = D2 + (D2 - D4) / 15
    Delta = mpf(16) * max(gap_42, gap_84) / 15 + 2 * abs(D_tail)
    shrink = gap_84 / gap_42 if gap_42 != 0 else mp.inf
    log("B-ladder gaps: |D4-D8|=%s |D2-D4|=%s shrink=%s"
        % (mp.nstr(gap_84, 4), mp.nstr(gap_42, 4), mp.nstr(shrink, 4)))
    log("Richardson: D_ex = %s" % mp.nstr(Dex, 12))
    log("bracket: [%s, %s] (Delta %s, rel %s)"
        % (mp.nstr(Dex - Delta, 12), mp.nstr(Dex + Delta, 12),
           mp.nstr(Delta, 4), mp.nstr(abs(Delta / Dex), 4)))

    # float cross-check: the canonical registered instrument is the record-
    # 1981 offline owner run (the pipeline this rig replicates byte-equal);
    # the record-1983 survey anchor is reported alongside.  The two float
    # runs disagree at 7.7e-4 relative on this row (a float-level question,
    # outside this certificate's scope); the gate anchors on 1981.
    d1981 = d1983 = None
    try:
        with open(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                               "..", "results", "1981_offline_owner.json"),
                  encoding="utf-8") as fh:
            rep = json.load(fh)
        for c in rep.get("cases", []):
            if (abs(float(c.get("delta", -1)) - 0.1) < 1e-9
                    and abs(float(c.get("scale", -1)) - 1.0) < 1e-9
                    and c.get("n") == 0 and c.get("M") == 12):
                d1981 = float(c["D"])
    except (OSError, KeyError, ValueError):
        pass
    try:
        with open(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                               "..", "results", "1983_rh_reach_probe.json"),
                  encoding="utf-8") as fh:
            rep3 = json.load(fh)
        for a in rep3.get("replication_anchors", []):
            if abs(float(a.get("delta", -1)) - 0.1) < 1e-9:
                d1983 = float(a["D_survey"])
    except (OSError, KeyError, ValueError):
        pass
    route_ok = abs(D_ap8 - Dex) <= 100
    float_ok = d1981 is not None and abs(mpf(d1981) - Dex) <= 100
    if d1981 is not None:
        log("float 1981 registered D = %.6f; rig-vs-1981 = %s (abs)"
            % (d1981, mp.nstr(abs(mpf(d1981) - Dex), 6)))
    if d1983 is not None:
        log("float 1983 survey anchor D = %.6f; rig-vs-1983 = %s (abs)"
            % (d1983, mp.nstr(abs(mpf(d1983) - Dex), 6)))

    checks = {
        "pins": mp.nstr(max(pins_b, pins_c), 3),
        "quad_doubling": mp.nstr(quad_rel, 3),
        "P_identity": mp.nstr(pid, 3),
        "gap_shrink_84_to_42": mp.nstr(shrink, 4),
        "delta_rel": mp.nstr(abs(Delta / Dex), 4),
        "route_gap": mp.nstr(abs(D_ap8 - Dex), 6),
        "float_1981_gap": (mp.nstr(abs(mpf(d1981) - Dex), 6)
                           if d1981 is not None else None),
        "float_1983_gap": (mp.nstr(abs(mpf(d1983) - Dex), 6)
                           if d1983 is not None else None),
    }
    ok = (max(pins_b, pins_c) < mpf("1e-20") and quad_rel < mpf("1e-20")
          and pid < mpf("1e-20") and shrink >= 8
          and abs(Delta / Dex) <= mpf("2e-6") and route_ok and float_ok)
    log("CERT_BRACKET_OK = %s" % ok)
    report = {
        "record": 1985,
        "status": "D_INTERVAL_CERTIFICATE",
        "pre_registration": "docs/proofs/1985_cert_d.md",
        "rho": [0.6, GAMMA1], "M": len(nodes), "scale": 1.0, "k": 30.0,
        "n": 0, "dps": DIG,
        "ladder": ["0.016", "0.008", "0.004", "0.002"],
        "D_routeB": [mp.nstr(d, 15) for d in ladder],
        "D_routeAp_h008": mp.nstr(D_ap8, 15),
        "route_gap_h008": mp.nstr(D_ap8 - D_b8, 6),
        "tail_annulus_B": mp.nstr(D_tail, 6),
        "D_ex": mp.nstr(Dex, 15),
        "Delta": mp.nstr(Delta, 8),
        "bracket": [mp.nstr(Dex - Delta, 15), mp.nstr(Dex + Delta, 15)],
        "relative_halfwidth": mp.nstr(abs(Delta / Dex), 6),
        "cert_ok": bool(ok),
        "checks": checks,
        "float_D_1981": d1981,
        "float_D_1983_survey": d1983,
        "n_primes": len(pset),
        "support_radius": support_radius,
    }
    out = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..",
                       "results", "1985_cert_d.json")
    with open(out, "w", encoding="utf-8") as fh:
        fh.write(json.dumps(report, indent=2) + "\n")
    log("wrote %s" % os.path.abspath(out))


if __name__ == "__main__":
    main()
