"""2055 - Route A link L2: the second method batch on the reduced evaluator.

OBJECT (same as 2054): the committed 2037-class float pipeline with the phi
rule at m = 1600 (one-copy G8-H, window [-40, 40], stored floats exact),
priced by the panel-local model architecture (records 2048/2051/2052/2054).

TWO METHODS CHANGE (both rigorous, both gated):

  (A) THE SIGMA CHANNEL.  2048 A1 (kept by 2054) priced int sigma*g by the
      direct interval method at 0.05 panels, zeroth order:
          arch_proj = sum_i w_sigma(panel_i) * g_mid_i * 0.05,
      with w_sigma = ordinary interval width of r43.sigma_arch_iv over the
      panel (~ |sigma'| dxi: refinement-proof, 9.287269e+11 at m = 1600).
      Here the SAME object int_window sigma*g is enclosed by a THIRD-ORDER
      Taylor model per panel:
          int_panel sigma*g = sigma(m) G0 + sigma'(m) G1
                            + (1/2) sigma''(m) G2 + R3,
          |R3| <= (1/6) sup_panel|sigma'''| r^3 int_panel |g|,  r = dxi/2,
      G_k = int (x-m)^k g  (trapezoid on the fine grid, error charged
      (dxi^2/12) * enclosed int |g^(j)|), sigma^(k)(m) enclosed by the
      termwise-differentiated Bernoulli ladder + elementary tail charges;
      sup|sigma'''| over the panel likewise.  The enclosure is one-sided:
      the reported quantity is the deviation bound, matching the A1
      convention it replaces.

  (B) THE AGGREGATE LADDER extended downward by two rungs, h = 0.0005 and
      h = 0.00025 (the 2054 endpoint step ratio 4.06 sits on the h^2 law
      of the hump panels' trap-difference charge; the rung machinery is
      h-parametric and the nodes land on the fine grid).

SIGMA DERIVATIVE MACHINERY (the element; validated in-run by A7/A8):
    sigma(u) = log pi - Re psi(1/4 - i u/2),  w = z + 8, z = 1/4 - i u/2
    psi(z)   = psi(z+8) - sum_{j<8} 1/(z+j)          [exact shift identity]
    psi(w)   = log w - 1/(2w) - sum_{n<=6} B_2n/(2n w^2n) + T0
    psi'(w)  = 1/w + 1/(2w^2) + sum B_2n w^{-2n-1} + T1
    psi''(w) = -1/w^2 - 1/w^3 - sum (2n+1) B_2n w^{-2n-2} + T2
    psi'''(w)= 2/w^3 + 3/w^4 + sum (2n+1)(2n+2) B_2n w^{-2n-3} + T3
  Tail charges from the exact Gauss representation
    psi(w) = log w - 1/(2w) - 2 int_0^inf t/((w^2+t^2)(e^{2 pi t}-1)) dt
  expanded to n = 6 (residual factor t^12/(w^12 (w^2+t^2))):
    |T0(w)| <= 2 M13 / (|w|^12 Dmin(w)),  Dmin = x^2+y^2 if |y|<=x else 2x|y|
    M13 = int_0^inf t^13/(e^{2 pi t}-1) dt = |B_14|/28 = 1/24
  and, on the disk |w - w0| = rho = x/2 (Re w >= x/2 > 0 on it):
    sup_disk|T0| <= 2 M13 / (R_lo^12 Dmin_lo),
    |T1| <= sup/rho, |T2| <= 2 sup/rho^2, |T3| <= 6 sup/rho^3
  (Cauchy).  Chain to u:  d sigma/du = -(1/2) Im psi'(z);
    d^2 sigma/du^2 = (1/4) Re psi''(z);  d^3 sigma/du^3 = (1/8) Im psi'''(z);
    d^k/dxi^k = (2 pi)^k d^k/du^k.  SAFE = 8 multiplies every tail charge
  (pointwise validation against mpmath polygamma at dps 45 peaked at
  diff/charge = 0.93 on the least-convergent sample, u = 0, pre-SAFE;
  the factor is margin, not part of the derivation).

FROZEN VERDICT RULES
    total := min over the six rungs of min(charge_L3, charge_agg)
             + charge_L1 at the best rung + arch3
    arch3 := sum_i [ w_h(sigma)|T0| + (|sig_c|+w_h) e0
                   + h1 |T1| + (|c1|+h1) e1
                   + 0.5 ( h2 |T2| + (|c2|+h2) e2 )
                   + (1/6) S3 r^3 (I + e0) ]                    [one-sided]
    REDUCED-L2-VIABLE : all gates pass AND total <  BAR10
    REDUCED-L2-GRAY   : all gates pass AND BAR10 <= total < BUDGET3
    REDUCED-L2-FAIL   : all gates pass AND total >= BUDGET3
    ANCHOR-FAIL       : any gate misses
  BAR10 = BUDGET3/10 = 3.40604987188126656e+11, BUDGET3 = |Q_1600| (2053).

GATES (frozen)
  P1 arch-old reproduction (2048 A1 convention) vs 9.287269e+11 rel<=1e-9
  P2 rung h=0.001 fields reproduce the 2054 artifact rel<=1e-9
     (charge_L3 1.6335326709264424e+12, charge_agg 7.564715032348474e+11,
      agg_main 6.675343405960566e+11, agg_theta 7.809777817367694e+10,
      agg_corr 1.0839384465113783e+10)
  P3 L1 at h=0.001 reproduces 1.3078036401976297e+07 rel<=1e-9
  C1 Q400 / C2 Q1600 (2053 anchors, rel<=1e-6, sign<0); C3 setup constants;
  C4 span equivalence 0; C5 m=400 vs 2051 (rel<=1e-9); C6 arch width_mean
  vs 569.087 (tol 2%); A1 pipeline a1_abs_max <= 1e-9 gmax at all six rungs;
  A2a zero violations at all six rungs; A2b booked gap charge <= 1e9 at all
  six rungs; A3 iv containment (r51); A6 jet selftest (r51); B5 forward
  selftest (r52); A7 sigma-derivative containment vs mpmath polygamma dps
  45 at 17 u-points x 4 orders, worst ratio < 1; A8 committed
  r43.sigma_arch_iv contains the same mp digamma references at those points;
  A9 charge_L3 and charge_agg strictly decreasing over the six rungs;
  A10 (a) per-panel Taylor-3 mp references (mp sigma derivatives at dps 45
  times the same float moments) inside the panel enclosure W_i at 9 sampled
  panels, worst dev/W < 1; (b) the same reference summed over the whole
  window inside [C +/- arch3]; B1 containment 7/7; B3 ladder-vs-fine
  bitwise 0.0 at both new rungs; B4 all charges finite and non-negative.

MACHINERY NOTE (new rungs): run_rung's stencil slices read gpp up to index
2 n_pan + 1; the fine-grid stencil at dxi has one trailing edge copy, so
the probe passes gpp with two additional trailing copies (the same edge
convention fine_grid itself uses).  For h >= 0.001 the slices never reach
the pad; bitwise identity with 2054 is gated by P2.

CLI: --smoke | --workers N | --chunk N | --selftest
"""

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
import routea_l1_nodal_enclosure_2052 as r52   # noqa: E402
import routea_l3_aggregate_2051 as r51         # noqa: E402
import routea_reduced_evaluator_2054 as r54    # noqa: E402

mp.iv.dps = 20

XI_MAX = 40.0
M_RED = 1600
PANELS = 6
DXI_G = 0.00025
H_LADDER6 = (0.01, 0.005, 0.002, 0.001, 0.0005, 0.00025)
H_OLD_BEST = 0.001

# frozen 2053 window values
Q400_FROZEN = -1.1111757839943646e+20
Q1600_FROZEN = -3406049871881.2666
BUDGET3 = abs(Q1600_FROZEN)
BAR10 = 0.1 * BUDGET3

# frozen 2054 artifact fields (P1/P2/P3)
ARCH_2054_1600 = 928726947225.5668
WIDTH_MEAN_2054 = 569.0867771360982
AGG_2054_001 = 756471503234.8474
L3_2054_001 = 1633532670926.4424
AGGMAIN_2054_001 = 667534340596.0566
AGGTHETA_2054_001 = 78097778173.67694
AGGCORR_2054_001 = 10839384465.113783
L1_2054_001 = 13078036.401976297

# frozen 2051 m = 400 charges at h = 0.002 (C5)
L3_2051_0P002 = 5.657706991143483e+18
AGG_2051_0P002 = 2.7512365454404613e+18
C_BOOK_2051 = 458.0475860314685
C1_BOOK_2051 = 21898.85724574201
SUPPORT_2051 = 9.504
BOOK_2051 = 1647
NFAM_2051 = 17

ARCH_ANCHOR_DXI = 0.05
ANCHOR_WIDTH_MEAN_2043 = 569.087
ANCHOR_WIDTH_TOL = 0.02

TOL_P = 1e-9
TOL_C1C2 = 1e-6
TOL_C3 = 1e-9
TOL_C4 = 1e-12
TOL_C5 = 1e-9
GAP_MAX = 1e9

SAFE = 8.0
U_DELTA = 0.001               # arch moment-error grid spacing (xi-units)
N_PAN_ARCH = int(round(2 * XI_MAX / ARCH_ANCHOR_DXI))       # 1600
SMOKE_LO, SMOKE_HI = 780, 821  # smoke panel window around xi ~ 0
PICK_PANELS = (0, 199, 400, 639, 666, 699, 800, 1199, 1599)
U_PICKS = [0.0] + [s * m * 2.0 * math.pi
                   for m in (1.0, 0.493, 6.68, 7.03, 20.0, 34.97, 39.747)
                   for s in (1.0, -1.0)]

BERN_FULL_IV = [mp.iv.mpf(mp.mpf(1) / 6), mp.iv.mpf(-mp.mpf(1) / 30),
                mp.iv.mpf(mp.mpf(1) / 42), mp.iv.mpf(-mp.mpf(1) / 30),
                mp.iv.mpf(mp.mpf(5) / 66), mp.iv.mpf(-mp.mpf(691) / 2730)]
M13 = mp.mpf(7) / 6 / 28      # = |B_14|/28 = int t^13/(e^2pi t -1) dt
X_ARCH = mp.mpf('8.25')
RHO_DISK = X_ARCH / 2
TWO_PI = float(2 * math.pi)


def _tail_charges(u_f):
    """(t0, t1, t2, t3) * SAFE: absolute tail bounds of T0..T3 at the point
    w = 8.25 - i u_f/2 (u_f: the panel's min-|u| endpoint, in u-units)."""
    y = abs(mp.mpf(repr(float(u_f)))) / 2
    x = X_ARCH
    R = mp.sqrt(x * x + y * y)
    dmin0 = x * x + y * y if y <= x else 2 * x * y
    sup0 = 2 * M13 / (R ** 12 * dmin0)
    r_lo = R - RHO_DISK
    x_lo = x - RHO_DISK
    if y <= RHO_DISK:
        dmin = x_lo * x_lo
    else:
        a_lo = y - RHO_DISK
        dmin = min(x_lo * x_lo + a_lo * a_lo, 2 * x_lo * a_lo)
    sup = 2 * M13 / (r_lo ** 12 * dmin)
    return (SAFE * sup0, SAFE * sup / RHO_DISK,
            SAFE * 2 * sup / RHO_DISK ** 2, SAFE * 6 * sup / RHO_DISK ** 3)


def _cadd(a, b):
    return (a[0] + b[0], a[1] + b[1])


def _cmul(a, b):
    return (a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0])


def _csmul(c, a):
    return (c * a[0], c * a[1])


def _iv_ch(ivv):
    """(centre, half-width) floats of an iv interval."""
    lo = mp.mpf(ivv.a)
    hi = mp.mpf(ivv.b)
    return float((lo + hi) / 2), float((hi - lo) / 2)


def sigma_chain_iv(u_iv, with_sig=True):
    """Sigma and its u-derivatives on the iv interval u_iv (u-units).

    Returns {"sig"?, "s1", "s2", "s3"} -> (centre, half-width) floats; the
    truncation part is interval arithmetic on the termwise-differentiated
    ladder + exact shift sums, each widened by its SAFE tail charge.
    Tail charges evaluated at the interval endpoint of minimal |u|.
    """
    iv = mp.iv
    u_lo = mp.mpf(u_iv.a)
    u_hi = mp.mpf(u_iv.b)
    u_min = u_lo if abs(u_lo) <= abs(u_hi) else u_hi
    t0, t1, t2, t3 = _tail_charges(float(u_min))
    x = iv.mpf(X_ARCH)
    y = u_iv / 2
    y2 = y * y
    m2 = x * x + y2
    t1c = (x / m2, y / m2)                     # 1/w, w = 8.25 - i y (y=u/2)
    t1sq = _cmul(t1c, t1c)
    t1cb = _cmul(t1sq, t1c)
    t1f4 = _cmul(t1cb, t1c)
    half = iv.mpf(mp.mpf(1) / 2)
    p1 = _cadd(_cadd(t1c, _csmul(half, t1sq)), (iv.mpf(0), iv.mpf(0)))
    p2 = _csmul(iv.mpf(-1), _cadd(t1sq, t1cb))
    p3 = _cadd(_csmul(iv.mpf(2), t1cb), _csmul(iv.mpf(3), t1f4))
    two = iv.mpf(2)
    w2r = x * x - y2
    w2i = -two * x * y                         # w^2 for w = x - i y
    pwr, pwi = w2r, w2i                        # w^{2n}
    for n, b in enumerate(BERN_FULL_IV, start=1):
        pw2 = pwr * pwr + pwi * pwi
        q = _cmul((pwr / pw2, -pwi / pw2), t1c)          # w^{-2n-1}
        p1 = _cadd(p1, _csmul(b, q))
        p2 = _cadd(p2, _csmul(-(2 * n + 1) * b, _cmul(q, t1c)))
        p3 = _cadd(p3, _csmul((2 * n + 1) * (2 * n + 2) * b,
                              _cmul(q, t1sq)))
        nre = pwr * w2r - pwi * w2i
        nim = pwr * w2i + pwi * w2r
        pwr, pwi = nre, nim
    j2 = (iv.mpf(0), iv.mpf(0))
    j3 = (iv.mpf(0), iv.mpf(0))
    j4 = (iv.mpf(0), iv.mpf(0))
    q4 = iv.mpf(mp.mpf('0.25'))
    for j in range(8):
        xj = q4 + iv.mpf(j)
        den = xj * xj + y2
        inv = (xj / den, y / den)              # 1/(z+j), z+j = xj - i y
        inv2 = _cmul(inv, inv)
        j2 = _cadd(j2, inv2)
        j3 = _cadd(j3, _csmul(two, _cmul(inv2, inv)))
        j4 = _cadd(j4, _csmul(iv.mpf(6), _cmul(inv2, inv2)))
    ps1 = _cadd(p1, j2)                        # psi'(z)
    ps2 = _cadd(p2, _csmul(iv.mpf(-1), j3))    # psi''(z)
    ps3 = _cadd(p3, j4)                        # psi'''(z)
    s1_iv = -ps1[1] / 2
    s2_iv = ps2[0] / 4
    s3_iv = ps3[1] / 8
    out = {}
    for key, ivv, tw in (("s1", s1_iv, t1 / 2), ("s2", s2_iv, t2 / 4),
                         ("s3", s3_iv, t3 / 8)):
        c, h = _iv_ch(ivv)
        out[key] = (c, h + float(tw))
    if with_sig:
        sig_iv = r43.sigma_arch_iv(u_iv)
        c, h = _iv_ch(sig_iv)
        out["sig"] = (c, h + float(t0))
    return out


def _trap(y, w):
    """Trapezoid of y on a uniform grid of spacing w (manual, documented)."""
    return float(w * (np.sum(y) - 0.5 * (y[0] + y[-1])))


def arch3_charge(g_com, dxi_g, uu1, uu2, u_delta, edges, j_first, ref_picks,
                 tag):
    """The third-order sigma-channel enclosure of int sigma*g over `edges`.

    Panels are ARCH_ANCHOR_DXI wide; `j_first` is the global index of the
    first panel (0 for the full window).  Returns the one-sided deviation
    bound W = sum W_i, the centre C = sum C_i, the bin decomposition, the
    A10a per-panel reference deviations and the A10b full-window reference
    deviation (mpmath sigma derivatives at dps 45 against the same float
    moments).
    """
    mp.mp.dps = 45
    n_use = len(edges) - 1
    step = int(round(ARCH_ANCHOR_DXI / dxi_g))
    u_step = int(round(ARCH_ANCHOR_DXI / u_delta))
    n_u = len(uu1)
    r = ARCH_ANCHOR_DXI / 2
    W = np.zeros(n_use)
    C = np.zeros(n_use)
    s3s = np.zeros(n_use)
    ref_dev = []
    ref_sum = mp.mpf(0)
    for i in range(n_use):
        gidx = j_first + i
        a = float(edges[i])
        b = float(edges[i + 1])
        m = 0.5 * (a + b)
        i0 = gidx * step
        seg = g_com[i0:i0 + step + 1]
        xs = a + dxi_g * np.arange(step + 1)
        t0m = _trap(seg, dxi_g)
        t1m = _trap((xs - m) * seg, dxi_g)
        t2m = _trap((xs - m) ** 2 * seg, dxi_g)
        ia_abs = _trap(np.abs(seg), dxi_g)
        j0 = gidx * u_step
        j1 = min(n_u, (gidx + 1) * u_step + 2)
        lo = max(0, j0 - 1)
        ia2 = float(2 * u_delta * np.sum(uu2[lo:j1]))
        ia1 = float(2 * u_delta * np.sum(uu1[lo:j1]))
        e0 = (dxi_g ** 2 / 12.0) * ia2
        e1 = (dxi_g ** 2 / 12.0) * (r * ia2 + 2.0 * ia1)
        ia0 = ia_abs + e0
        e2 = (dxi_g ** 2 / 12.0) * (r * r * ia2 + 4.0 * r * ia1 + 2.0 * ia0)
        u0 = TWO_PI * m
        chm = sigma_chain_iv(mp.iv.mpf([repr(u0), repr(u0)]))
        sig_c, sig_h = chm["sig"]
        c1 = TWO_PI * chm["s1"][0]
        h1 = TWO_PI * chm["s1"][1]
        c2 = TWO_PI ** 2 * chm["s2"][0]
        h2 = TWO_PI ** 2 * chm["s2"][1]
        ch3 = sigma_chain_iv(mp.iv.mpf([repr(TWO_PI * a),
                                        repr(TWO_PI * b)]), with_sig=False)
        s3 = TWO_PI ** 3 * (abs(ch3["s3"][0]) + ch3["s3"][1])
        wi = (sig_h * abs(t0m) + (abs(sig_c) + sig_h) * e0
              + h1 * abs(t1m) + (abs(c1) + h1) * e1
              + 0.5 * (h2 * abs(t2m) + (abs(c2) + h2) * e2)
              + (1.0 / 6.0) * s3 * r ** 3 * ia0)
        W[i] = wi
        C[i] = sig_c * t0m + c1 * t1m + 0.5 * c2 * t2m
        s3s[i] = s3
        z = mp.mpf('0.25') - 1j * mp.mpf(repr(u0)) / 2
        sr = mp.log(mp.pi) - mp.re(mp.digamma(z))
        s1r = -mp.im(mp.polygamma(1, z)) / 2 * TWO_PI
        s2r = mp.re(mp.polygamma(2, z)) / 4 * TWO_PI ** 2
        ref_i = sr * t0m + s1r * t1m + 0.5 * s2r * t2m
        ref_sum += ref_i
        if gidx in ref_picks:
            ref_dev.append({"panel": gidx, "W": wi,
                            "dev_over_W": float(abs(ref_i - mp.mpf(repr(
                                float(C[i]))))
                                / max(mp.mpf(repr(wi)), mp.mpf('1e-300')))})
    arch3 = float(np.sum(W))
    centre = float(np.sum(C))
    bins = []
    mids = 0.5 * (edges[:-1] + edges[1:])
    for blo, bhi in ((-40, -8), (-8, -5), (-5, -1), (-1, 1), (1, 5),
                     (5, 40)):
        mk = (mids >= blo) & (mids < bhi)
        if not mk.any():
            continue
        bins.append({"lo": blo, "hi": bhi, "W": float(np.sum(W[mk])),
                     "C": float(np.sum(C[mk])),
                     "S3max": float(np.max(s3s[mk]))})
    dev_w = abs(ref_sum - mp.mpf(repr(centre)))
    ref_win = {"dev": float(dev_w),
               "over_W": float(dev_w / max(mp.mpf(repr(arch3)),
                                           mp.mpf('1e-300')))}
    ipk = int(np.argmax(W))
    print("arch3 %s: W %.6e centre %.6e worst panel %d (xi %.3f) W_i "
          "%.4e S3_i %.4e | ref window dev %.4e (over W %.4f)"
          % (tag, arch3, centre, j_first + ipk,
             0.5 * (edges[ipk] + edges[ipk + 1]), W[ipk], s3s[ipk],
             ref_win["dev"], ref_win["over_W"]), flush=True)
    return {"arch3": arch3, "centre": centre, "bins": bins,
            "ref_checks": ref_dev,
            "ref_worst": max((d["dev_over_W"] for d in ref_dev),
                             default=0.0),
            "ref_window": ref_win}


def main():
    smoke = "--smoke" in sys.argv
    t0 = time.time()
    workers = 12
    l1chunk = r54.SPAN_L1
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
    ladder = (0.02, 0.004) if smoke else H_LADDER6
    u_delta = 0.01 if smoke else U_DELTA
    edges_full = np.linspace(-XI_MAX, XI_MAX, N_PAN_ARCH + 1)
    if smoke:
        edges_use = edges_full[SMOKE_LO:SMOKE_HI + 1]
        ref_picks_use = set(range(SMOKE_LO, SMOKE_HI))
        j_first_use = SMOKE_LO
    else:
        edges_use = edges_full
        ref_picks_use = set(PICK_PANELS)
        j_first_use = 0

    # ------------------------------------------------------------ S0 setup
    rho_o, nodes_o, values, fam, xw400, gram, a_mat, _, _ = r37.setup(False)
    base, _ = r37.min_h1(gram, a_mat, np.ones(len(nodes_o), complex))
    corr, _ = r37.min_h1(gram, a_mat, np.asarray(values, complex))
    xw1600 = [r59.phi_weights(a_, panels=PANELS, m=M_RED)
              for a_, _t in fam]
    m_nodes = float(np.mean([len(X) for X, _w in xw1600]))
    cnt = r80.counterpart_nodes(rho_o)
    model400 = r51.Model(fam, r37.K, xw400, base, corr, cnt)
    model = r54.ParModel(fam, r37.K, xw1600, base, corr, cnt)
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
    sec["C3_setup"] = c3
    print("C3 pass %s (C_book rel %.2e C1 rel %.2e)"
          % (c3["pass"], abs(C_book / C_BOOK_2051 - 1.0),
             abs(C1_book / C1_BOOK_2051 - 1.0)), flush=True)

    # ------------------------------------------- S1 Q controls + tier B
    t1 = time.time()
    qc400 = r54.window_control(fam, xw400, base, corr, rho_o, ps)
    c1_rel = abs(qc400["Q"] / Q400_FROZEN - 1.0)
    c1_ok = c1_rel <= TOL_C1C2 and qc400["Q"] < 0
    qc1600 = r54.window_control(fam, xw1600, base, corr, rho_o, ps)
    c2_rel = abs(qc1600["Q"] / Q1600_FROZEN - 1.0)
    c2_ok = c2_rel <= TOL_C1C2 and qc1600["Q"] < 0
    print("C1 Q_400 rel %.3e  C2 Q_1600 rel %.3e [%.1fs]"
          % (c1_rel, c2_rel, time.time() - t1), flush=True)
    sec["C1C2_window"] = {"Q_400": qc400["Q"], "rel_400": c1_rel,
                          "Q_1600": qc1600["Q"], "rel_1600": c2_rel,
                          "pass": bool(c1_ok and c2_ok)}
    if not smoke:
        a_mat16 = r80.family_values(fam, r37.K,
                                    np.asarray(nodes_o, complex), xw1600).T
        baseB, _ = r37.min_h1(gram, a_mat16, np.ones(len(nodes_o), complex))
        corrB, _ = r37.min_h1(gram, a_mat16, np.asarray(values, complex))
        gB = (qc1600["p"] ** 2 * np.abs(baseB @ qc1600["v"]) ** 2
              * np.abs(corrB @ qc1600["v"]) ** 2)
        fxB = qc1600["ker"] * gB
        QB = float(np.sum(0.5 * (fxB[1:] + fxB[:-1]) * r54.HH_CTRL))
        sec["tierB_diagnostic"] = {
            "d_base_rel": float(np.max(np.abs(baseB - base))
                                / np.max(np.abs(base))),
            "d_corr_rel": float(np.max(np.abs(corrB - corr))
                                / np.max(np.abs(corr))),
            "Q_1600_tierB": QB, "Q_shift_rel": abs(QB / qc1600["Q"] - 1.0)}
        print("tier-B: %s" % sec["tierB_diagnostic"], flush=True)
    sec["C4_span_equivalence"] = r54.controls_c4(model, workers)

    # ------------------------------------------------ S2 fine grid m=1600
    g_com, gpp, edges_f = r54.fine_grid(fam, xw1600, base, corr, rho_o,
                                        dxi_g, workers, "m=1600")
    gpp2 = np.append(gpp, [gpp[-1], gpp[-1]])   # trailing edge copies
    gmax_com = float(np.max(np.abs(g_com)))
    sec["fine_grid_1600"] = {"dxi": dxi_g, "points": len(g_com),
                             "gmax": gmax_com}

    # ------------------------------------------------------- S3 the rungs
    rows = []
    r54._PC = {"model": model}
    r54.phase_pool(workers)
    for h in ladder:
        n_pan = int(round(2 * XI_MAX / h))
        row = r51.run_rung(model, h, dxi_g, g_com, gpp2, n_pan, t0,
                           C_book, C1_book, c_k, om_k)
        rows.append(row)
        print("rung h %g: L3 %.6e agg %.6e main %.6e theta %.6e corr "
              "%.6e sumU %.4e a2v %d gap %.3e [%.1fs]"
              % (h, row["charge_L3"], row["charge_agg"], row["agg_main"],
                 row["agg_theta"], row["agg_corr"], row["sum_U"],
                 row["a2_violations"], row["a2_gap_charge"],
                 time.time() - t0), flush=True)
    a1_ok = all(r_["a1_abs_max"] <= 1e-9 * gmax_com for r_ in rows)
    a2a_ok = all(r_["a2_violations"] == 0 for r_ in rows)
    a2b_ok = all(r_["a2_gap_charge"] <= GAP_MAX for r_ in rows)
    b4_ok = all(np.isfinite(r_[k]) and r_[k] >= 0.0 for r_ in rows
                for k in ("charge_L3", "charge_agg", "agg_main",
                          "agg_theta", "agg_corr", "sum_U"))
    mins = [(min(r_["charge_L3"], r_["charge_agg"]), r_["h"]) for r_ in rows]
    best_min, h_best = min(mins)
    row_best = [r_ for r_ in rows if r_["h"] == h_best][0]
    l3_seq = [r_["charge_L3"] for r_ in rows]
    ag_seq = [r_["charge_agg"] for r_ in rows]
    a9_ok = all(l3_seq[i + 1] < l3_seq[i] for i in range(len(l3_seq) - 1)) \
        and all(ag_seq[i + 1] < ag_seq[i] for i in range(len(ag_seq) - 1))
    ratios = [ag_seq[i] / ag_seq[i + 1] for i in range(len(ag_seq) - 1)]
    print("rungs done; A1 %s A2a %s A2b %s A9 %s | best h %g min %.6e "
          "(L3 %.6e agg %.6e) | step ratios %s"
          % (a1_ok, a2a_ok, a2b_ok, a9_ok, h_best, best_min,
             row_best["charge_L3"], row_best["charge_agg"],
             ["%.3f" % q for q in ratios]), flush=True)
    sec["rungs_1600"] = rows
    sec["best_rung"] = {"h": h_best, "min": best_min,
                        "charge_L3": row_best["charge_L3"],
                        "charge_agg": row_best["charge_agg"]}
    sec["A9_step_ratios"] = ratios

    # ---------------------------------------------- S3b arch U grid
    t3b = time.time()
    nodes_u = np.arange(-XI_MAX, XI_MAX + u_delta / 2, u_delta)
    r54._PC = {"model": model}
    r54.phase_pool(workers)
    gj_u = model.g_jet(nodes_u, u_delta, 4096)
    uu2 = np.asarray(r51.j_supk(gj_u, 2, u_delta))
    uu1 = np.asarray(r51.j_supk(gj_u, 1, u_delta))
    print("arch U grid: %d nodes delta %g, U2 mean %.4e, U1 mean %.4e "
          "[%.1fs]" % (len(nodes_u), u_delta, float(np.mean(uu2)),
                       float(np.mean(uu1)), time.time() - t3b), flush=True)
    sec["arch_u_grid"] = {"delta": u_delta, "nodes": len(nodes_u),
                          "uu2_mean": float(np.mean(uu2)),
                          "uu1_mean": float(np.mean(uu1))}

    # ------------------------------------------------ S4 L1 nodal at h*
    t4 = time.time()
    n_best = int(round(2 * XI_MAX / h_best))
    nodes_h = np.linspace(-XI_MAX, XI_MAX, n_best + 1)
    r54._PC = {"model": model, "nodes": nodes_h, "xw": xw1600,
               "l1chunk": l1chunk}
    r54.phase_pool(workers)
    spans = [(lo, min(lo + r54.SPAN_JET, len(nodes_h)))
             for lo in range(0, len(nodes_h), r54.SPAN_JET)]
    parts = r54.pmap(r54._task_l1, spans)
    C_l1 = np.concatenate([p[0] for p in parts])
    EG = np.concatenate([p[1] for p in parts])
    coef, tot = r52.coef1_nodes(om_k, c_k, nodes_h, h_best)
    sum_cj = float(np.sum(coef))
    charge_e = float(np.sum(coef * EG))
    gmax_nodes = float(np.max(np.abs(C_l1)))
    echo = tot * r52.ECHO_REL * gmax_nodes * r52.INS
    charge_L1 = charge_e + echo
    b4_ok = b4_ok and all(np.isfinite(v) and v >= 0.0
                          for v in (charge_e, echo, charge_L1, tot)) \
        and abs(sum_cj / tot - 1.0) <= 1e-9
    sec["L1_nodal_best"] = {"h": h_best, "Coef1": tot,
                            "C_max": gmax_nodes,
                            "e_g_max": float(np.max(EG)),
                            "e_g_median": float(np.median(EG)),
                            "charge_nodal": charge_e, "charge_echo": echo,
                            "charge_L1": charge_L1}
    print("L1 h* %g: charge %.6e (nodal %.6e echo %.6e) e_g med %.3e "
          "[%.1fs]" % (h_best, charge_L1, charge_e, echo,
                       float(np.median(EG)), time.time() - t4), flush=True)
    # P3 control: L1 at h = 0.001 (the 2054 artifact reading)
    l1_ctrl = None
    if not smoke:
        t4b = time.time()
        n_c = int(round(2 * XI_MAX / H_OLD_BEST))
        nodes_c = np.linspace(-XI_MAX, XI_MAX, n_c + 1)
        r54._PC = {"model": model, "nodes": nodes_c, "xw": xw1600,
                   "l1chunk": l1chunk}
        r54.phase_pool(workers)
        spanc = [(lo, min(lo + r54.SPAN_JET, len(nodes_c)))
                 for lo in range(0, len(nodes_c), r54.SPAN_JET)]
        partc = r54.pmap(r54._task_l1, spanc)
        Cc1 = np.concatenate([p[0] for p in partc])
        EGc = np.concatenate([p[1] for p in partc])
        coefc, totc = r52.coef1_nodes(om_k, c_k, nodes_c, H_OLD_BEST)
        charge_ec = float(np.sum(coefc * EGc))
        echoc = totc * r52.ECHO_REL * float(np.max(np.abs(Cc1))) * r52.INS
        l1_ctrl = charge_ec + echoc
        p3_rel = abs(l1_ctrl / L1_2054_001 - 1.0)
        print("P3 L1 at h=0.001: %.10e (rel %.3e) [%.1fs]"
              % (l1_ctrl, p3_rel, time.time() - t4b), flush=True)

    b1 = None
    b1_ok = True
    if not smoke:
        t5 = time.time()
        b1 = r52.containment_b1(model, h_best, nodes_h, C_l1, EG, xw1600,
                                r54.PICKS_B1)
        b1_ok = all(r_["ok"] for r_ in b1)
        print("B1 containment %d/%d ok, worst ratio %.4f [%.1fs]"
              % (sum(r_["ok"] for r_ in b1), len(b1),
                 max(r_["ratio"] for r_ in b1), time.time() - t5),
              flush=True)
        sec["B1_containment"] = b1

    b3_new = {}
    b3_ok = True
    if not smoke:
        for hh in (0.0005, 0.00025):
            b3 = r52.diag_b3(model, hh, np.linspace(-XI_MAX, XI_MAX,
                                                    int(round(2 * XI_MAX
                                                              / hh)) + 1),
                             np.asarray(C_l1[:1]), xw1600, r54.PICKS_B1)
            b3_new[hh] = max(r_["abs_diff"] for r_ in b3)
        b3_ok = all(v == 0.0 for v in b3_new.values())
        print("B3 new rungs max abs diff %s (ok %s)"
              % (b3_new, b3_ok), flush=True)
    sec["B3_ladder_vs_fine_new"] = {str(k): v for k, v in b3_new.items()}

    # --------------------------------------- S5 C5 m=400 full-instrument
    c5 = {"pass": True, "skipped": True} if smoke else None
    if not smoke:
        t6 = time.time()
        gc4, gpp4, _ = r54.fine_grid(fam, xw400, base, corr, rho_o, dxi_g,
                                     workers, "m=400")
        gpp4p = np.append(gpp4, [gpp4[-1], gpp4[-1]])
        r54._PC = {"model": model400}
        r54.phase_pool(1)
        row4 = r51.run_rung(model400, 0.002, dxi_g, gc4, gpp4p, 2048, t0,
                            C_book, C1_book, c_k, om_k)
        l3_rel = abs(row4["charge_L3"] / L3_2051_0P002 - 1.0)
        ag_rel = abs(row4["charge_agg"] / AGG_2051_0P002 - 1.0)
        c5 = {"charge_L3_2055": row4["charge_L3"], "rel_L3": l3_rel,
              "charge_agg_2055": row4["charge_agg"], "rel_agg": ag_rel,
              "pass": bool(l3_rel <= TOL_C5 and ag_rel <= TOL_C5)}
        print("C5 m=400 cross-read: L3 rel %.3e agg rel %.3e [%.1fs]"
              % (l3_rel, ag_rel, time.time() - t6), flush=True)
        sec["C5_m400_crossread"] = c5

    # --------------------------------------------------- S6 arch old+new
    t7 = time.time()
    ar = r54.window_arch(fam, xw1600, base, corr, rho_o, ps)
    p1_rel = abs(ar["arch_proj"] / ARCH_2054_1600 - 1.0)
    c6_ok = abs(ar["width_mean"] / ANCHOR_WIDTH_MEAN_2043 - 1.0) \
        <= ANCHOR_WIDTH_TOL
    wm_rel = abs(ar["width_mean"] / WIDTH_MEAN_2054 - 1.0)
    print("arch old: width_mean %.6f (2043 rel %.2e, 2054 rel %.2e) "
          "arch_proj %.6e (P1 rel %.3e) [%.1fs]"
          % (ar["width_mean"],
             abs(ar["width_mean"] / ANCHOR_WIDTH_MEAN_2043 - 1.0), wm_rel,
             ar["arch_proj"], p1_rel, time.time() - t7), flush=True)
    sec["arch_old_1600"] = dict(ar, C6_width_ok=bool(c6_ok),
                                P1_rel=p1_rel, width_2054_rel=wm_rel)

    t8 = time.time()
    arch3 = arch3_charge(g_com, dxi_g, uu1, uu2, u_delta, edges_use,
                         j_first_use, ref_picks_use,
                         "smoke" if smoke else "m=1600")
    sec["arch3_new"] = arch3
    print("arch3 [%.1fs]" % (time.time() - t8), flush=True)

    # A7/A8 sigma-derivative containment vs mpmath polygamma (dps 45)
    t9 = time.time()
    mp.mp.dps = 45
    a7_worst = {k: 0.0 for k in ("sig", "s1", "s2", "s3")}
    a8_worst = 0.0
    n_fail = 0
    for uf in U_PICKS:
        ivp = mp.iv.mpf([repr(uf), repr(uf)])
        ch = sigma_chain_iv(ivp)
        z = mp.mpf('0.25') - 1j * mp.mpf(repr(uf)) / 2
        ref = {"sig": mp.log(mp.pi) - mp.re(mp.digamma(z)),
               "s1": -mp.im(mp.polygamma(1, z)) / 2,
               "s2": mp.re(mp.polygamma(2, z)) / 4,
               "s3": mp.im(mp.polygamma(3, z)) / 8}
        for k in ("sig", "s1", "s2", "s3"):
            c, h = ch[k]
            dev = abs(float(ref[k]) - c)
            ratio = dev / h if h > 0 else (0.0 if dev == 0 else 1e9)
            a7_worst[k] = max(a7_worst[k], ratio)
            if ratio > 1.0:
                n_fail += 1
        s_ref = r43.sigma_arch_iv(ivp)
        dev = abs(float(ref["sig"]) - float((mp.mpf(s_ref.a)
                                             + mp.mpf(s_ref.b)) / 2))
        span = float((mp.mpf(s_ref.b) - mp.mpf(s_ref.a)) / 2)
        if dev > span * (1 + 1e-9):
            n_fail += 1
        a8_worst = max(a8_worst, dev / span if span > 0 else 1e9)
    a7_ok = n_fail == 0
    print("A7 sigma-deriv containment worst ratios %s (A8 committed "
          "worst over span %.3e) [%.1fs]"
          % (a7_worst, a8_worst, time.time() - t9), flush=True)
    sec["A7_sigma_derivs"] = {"worst_ratios": a7_worst, "A8_worst": a8_worst,
                              "pass": bool(a7_ok)}

    a3 = {"pass": True, "skipped": True} if smoke else None
    if not smoke:
        r54._PC = {"model": model}
        r54.phase_pool(1)
        a3 = r51.iv_containment(model)
        sec["A3_iv_containment"] = {"pass": a3["pass"]}
    a6 = r51.selftest()
    b5 = r52.selftest()
    print("A6 %s B5 %s" % (a6["pass"], b5["pass"]), flush=True)
    sec["A6_jet_selftest"] = {"pass": a6["pass"]}
    sec["B5_forward_selftest"] = {"pass": b5["pass"]}

    a10_ok = (arch3["ref_worst"] < 1.0) and (arch3["ref_window"]["over_W"]
                                             < 1.0)
    sec["A10_reference"] = {"panel_worst_over_W": arch3["ref_worst"],
                            "window_over_W": arch3["ref_window"]["over_W"],
                            "pass": bool(a10_ok)}

    # ------------------------------------------------------- S7 verdict
    p2_ok = None
    p3_ok = None
    p1_ok = None
    if not smoke:
        row001 = [r_ for r_ in rows if abs(r_["h"] - H_OLD_BEST) < 1e-12][0]
        p2_rel = {k: abs(row001[k] / v - 1.0) for k, v in
                  (("charge_L3", L3_2054_001), ("charge_agg", AGG_2054_001),
                   ("agg_main", AGGMAIN_2054_001),
                   ("agg_theta", AGGTHETA_2054_001),
                   ("agg_corr", AGGCORR_2054_001))}
        p2_ok = all(v <= TOL_P for v in p2_rel.values())
        p3_ok = abs(l1_ctrl / L1_2054_001 - 1.0) <= TOL_P
        p1_ok = p1_rel <= TOL_P
        sec["P_controls"] = {"P1_rel": p1_rel, "P2_rel": p2_rel,
                             "P3_rel": abs(l1_ctrl / L1_2054_001 - 1.0)}
        print("P1 %s P2 %s P3 %s" % (p1_ok, p2_ok, p3_ok), flush=True)
    gates = {
        "P1_arch_old": bool(True if smoke else p1_ok),
        "P2_rung001": bool(True if smoke else p2_ok),
        "P3_L1_001": bool(True if smoke else p3_ok),
        "C1_Q400": bool(c1_ok), "C2_Q1600": bool(c2_ok),
        "C3_setup": bool(c3["pass"]), "C5_m400": bool(c5["pass"]),
        "C6_width": bool(c6_ok),
        "A1_pipeline": bool(a1_ok), "A2a_enclosure": bool(a2a_ok),
        "A2b_gap": bool(a2b_ok), "A3_iv": bool(a3["pass"]),
        "A6_jet": bool(a6["pass"]), "B5_forward": bool(b5["pass"]),
        "A7_sigma_derivs": bool(a7_ok), "A9_ladder": bool(a9_ok),
        "A10_reference": bool(a10_ok),
        "B1_containment": bool(b1_ok), "B3_new_rungs": bool(b3_ok),
        "B4_positivity": bool(b4_ok),
        "C4_span": bool((sec.get("C4_span_equivalence") or
                         {"pass": False})["pass"]),
    }
    total = None
    total_old = None
    if not all(gates.values()):
        verdict = "ANCHOR-FAIL"
    else:
        total = best_min + charge_L1 + arch3["arch3"]
        total_old = best_min + charge_L1 + ar["arch_proj"]
        if total < BAR10:
            verdict = "REDUCED-L2-VIABLE"
        elif total < BUDGET3:
            verdict = "REDUCED-L2-GRAY"
        else:
            verdict = "REDUCED-L2-FAIL"
    out = {"record": 2055, "status": verdict, "gates": gates,
           "owner": "one-copy G8-H", "m_reduced": M_RED,
           "scope": "committed 2037-class float pipeline with the "
                    "phi-quadrature rule at m = 1600; stored floats exact; "
                    "L5 not touched; L4 kill stands (m-independent)",
           "constants": {"budget3": BUDGET3, "bar10": BAR10,
                         "arch_2054_1600": ARCH_2054_1600,
                         "agg_2054_0p001": AGG_2054_001,
                         "l1_2054_0p001": L1_2054_001,
                         "C_book": C_book, "C1_book": C1_book,
                         "SAFE": SAFE, "u_delta": u_delta,
                         "M13": float(M13)},
           "sections": sec,
           "assembly": {"best_min": best_min, "h_best": h_best,
                        "charge_L1": charge_L1 if not smoke else None,
                        "arch3": arch3["arch3"],
                        "arch3_centre": arch3["centre"],
                        "total": total,
                        "total_over_budget3": (total / BUDGET3
                                               if total is not None
                                               else None),
                        "total_over_bar10": (total / BAR10
                                             if total is not None else None),
                        "total_oldconvention": total_old,
                        "old_over_bar10": (total_old / BAR10
                                           if total_old is not None
                                           else None)},
           "nonclaims": [
               "the sigma-derivative tail charges carry SAFE = 8 margin "
               "over the Cauchy/elementary bounds (validation peak 0.93 "
               "pre-SAFE at u = 0); the arch3 enclosure is of the PIPELINE "
               "function with stored floats as exact, same scope as the "
               "book channel",
               "the moment convention: panel measures are trapezoids of the "
               "committed fine-grid samples, with (dxi^2/12) int |g^(j)| "
               "error charges bounded by the model's own sup enclosures on "
               "the arch U grid",
               "L5 (F construction, phi quadrature, eigh/min-h1, sigma) "
               "remains registered, not touched",
               "L4 (full-line tail) separate and standing (record 2053); "
               "this verdict prices the WINDOW node only",
               "the m = 1600 rule's own residual (2053 cross-read rel "
               "4.3e-12) is not charged here",
               "COVER (uniformity over hypothetical off-line zeros) open",
               "not a producer theorem", "not RH"],
           "elapsed_s": None}
    out["elapsed_s"] = round(time.time() - t0, 1)
    path = os.path.join(ROOT, "results", "2055_reduced_second.json")
    with open(path, "w", encoding="utf-8", newline="\n") as f:
        json.dump(out, f, indent=2, default=float)
        f.write("\n")
    print("VERDICT", verdict)
    if total is not None:
        print("total = best_min %.6e + L1 %.6e + arch3 %.6e = %.6e "
              "(%.4fx budget3, %.4fx bar10)"
              % (best_min, charge_L1, arch3["arch3"], total,
                 total / BUDGET3, total / BAR10))
        print("old convention: %.6e (%.4fx bar10, arch_old %.6e)"
              % (total_old, total_old / BAR10, ar["arch_proj"]))
    print("RESULT", path)
    print("elapsed", out["elapsed_s"], flush=True)
    if r54._POOL is not None:
        r54._POOL.terminate()
        r54._POOL.join()


if __name__ == "__main__":
    main()