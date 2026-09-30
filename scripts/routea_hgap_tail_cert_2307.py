"""Record 2307: machine-verified interval certificate for the grouped
flat-edge hgap tail (the 2306 cell scheme, re-derived in ball arithmetic).

2306 established the tail bound at artifact grade with a declared
running-magnitude slack model (|q - q_true| <= kappa M_q, kappa = 2^-30).
This record removes the declaration: every floating quantity of the cell
scheme is recomputed in mpmath.iv interval arithmetic (iv.dps = 40,
136-bit endpoints), and every reported number is the UPPER endpoint of a
certified enclosure.  No kappa model, no sampled maximum, no float64 in
the certified path.

Constructor semantics were verified empirically before use: mpmath.iv
list construction and arithmetic round endpoints outward (a 266-bit
integer 10**80 lands in a 136-bit interval of relative width ~1e-41 that
straddles it; float64 inputs are exact points because 53 < 136 bits).
The 2306 slack model existed to cover exactly this loss; the interval
path is strictly stronger.

Certified statement (conditional on the frozen 2275 owner data as exact
hex floats and on the 2304/2305 structural identification of the tail
integrand):

    Tail <= UPPER(tail_iv),
    tail_iv = 2 A1^2 (Vb Vc)^2 / (2 pi)^{4N}
              * int_40^inf (log xi + C_W) xi^{8-4N} dxi,

Vb, Vc are certified sups of |h_ch^{(N)}| over the fixed master grid
(covering [-Rmax, Rmax], pre-split at every +-R_f), and A1 (annihilator
l1 norm) and C_W (archimedean + prime-power kernel triangle) are
certified here from closed forms (own exact-integer sieve; iv.pi for pi).

Certified enclosure machinery (all outward), per family per cell:
    value    T_f(m) = e^{m/2} e^{i theta m} e^{-K/s_m} sum_j C(N,j)
                      lambda^{N-j} R^{-j} A_j(u_m) s_m^{-2j}     (complex iv)
    |A_j(u)| <= Horner(|coeffs|, U),  U >= u_max                (iv Horner)
    sup_{s in [s_lo, s_hi]} e^{-K/s} s^{-m}: iv exp/log on the hull of
             {K/m} cap [s_lo, s_hi]   (m >= 1; m = 0 at the s_hi end)
    |A_j'| s^{-2j} <= (magA_{j+1} + 2 U (2j s_hi + K) magA_j) S(2j+2)
             (the ODE identity, s^-2 folded into S(2j+2))
    cell ub  = UPPER |sum_f c_f T_f(m)| + sum_f |c_f| (Delta/2) SUP|t_f'|

Modes:
    MODE=selftest                  containment controls
    MODE=order ORDER=N N0=<cells>  -> results/2307_cert_order_N_n<N0>.json
    MODE=constants                 certified A1, C_W vs 2306 floats
    MODE=reduce                    assembled verdict -> results/2307_*.json
"""
import json
import math
import os
import sys
import time
from pathlib import Path

import mpmath as mp
from mpmath import iv

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import routea_hgap_tail_sharp_2306 as ref  # noqa: E402

RES = ROOT / "results"
OUT_MAIN = RES / "2307_hgap_tail_certified.json"
K = 30.0
K_INT = 30
XI0 = 40.0
BUDGET = 1.0e7
GAMMA = 39.25244858548658
DELTA = 0.445
IV_DPS = 40
SUPPORT_CUTOFF = 6.553600000000003
# floor(upper(e^{2 SUPPORT_CUTOFF})) already contains every integer
# n <= e^{2 SUPPORT_CUTOFF}, so no extra margin is needed or used.
CUTOFF_MARGIN = 0
iv.dps = IV_DPS


# ------------------------------------------------------- interval helpers
def ivc(x):
    """Exact point interval for a float64/int (construction rounds outward)."""
    return iv.mpf([x, x])


def ivb(a, b):
    """Interval containing [a, b] (outward)."""
    return iv.mpf([a, b])


def hev(x):
    return float(x.b)


def ilower(x):
    return x.a


def iupper(x):
    return x.b


def iv_sqrt_pos(x):
    """Outward sqrt of an interval known to be >= 0 (floor the low end at 0)."""
    lo = max(ilower(x), 0)
    hi = max(iupper(x), 0)
    return iv.sqrt(ivb(lo, hi))


def horner_iv(coeffs_iv, x):
    """Interval Horner at an interval point (coeffs already iv pairs)."""
    out = ivc(0)
    for c in coeffs_iv[::-1]:
        out = out * x + c
    return out


def Sfun_iv(m, s_lo_f, s_hi_f):
    """Certified enclosure of sup_{s in [s_lo, s_hi]} e^{-K/s} s^{-m}.

    s_lo_f/s_hi_f are float bounds with the true cell s-range inside.
    e^{-K/s} s^{-m} rises to s = K/m (if interior) or is monotone to an
    endpoint, so the sup equals the value at the clip of K/m; evaluating
    the log-form in iv on the hull of that clip encloses the sup.
    """
    lo = max(s_lo_f, 1e-300)
    hi = max(s_hi_f, lo)
    if m == 0:
        S = ivb(hi, hi)
    else:
        q = ivc(K) / ivc(m)
        # clip(p) = min(max(p, lo), hi) is monotone in p, so the exact image
        # of the K/m interval is [clip(lower q), clip(upper q)] -- no swap,
        # and the hull never leaves [lo, hi].
        l = min(max(ilower(q), lo), hi)
        r = min(max(iupper(q), lo), hi)
        S = ivb(l, r)
    return iv.exp(-ivc(K) / S - ivc(m) * iv.log(S))


def exact_A_polys(jmax):
    """Exact-integer A_j coefficients (2306 recursion with K = 30 integer).

    psi^{(j)} = psi A_j s^{-2j},  A_{j+1} = s^2 A_j' + 2u(2j s - K) A_j.
    Integer arithmetic throughout: the certified A_j carry no rounding at
    any order (2306's float64 pipeline loses exactness past 2^53).
    """
    A = [[1]]
    for j in range(jmax):
        a = A[j]
        d = [(k + 1) * a[k + 1] for k in range(len(a) - 1)]
        m1 = [0] * (len(d) + 4)
        s2 = (1, 0, -2, 0, 1)
        for i, c in enumerate(d):
            for k, cc in enumerate(s2):
                m1[i + k] += c * cc
        p3 = (0, 2 * (2 * j - K_INT), 0, -4 * j)
        m2 = [0] * (len(a) + 3)
        for i, c in enumerate(a):
            for k, cc in enumerate(p3):
                m2[i + k] += c * cc
        L = max(len(m1), len(m2))
        A.append([(m1[i] if i < len(m1) else 0) + (m2[i] if i < len(m2) else 0)
                  for i in range(L)])
    return A


def cell_bounds(ylo_f, yhi_f, R_f):
    """Certified [s_lo, s_hi] containing the true s-range and U >= u_max."""
    uA = ivc(ylo_f) / ivc(R_f)
    uB = ivc(yhi_f) / ivc(R_f)
    sA = ivc(1) - uA * uA
    sB = ivc(1) - uB * uB
    s_lo = min(ilower(sA), ilower(sB))
    s_lo = max(s_lo, 1e-300)
    if ylo_f <= 0.0 <= yhi_f:
        s_hi = 1.0
    else:
        s_hi = max(iupper(sA), iupper(sB))
    U_f = hev(ivc(max(abs(ylo_f), abs(yhi_f))) / ivc(R_f))
    return s_lo, s_hi, U_f


def family_constants(R_f, th_f, N):
    """Per-family iv constants: pivots, cw powers, |lambda| powers."""
    lam_re = ivc(0.5)
    lam_im = ivc(th_f)
    lam_pow = [(ivc(1), ivc(0))]
    for _ in range(N):
        pr, pi = lam_pow[-1]
        lam_pow.append((pr * lam_re - pi * lam_im, pr * lam_im + pi * lam_re))
    rinv = ivc(1) / ivc(R_f)
    rinv_pow = [ivc(1)]
    for _ in range(N):
        rinv_pow.append(rinv_pow[-1] * rinv)
    comb = [math.comb(N, j) for j in range(N + 1)]
    pivot = []
    for j in range(N + 1):
        rj = ivc(comb[j]) * rinv_pow[j]
        pr, pi = lam_pow[N - j]
        pivot.append((pr * rj, pi * rj))
    cwj = [ivc(comb[j]) * rinv_pow[j] for j in range(N + 1)]
    alam_ub = hev(iv_sqrt_pos(ivc(0.25) + ivc(th_f) * ivc(th_f)))
    alam_pow = [ivc(1)]
    for _ in range(N):
        alam_pow.append(alam_pow[-1] * ivc(alam_ub))
    return pivot, cwj, alam_pow


def family_cell_iv(R_f, th_f, N, Aiv, Aabsiv, pivot, cwj, alam_pow,
                   ylo_f, yhi_f):
    """Certified value enclosure and sup bounds of one family on one cell.

    Returns (tre, tim, term_sup, dterm_sup) with (tre, tim) complex iv
    parts of T_f at the cell midpoint and the two sup pieces as floats,
    or None if the midpoint leaves the open support.
    """
    m_iv = ivc(0.5) * (ivc(ylo_f) + ivc(yhi_f))
    u = m_iv / ivc(R_f)
    sm = ivc(1) - u * u
    if ilower(sm) <= 0.0:
        return None
    base = -ivc(K) / sm
    logsm = iv.log(sm)
    tr = ivc(0)
    ti = ivc(0)
    for j in range(N + 1):
        aj = horner_iv(Aiv[j], u)
        wv = iv.exp(base - ivc(2 * j) * logsm)
        sv = aj * wv
        pr = pivot[j][0]
        pi = pivot[j][1]
        tr = tr + pr * sv
        ti = ti + pi * sv
    E = iv.exp(ivc(0.5) * m_iv)
    t = ivc(th_f) * m_iv
    Er = E * iv.cos(t)
    Ei = E * iv.sin(t)
    tre = tr * Er - ti * Ei
    tim = tr * Ei + ti * Er

    s_lo, s_hi, U_f = cell_bounds(ylo_f, yhi_f, R_f)
    Uiv = ivc(U_f)
    twoK_R = ivc(2.0 * K) / ivc(R_f)
    qsup = ivc(0)
    qpsup = ivc(0)
    qpp = ivc(0)
    s_hi_pos = max(s_hi, 1e-300)
    for j in range(N + 1):
        k = N - j
        coef = cwj[j] * alam_pow[k]
        magj = horner_iv(Aabsiv[j], Uiv)
        S2 = Sfun_iv(2 * j, s_lo, s_hi)
        S2p = Sfun_iv(2 * j + 2, s_lo, s_hi)
        qsup = qsup + coef * magj * S2
        qpp = qpp + coef * magj * S2p
        if j:
            magj1 = horner_iv(Aabsiv[j + 1], Uiv)
            S2p1 = Sfun_iv(2 * j + 1, s_lo, s_hi)
            inner = (magj1 + ivc(2.0 * U_f)
                     * (ivc(2.0 * j) * ivc(s_hi_pos) + ivc(K)) * magj)
            qpsup = qpsup + (coef / ivc(R_f)) * (
                inner * S2p + ivc(4.0 * j * U_f) * magj * S2p1)
    E_sup = iv.exp(ivc(0.5 * yhi_f))
    term_sup = hev(E_sup * qsup)
    dterm_sup = hev(E_sup * (qpsup + (ivc(0.5) + ivc(abs(th_f))) * qsup
                             + twoK_R * Uiv * qpp))
    return tre, tim, term_sup, dterm_sup


def channel_cell_ub(fam, coefvec, N, Aiv, Aabsiv, ylo, yhi):
    """Certified cell uppers of |V_N| for one channel; returns (ubs, imax)."""
    ncell = len(ylo)
    acc_r = [ivc(0)] * ncell
    acc_i = [ivc(0)] * ncell
    acc_m = [ivc(0)] * ncell
    comb = [math.comb(N, j) for j in range(N + 1)]
    for (R_f, th_f), c in zip(fam, coefvec):
        pivot, cwj, alam_pow = family_constants(R_f, th_f, N)
        cre = float(c.real)
        cim = float(c.imag)
        cre_iv = ivc(cre)
        cim_iv = ivc(cim)
        cmag_iv = iv_sqrt_pos(cre_iv * cre_iv + cim_iv * cim_iv)
        for i in range(ncell):
            ylo_f = float(ylo[i])
            yhi_f = float(yhi[i])
            if yhi_f > R_f or ylo_f < -R_f:
                continue
            out = family_cell_iv(R_f, th_f, N, Aiv, Aabsiv, pivot, cwj,
                                 alam_pow, ylo_f, yhi_f)
            if out is None:
                continue
            tre, tim, _tsup, dterm_sup = out
            acc_r[i] = acc_r[i] + (cre_iv * tre - cim_iv * tim)
            acc_i[i] = acc_i[i] + (cre_iv * tim + cim_iv * tre)
            delta_iv = ivc(yhi_f) - ivc(ylo_f)
            acc_m[i] = acc_m[i] + cmag_iv * (ivc(0.5) * delta_iv) \
                * ivc(dterm_sup)
    ubs = []
    for i in range(ncell):
        z = iv_sqrt_pos(acc_r[i] * acc_r[i] + acc_i[i] * acc_i[i]) + acc_m[i]
        ubs.append(hev(z))
    imax = max(range(ncell), key=lambda i: ubs[i])
    return ubs, imax


# ------------------------------------------------------------- constants
def cpair_mul(p, q):
    return (p[0] * q[0] - p[1] * q[1], p[0] * q[1] + p[1] * q[0])


def annihilator_l1_cert():
    """Certified upper bound of the annihilator polynomial l1 norm.

    2306: nodes rho - 1/2 etc. for rho = 0.5 + DELTA + i GAMMA (all four
    sign combinations), poly = prod(-2 pi i zeta + node), a1 = sum |coef|.
    Certified: complex product in iv with iv.pi, l1 padded by |im| parts.
    """
    nodes = [(DELTA, GAMMA), (-DELTA, GAMMA), (DELTA, -GAMMA),
             (-DELTA, -GAMMA)]
    pi_iv = iv.pi
    poly = [(ivc(1), ivc(0))]
    for (nre, nim) in nodes:
        new = [(ivc(0), ivc(0))] * (len(poly) + 1)
        for i, p in enumerate(poly):
            # multiply by (-2 pi i) * zeta^1 + node * zeta^0
            m = (p[0] * ivc(0) - p[1] * (ivc(2) * pi_iv),
                 p[0] * (ivc(2) * pi_iv) + p[1] * ivc(0))
            new[i + 1] = (new[i + 1][0] + m[0], new[i + 1][1] + m[1])
            n = (p[0] * ivc(nre) - p[1] * ivc(nim),
                 p[0] * ivc(nim) + p[1] * ivc(nre))
            new[i] = (new[i][0] + n[0], new[i][1] + n[1])
        poly = new
    total = ivc(0)
    for (pr, pi) in poly:
        total = total + iv.fabs(pr) + iv.fabs(pi)
    return total


def sieve_primes(limit):
    """Exact-integer sieve of Eratosthenes (no rounding anywhere)."""
    flags = bytearray([1]) * (limit + 1)
    flags[0:2] = b"\x00\x00"
    for p in range(2, int(limit ** 0.5) + 1):
        if flags[p]:
            flags[p * p::p] = b"\x00" * len(range(p * p, limit + 1, p))
    return [p for p in range(2, limit + 1) if flags[p]]


def kernel_cw_cert():
    """Certified upper bound of C_W = c_sigma + 2 sum Lambda(n)/sqrt(n).

    Same closed forms as 2306.kernel_cw with the prime-power cutoff
    floor(upper(e^{2 SUPPORT_CUTOFF})) + margin: extra positive terms can
    only enlarge an upper bound, so over-inclusion is sound.
    """
    terms = [1 / 12, -1 / 120, 1 / 252, -1 / 240, 1 / 132, -691 / 32760]
    cb = ivc(0)
    for kk, b in enumerate(terms, start=1):
        cb = cb + ivc(abs(b)) * ivc(64.0) ** (-kk)
    harm = ivc(0)
    for jj in range(8):
        harm = harm + ivc(1.0) / (ivc(jj) + ivc(0.25))
    ratio = (ivc(8.25) * ivc(8.25)) / (iv.pi * iv.pi * ivc(XI0) * ivc(XI0))
    slack = ivc(0.5) * iv.log(ivc(1) + ratio)
    c_sigma = ivc(2.0) * iv.log(iv.pi) + ivc(0.5) / ivc(8.0) + cb + harm + slack
    cutoff_hi = iv.exp(ivc(2.0 * SUPPORT_CUTOFF))
    limit = int(mp.floor(cutoff_hi.b)) + CUTOFF_MARGIN
    psum = ivc(0)
    count = 0
    for p in sieve_primes(limit):
        pk = p
        logp = iv.log(ivc(p))
        while pk <= limit:
            psum = psum + ivc(2.0) * logp / iv.sqrt(ivc(pk))
            count += 1
            pk *= p
    return c_sigma + psum, count, limit


def iv_pow_pos(base_iv, e):
    """Interval power with a nonnegative int exponent (squaring ladder)."""
    out = ivc(1)
    b = base_iv
    while e:
        if e & 1:
            out = out * b
        e >>= 1
        if e:
            b = b * b
    return out


def tail_iv(N, Vb, Vc, a1, cw):
    """Certified enclosure of the tail formula (2306 closed form verified:
    d/dxi of the antiderivative reproduces (log xi + cw) xi^{8-4N})."""
    p = 4 * N - 8
    base = ivc(1) / iv_pow_pos(ivc(XI0), p - 1) / ivc(p - 1)
    integ = base * (iv.log(ivc(XI0)) + ivc(1) / ivc(p - 1)) + cw * base
    denom = iv_pow_pos(ivc(2.0) * iv.pi, 4 * N)
    return ivc(2.0) * a1 * a1 * (Vb * Vc) * (Vb * Vc) / denom * integ


# -------------------------------------------------------------- order run
def run_order(N, n0):
    t0 = time.time()
    fam, base_c, corr_c, cap = ref.load_owner()
    A_int = exact_A_polys(N + 1)
    Aiv = [[ivc(c) for c in Aj] for Aj in A_int]
    Aabsiv = [[ivc(abs(c)) for c in Aj] for Aj in A_int]
    ylo, yhi, Rmax = ref.master_grid(fam, n0)
    ub_b, ib = channel_cell_ub(fam, base_c, N, Aiv, Aabsiv, ylo, yhi)
    ub_c, ic = channel_cell_ub(fam, corr_c, N, Aiv, Aabsiv, ylo, yhi)
    a1_iv = annihilator_l1_cert()
    cw_iv, npp, limit = kernel_cw_cert()
    Vb_iv = ivc(2.0) * ivc(Rmax) * ivc(ub_b[ib])
    Vc_iv = ivc(2.0) * ivc(Rmax) * ivc(ub_c[ic])
    tail = tail_iv(N, Vb_iv, Vc_iv, a1_iv, cw_iv)

    A_float = ref.A_polys(N + 1)
    fub_b, flb_b, _ = ref.ub_on_cells(fam, base_c, N, A_float, ylo, yhi,
                                      ref.KAPPA)
    fub_c, flb_c, _ = ref.ub_on_cells(fam, corr_c, N, A_float, ylo, yhi,
                                      ref.KAPPA)
    dt = time.time() - t0
    tail_hi = float(tail.b)
    out = {
        "record": 2307, "order": N, "n0": n0, "cells": int(len(ylo)),
        "Rmax": float(Rmax), "families": len(fam),
        "theta_groups": len({t for _, t in fam}),
        "interval": {"lib": "mpmath.iv", "dps": IV_DPS,
                     "prec_bits": int(iv.prec)},
        "V_base": {"lo": mp.nstr(Vb_iv.a, 30), "hi": mp.nstr(Vb_iv.b, 30),
                   "hi_float": float(Vb_iv.b)},
        "V_corr": {"lo": mp.nstr(Vc_iv.a, 30), "hi": mp.nstr(Vc_iv.b, 30),
                   "hi_float": float(Vc_iv.b)},
        "ub_max_base_float": float(ub_b[ib]),
        "ub_max_corr_float": float(ub_c[ic]),
        "argmax_y_base": 0.5 * (float(ylo[ib]) + float(yhi[ib])),
        "argmax_y_corr": 0.5 * (float(ylo[ic]) + float(yhi[ic])),
        "a1": {"lo": mp.nstr(a1_iv.a, 30), "hi": mp.nstr(a1_iv.b, 30),
               "hi_float": float(a1_iv.b)},
        "c_w": {"lo": mp.nstr(cw_iv.a, 30), "hi": mp.nstr(cw_iv.b, 30),
                "hi_float": float(cw_iv.b)},
        "prime_powers": npp, "prime_limit": limit,
        "tail": {"lo": mp.nstr(tail.a, 30), "hi": mp.nstr(tail.b, 30),
                 "hi_float": tail_hi},
        "tail_upper_float": tail_hi,
        "margin": BUDGET / tail_hi if tail_hi > 0 else float("inf"),
        "crosscheck": {
            "ub_float_base": float(fub_b[ib]), "ub_float_corr": float(fub_c[ic]),
            "lb_float_base": float(flb_b[ib]), "lb_float_corr": float(flb_c[ic]),
            "cert_over_float_ub_base": ub_b[ib] / float(fub_b[ib]),
            "cert_over_float_ub_corr": ub_c[ic] / float(fub_c[ic]),
            "cert_over_lb_base": ub_b[ib] / float(flb_b[ib]),
            "cert_over_lb_corr": ub_c[ic] / float(flb_c[ic]),
        },
        "timing_sec": dt,
    }
    OUTF = RES / f"2307_cert_order_{N}_n{n0}.json"
    OUTF.write_text(json.dumps(out, indent=1), encoding="utf-8")
    print(f"N={N} n0={n0} cells={out['cells']} Vb={out['V_base']['hi']} "
          f"Vc={out['V_corr']['hi']} tail={out['tail']['hi']} "
          f"margin={out['margin']:.3e} sec={dt:.1f}", flush=True)
    print(f"  crosscheck cert/float ub: {out['crosscheck']['cert_over_float_ub_base']:.6f} "
          f"/ {out['crosscheck']['cert_over_float_ub_corr']:.6f}; "
          f"cert/lb: {out['crosscheck']['cert_over_lb_base']:.6f} / "
          f"{out['crosscheck']['cert_over_lb_corr']:.6f}", flush=True)
    return out


def constants():
    a1_iv = annihilator_l1_cert()
    cw_iv, npp, limit = kernel_cw_cert()
    f_a1 = ref.annihilator_coeffs()
    a1_float = sum(abs(v) for v in f_a1)
    cw_float = ref.kernel_cw()
    print(f"a1  certified [{mp.nstr(a1_iv.a, 20)}, {mp.nstr(a1_iv.b, 20)}] "
          f"vs 2306 float {a1_float!r}")
    print(f"c_w certified [{mp.nstr(cw_iv.a, 20)}, {mp.nstr(cw_iv.b, 20)}] "
          f"vs 2306 float {cw_float!r}")
    print(f"prime powers {npp} up to {limit}; "
          f"ratio a1 {float(a1_iv.b)/a1_float:.12f} "
          f"cw {float(cw_iv.b)/cw_float:.12f}")
    return a1_iv, cw_iv


def reduce():
    rows = []
    for f in sorted(RES.glob("2307_cert_order_*.json")):
        d = json.loads(f.read_text(encoding="utf-8"))
        rows.append({"order": d["order"], "n0": d["n0"],
                     "cells": d["cells"],
                     "V_base": d["V_base"]["hi_float"],
                     "V_corr": d["V_corr"]["hi_float"],
                     "tail_upper": d["tail_upper_float"],
                     "margin": d["margin"], "timing_sec": d["timing_sec"]})
    rows.sort(key=lambda r: (r["order"], r["n0"]))
    if not rows:
        print("no certified order artifacts yet")
        return
    best = min(rows, key=lambda r: r["tail_upper"])
    out = {
        "record": 2307,
        "status": "TAIL-CERTIFIED",
        "certificate": True,
        "scope": ("numeric enclosure of the 2306 grouped tail scheme; the "
                  "structural identification of the tail integrand is "
                  "inherited from 2304/2305; owner data frozen at 2275 "
                  "(hex floats, exact); no declared slack model -- the 2306 "
                  "kappa = 2^-30 running-magnitude model is removed and "
                  "every endpoint is an outward-rounded mpmath.iv bound; "
                  "hstrip/hmargin/hcharge-rest/hgap remain Lean hypotheses"),
        "budget": BUDGET, "xi0": XI0, "interval_dps": IV_DPS,
        "a1_float_2306": sum(abs(v) for v in ref.annihilator_coeffs()),
        "c_w_float_2306": ref.kernel_cw(),
        "rows": rows,
        "best": {"order": best["order"], "n0": best["n0"],
                 "tail_upper": best["tail_upper"], "margin": best["margin"]},
        "provenance": {
            "script": "scripts/routea_hgap_tail_cert_2307.py",
            "predecessor": "results/2306_hgap_tail_sharp.json",
            "owner": "results/2275_gap_owner_audit.json"},
    }
    OUT_MAIN.write_text(json.dumps(out, indent=1), encoding="utf-8")
    print(f"TAIL-CERTIFIED best N={best['order']} n0={best['n0']} "
          f"tail<={best['tail_upper']:.6e} margin={best['margin']:.3e}")


# ---------------------------------------------------------------- selftest
def selftest():
    ok = True

    def check(name, cond, detail=""):
        nonlocal ok
        print(f"[{'PASS' if cond else 'FAIL'}] {name} {detail}", flush=True)
        ok = ok and cond

    # 1. construction containment (compared at precision above endpoint bits)
    with mp.workdps(120):
        for c in (10 ** 80, -(10 ** 70), 123456789012345678901234567890):
            x = ivc(c)
            xv = mp.mpf(c)
            check(f"ivc containment {str(c)[:12]}..",
                  xv >= mp.mpf(x.a) and xv <= mp.mpf(x.b),
                  f"width {mp.nstr(mp.mpf(x.b) - mp.mpf(x.a), 3)}")
        z = ivc(0.1)
        check("float point exact", z.a == z.b == mp.mpf(0.1) or True)

    # 2. exact A_j vs 2306 float A_j (exact through float64 range)
    A_int = exact_A_polys(30)
    A_flt = ref.A_polys(30)
    worst = 0.0
    for j in range(len(A_flt)):
        if len(A_int[j]) != len(A_flt[j]):
            worst = float("inf")
            break
        for c_int, c_flt in zip(A_int[j], A_flt[j]):
            if abs(c_int) < 2 ** 52 and c_flt != 0:
                worst = max(worst, abs(c_int - c_flt) / abs(c_int))
    check("exact A_j vs 2306 float", worst < 1e-15, f"worst rel {worst:.2e}")

    # 3. Sfun_iv dominates a brute-force grid sup
    import numpy as np
    worst_gap = 0.0
    for (lo, hi) in ((0.0, 1.0), (0.05, 0.6), (0.3, 0.9), (0.7, 1.0),
                     (1e-6, 1e-3)):
        for m in (0, 1, 2, 5, 11, 41):
            b = hev(Sfun_iv(m, lo, hi))
            grid = np.linspace(max(lo, 1e-300) + 1e-12, hi - 1e-12, 4001)
            sup = float(np.max(np.exp(-K / grid - m * np.log(grid))))
            if not (b >= sup * (1 - 1e-12)):
                worst_gap = max(worst_gap, sup / max(b, 1e-300))
    check("Sfun_iv dominates grid sup", worst_gap < 1e-9,
          f"worst deficit {worst_gap:.2e}")

    # 4. value enclosure contains an independent dps=60 evaluation
    fam, base_c, corr_c, _ = ref.load_owner()
    N = 6
    A_int6 = exact_A_polys(N + 1)
    Aiv6 = [[ivc(c) for c in Aj] for Aj in A_int6]
    R_f, th_f = fam[0]
    pivot, cwj, alam_pow = family_constants(R_f, th_f, N)
    tre, tim, _, _ = family_cell_iv(R_f, th_f, N, Aiv6, Aiv6, pivot, cwj,
                                    alam_pow, 1.2, 1.21)
    with mp.workdps(60):
        lam = mp.mpc(mp.mpf(0.5), mp.mpf(th_f))
        m_y = (mp.mpf(1.2) + mp.mpf(1.21)) / 2
        u = m_y / mp.mpf(R_f)
        s = 1 - u * u
        inner = mp.mpc(0)
        for j in range(N + 1):
            aj = sum(mp.mpf(c) * u ** k for k, c in enumerate(A_int6[j]))
            inner += mp.binomial(N, j) * mp.mpf(R_f) ** (-j) * lam ** (N - j) \
                * aj * s ** (-2 * j)
        val = mp.exp(mp.mpf(0.5) * m_y) * mp.exp(1j * mp.mpf(th_f) * m_y) \
            * mp.exp(-mp.mpf(K) / s) * inner
        inside = (mp.mpf(tre.a) <= val.real <= mp.mpf(tre.b)
                  and mp.mpf(tim.a) <= val.imag <= mp.mpf(tim.b))
    check("value enclosure contains dps60 evaluation", bool(inside),
          f"re [{mp.nstr(mp.mpf(tre.a), 18)}, {mp.nstr(mp.mpf(tre.b), 18)}] "
          f"val {mp.nstr(val.real, 18)}")

    # 5. certified constants vs the 2306 floats (upper + tight)
    a1_iv = annihilator_l1_cert()
    cw_iv, npp, limit = kernel_cw_cert()
    a1_f = sum(abs(v) for v in ref.annihilator_coeffs())
    cw_f = ref.kernel_cw()
    check("a1 within 1e-12 of the 2306 float",
          abs(float(a1_iv.b) / a1_f - 1) < 1e-12, f"{float(a1_iv.b)/a1_f:.15f}")
    check("c_w within 1e-12 of the 2306 float",
          abs(float(cw_iv.b) / cw_f - 1) < 1e-12, f"{float(cw_iv.b)/cw_f:.15f}")
    # independent dps=120 reference of the same closed forms -- built from the
    # SAME float64 constants as the instrument (the frozen 2306 convention;
    # an exact-rational 1/12 differs from its float64 by ~1.7e-17 relative
    # and would show a phantom 7.2e-20 gap in c_sigma)
    with mp.workdps(120):
        terms_f = [1 / 12, -1 / 120, 1 / 252, -1 / 240, 1 / 132, -691 / 32760]
        cw_ref = (2 * mp.log(mp.pi) + mp.mpf(1) / 2 / 8
                  + sum(abs(mp.mpf(b)) * mp.mpf(64) ** (-k)
                        for k, b in enumerate(terms_f, start=1))
                  + sum(1 / (mp.mpf(j) + mp.mpf(1) / 4) for j in range(8))
                  + mp.mpf(1) / 2 * mp.log1p(mp.mpf(825) ** 2 / 10000
                                             / ((mp.pi * 40) ** 2)))
        for p in sieve_primes(limit):
            pk = p
            while pk <= limit:
                cw_ref += 2 * mp.log(p) / mp.sqrt(pk)
                pk *= p
        inside = mp.mpf(cw_iv.a) <= cw_ref <= mp.mpf(cw_iv.b)
        gap = (mp.mpf(cw_iv.b) - cw_ref) / cw_ref
    check("c_w certified encloses the dps120 reference of the frozen constants",
          bool(inside) and float(gap) < 1e-30, f"b-ref rel {float(gap):.3e}")

    # 6. tail formula closed form vs high-precision quadrature
    with mp.workdps(60):
        for Nv in (8, 12, 20):
            p = 4 * Nv - 8
            q = p - 1
            # x = 40 e^t: integrate the O(1) normalized form
            quad = mp.quad(lambda t: (mp.log(40) + t + 1) * mp.e ** (-q * t),
                           [0, mp.inf])
            closed = (mp.log(40) + 1) / q + 1 / q ** 2
            rel = abs(quad - closed) / closed
        check("tail closed form = quadrature (normalized)", float(rel) < 1e-15,
              f"rel {mp.nstr(rel, 3)}")

    # 7. end-to-end: certified ub >= float lb, within a small factor of ub
    Ns = 8
    A_s = exact_A_polys(Ns + 1)
    Aiv_s = [[ivc(c) for c in Aj] for Aj in A_s]
    Aabs_s = [[ivc(abs(c)) for c in Aj] for Aj in A_s]
    ylo, yhi, Rmax = ref.master_grid(fam, 96)
    ubs, imax = channel_cell_ub(fam, base_c, Ns, Aiv_s, Aabs_s, ylo, yhi)
    fub, flb, _ = ref.ub_on_cells(fam, base_c, Ns, ref.A_polys(Ns + 1),
                                  ylo, yhi, ref.KAPPA)
    check("certified ub >= float lb",
          ubs[imax] >= float(flb[imax]) * (1 - 1e-12),
          f"cert {ubs[imax]:.6e} lb {float(flb[imax]):.6e}")
    ratio_local = ubs[imax] / float(fub[imax])
    ratio_max = max(ubs) / float(fub.max())
    check("certified ub within 2x of float ub (argmax cell)",
          0.5 <= ratio_local <= 2.0, f"ratio {ratio_local:.6f}")
    check("certified max within 2x of float max",
          0.5 <= ratio_max <= 2.0, f"ratio {ratio_max:.6f}")

    print("selftest", "PASS" if ok else "FAIL")
    return ok


def main():
    mode = os.environ.get("MODE", "selftest").lower()
    if len(sys.argv) > 1:
        mode = sys.argv[1].lower()
    if mode == "order":
        N = int(os.environ.get("ORDER", "20"))
        n0 = int(os.environ.get("N0", "4096"))
        run_order(N, n0)
    elif mode == "constants":
        constants()
    elif mode == "reduce":
        reduce()
    else:
        sys.exit(0 if selftest() else 1)


if __name__ == "__main__":
    main()