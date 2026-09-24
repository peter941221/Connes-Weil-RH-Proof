#!/usr/bin/env python3
"""Record 1976 rig: exact-rational design of the third-order interval certificate.

Provenance: record 1976 "the third rung is a certified rational interval".
Formulas from records 1973/1974/1975 (committed closed forms, reflected gain
data, the cleared bracket).  No floating point enters a certified number: every
enclosure below is computed in exact Fraction arithmetic and mirrors the Lean
statements one for one.

Objects (s-coordinate, x = (1 - s) / 2, left half = 0 < s < 1):

    V s        = 4 s / (1 - s^2)
    U s        = (exp (V s) - 1) / (exp (V s) + 1) = 1 - 2 T ((1 - s)/2)
    P(s, u)    = alpha s * u^2 - beta s * u + gamma s      (thirdOrderBracket)
    alpha s    = 12 (1 + s^2)^3
    beta  s    = 36 s + 12 s^3 - 36 s^5 - 12 s^7
    gamma s    = -1 + 8 s^6 + 3 s^8 - 42 s^4

Certified exp bounds (n = 20, y = V q / m with 0 <= y <= 1):

    T20 y = sum_{i < 20} y^i / i!,   E20 y = y^20 * 21 / (20! * 20)
    expLo m q = (T20 y - E20 y)^m <= exp (V q) <= (T20 y + E20 y)^m = expHi m q
    U q in [ (expLo - 1)/(expHi + 1), (expHi - 1)/(expLo + 1) ]

Cheap committed fallbacks (no exp machinery):
    V q / (V q + 2) <= U q   (self_div_add_two_le_exp_ratio)   and   U q <= 1.

Certificate layout on (0, 1):

    [0, s_lo]  = left chain, pieces with P < 0   (tight or cheap U bounds)
    [s_lo, s_hi] the monotone straddle: h' > 0 there, h s_d < 0 < h s_c
    [s_hi, 1]  = right chain, pieces with P > 0

x-bracket: x* = (1 - s*)/2 lies in [x_c, x_d] = [(1-s_c)/2, (1-s_d)/2].

Rung: derivOrderL1 3 smoothSeed = 4 * int_0^{1/2} |T'''| with
    int_0^{1/2} |T'''| = T'' x_c + T'' x_d + int_{x_c}^{x_d} |T'''|,
the gap integral in [0, (x_d - x_c) * 16 * max|P| / (1 - s_c^2)^6].
"""

from fractions import Fraction as F
import math
import sys

sys.set_int_max_str_digits(2000000)

# ---------------------------------------------------------------- exact objects

def V(q):
    return 4 * q / (1 - q * q)


def ALPHA(q):
    return 12 * (1 + q * q) ** 3


def BETA(q):
    return 36 * q + 12 * q ** 3 - 36 * q ** 5 - 12 * q ** 7


def GAMMA(q):
    return -1 + 8 * q ** 6 + 3 * q ** 8 - 42 * q ** 4


def P(q, u):
    return ALPHA(q) * u * u - BETA(q) * u + GAMMA(q)


FACTS = [1] * 21
for _i in range(1, 21):
    FACTS[_i] = FACTS[_i - 1] * _i
TAIL = F(21) / (FACTS[20] * 20)


def exp_bounds(q, m):
    """(expLo, expHi) at the rational point q with root exponent m."""
    y = V(F(q)) / m
    t = sum(y ** i / F(FACTS[i]) for i in range(20))
    e = y ** 20 * TAIL
    return (t - e) ** m, (t + e) ** m


def u_exp_bounds(q, m):
    elo, ehi = exp_bounds(q, m)
    return (elo - 1) / (ehi + 1), (ehi - 1) / (elo + 1)


def u_cheap_lower(q):
    v = V(F(q))
    return v / (v + 2)


def m_for(q, cap):
    if q >= 1:                     # V is junk at s = 1; the cheap bound U <= 1 covers it
        return None
    v = V(F(q))
    m = 1
    while m < v:
        m *= 2
    return m if m <= cap else None


# ---------------------------------------------------------------- enclosures

def enc(a, b, uL, uH):
    """Lean piece enclosure: P in [pLo, pHi] on [a, b]."""
    mlo = 36 * a + 12 * a ** 3 - 36 * b ** 5 - 12 * b ** 7
    mhi = 36 * b + 12 * b ** 3 - 36 * a ** 5 - 12 * a ** 7
    clo = -1 + 8 * a ** 6 + 3 * a ** 8 - 42 * b ** 4
    chi = -1 + 8 * b ** 6 + 3 * b ** 8 - 42 * a ** 4
    return ALPHA(a) * uL ** 2 - mhi * uH + clo, ALPHA(b) * uH ** 2 - mlo * uL + chi


def piece_bounds(a, b, cap):
    ma, mb = m_for(a, cap), m_for(b, cap)
    uL = u_exp_bounds(a, ma)[0] if ma is not None else u_cheap_lower(a)
    uH = u_exp_bounds(b, mb)[1] if mb is not None else F(1)
    return uL, uH


def decide(a, b, cap):
    uL, uH = piece_bounds(a, b, cap)
    plo, phi = enc(a, b, uL, uH)
    if phi < 0:
        return "neg", uL, uH, plo, phi
    if plo > 0:
        return "pos", uL, uH, plo, phi
    return "OPEN", uL, uH, plo, phi


SIZES = [F(1, 10), F(1, 20), F(1, 50), F(1, 100), F(1, 200), F(1, 500),
         F(1, 1000), F(1, 2000), F(1, 5000), F(1, 10000)]


def chain(start, stop, cap):
    pieces, cur = [], F(start)
    while cur < stop:
        nxt, st = stop, "OPEN"
        for w in SIZES:
            cand = min(cur + w, stop)
            st = decide(cur, cand, cap)[0]
            if st != "OPEN":
                nxt = cand
                break
        pieces.append((cur, nxt, st))
        cur = nxt
    return pieces


# ---------------------------------------------------------------- float checks

def u_f(s):
    v = 4.0 * s / (1.0 - s * s)
    return math.tanh(0.5 * v)


def P_f(s):
    t = u_f(s)
    return (12 * (1 + s * s) ** 3) * t * t - (36 * s + 12 * s ** 3 - 36 * s ** 5 - 12 * s ** 7) * t \
        + (-1 + 8 * s ** 6 + 3 * s ** 8 - 42 * s ** 4)


def hprime_split_f(s):
    """The Lean split form: alpha' u^2 - beta' u + gamma' + (2 alpha u - beta) u'."""
    u = u_f(s)
    t2 = 1.0 - u * u
    vp = 4 * (1 + s * s) / (1 - s * s) ** 2
    ap = 72 * s * (1 + s * s) ** 2
    bp = 36 + 36 * s * s - 180 * s ** 4 - 84 * s ** 6
    gp = 48 * s ** 5 + 24 * s ** 7 - 168 * s ** 3
    a = 12 * (1 + s * s) ** 3
    b = 36 * s + 12 * s ** 3 - 36 * s ** 5 - 12 * s ** 7
    return ap * u * u - bp * u + gp + (2 * a * u - b) * (vp / 2) * t2


def report_float():
    dh = 1e-6
    print("== float sanity ==")
    worst = 0.0
    for s in (0.1, 0.3, 0.5, 0.55, 0.6, 0.8, 0.95):
        num = (P_f(s + dh) - P_f(s - dh)) / (2 * dh)
        worst = max(worst, abs(num - hprime_split_f(s)))
    print("  worst |numeric h' - split form| = %.2e" % worst)
    lo, hi = 0.5, 0.6
    for _ in range(200):
        mid = 0.5 * (lo + hi)
        if P_f(mid) < 0:
            lo = mid
        else:
            hi = mid
    sstar = 0.5 * (lo + hi)
    print("  s* = %.15f   x* = %.15f   u(s*) = %.15f" % (sstar, 0.5 * (1 - sstar), u_f(sstar)))
    print("  P(0.55) = %+.3e  P(0.57) = %+.3e  P(0.6) = %+.4f"
          % (P_f(0.55), P_f(0.57), P_f(0.6)))
    hs = min(hprime_split_f(s / 1000) for s in range(1, 999))
    print("  min of h' over the grid = %+.4f" % hs)
    for s in (0.2, 0.4, 0.5, 0.55, 0.5635, 0.6, 0.7, 0.9):
        print("    h'(%.4f) = %+9.4f   P = %+10.3e" % (s, hprime_split_f(s), P_f(s)))
    print()


# ---------------------------------------------------------------- straddle

def straddle_certificate(s_lo, s_hi, cap=4):
    """Exact split-form certificate: h' > 0 on [s_lo, s_hi]."""
    a, b = F(s_lo), F(s_hi)
    uL = u_exp_bounds(a, m_for(a, cap))[0]
    uH = u_exp_bounds(b, m_for(b, cap))[1]
    vp = lambda s: 4 * (1 + s * s) / (1 - s * s) ** 2
    ap = lambda s: 72 * s * (1 + s * s) ** 2
    bp = lambda s: 36 + 36 * s * s - 180 * s ** 4 - 84 * s ** 6
    gp = lambda s: 48 * s ** 5 + 24 * s ** 7 - 168 * s ** 3
    t1 = ap(a) * uL ** 2 - bp(a) * uH + gp(b)          # alpha' u^2 - beta' u + gamma'
    t2 = (2 * ALPHA(a) * uL - BETA(b)) * (vp(a) / 2) * (1 - uH ** 2)
    print("== straddle [%s, %s] ==" % (s_lo, s_hi))
    print("  u in [%.15f, %.15f]" % (float(uL), float(uH)))
    print("  term1 >= %+.6f   term2 >= %+.6f   h' >= %+.6f"
          % (float(t1), float(t2), float(t1 + t2)))
    print("  2 alpha(a) uL - beta(b) = %+.4f  (need > 0)"
          % float(2 * ALPHA(a) * uL - BETA(b)))
    for q in (s_lo, s_hi):
        uLq, uHq = u_exp_bounds(F(q), m_for(F(q), cap))
        plo, phi = enc(F(q), F(q), uLq, uHq)
        print("  H(%s) in [%+.3e, %+.3e]" % (q, float(plo), float(phi)))
    print()
    return t1 + t2


# ---------------------------------------------------------------- T'' bounds

def Gain(s):
    return 8 * (1 + s * s) / (1 - s * s) ** 2


def GainSlope(s):
    return -32 * s * (s * s + 3) / (1 - s * s) ** 3


def ttwo_bounds(s, cap=4):
    """Exact bracket for T'' ((1-s)/2) via p(u) = (1-u^2)(u G^2 + G') and |p'| <= Mp."""
    s = F(s)
    g, gp = Gain(s), GainSlope(s)
    uL, uH = u_exp_bounds(s, m_for(s, cap))
    Mp = g * g * (1 + 3 * uH ** 2) + 2 * uH * abs(gp)
    pL = (1 - uL ** 2) * (uL * g * g + gp)
    half = (uH - uL) * Mp / 4
    return pL / 4 - half, pL / 4 + half


def report_rung(s_d, s_c, cap=4):
    x_c, x_d = (1 - s_c) / 2, (1 - s_d) / 2
    tlo_c, thi_c = ttwo_bounds(s_c, cap)
    tlo_d, thi_d = ttwo_bounds(s_d, cap)
    # gap sup: |T'''| = 16 (1-u^2) |P| / (1-s^2)^6 <= 16 * max|P| / (1-s_c^2)^6
    uL, uH = piece_bounds(s_d, s_c, cap)
    plo, phi = enc(s_d, s_c, uL, uH)
    pmax = max(abs(plo), abs(phi))
    sup = 16 * pmax / (1 - s_c ** 2) ** 6
    gap = (x_d - x_c) * sup
    rlo = 4 * (tlo_c + tlo_d)
    rhi = 4 * (thi_c + thi_d + gap)
    print("== rung ==")
    print("  s in [%s, %s]  =>  x in [%s, %s] = [%.10f, %.10f]"
          % (s_d, s_c, x_c, x_d, float(x_c), float(x_d)))
    print("  T''(x_c) in [%.12f, %.12f]" % (float(tlo_c), float(thi_c)))
    print("  T''(x_d) in [%.12f, %.12f]" % (float(tlo_d), float(thi_d)))
    print("  P on gap in [%.3e, %.3e]   sup|T'''| <= %.6e   gap int <= %.3e"
          % (float(plo), float(phi), float(sup), float(gap)))
    print("  rung in [%.12f, %.12f]  (width %.2e)"
          % (float(rlo), float(rhi), float(rhi - rlo)))
    return rlo, rhi


# ---------------------------------------------------------------- main

def main():
    report_float()
    s_lo, s_hi = F(55, 100), F(23, 40)             # 0.55, 0.575 (straddle)
    s_d, s_c = F(5634883, 10 ** 7), F(5634884, 10 ** 7)
    st = straddle_certificate(s_lo, s_hi)

    cap = 32
    left = chain(0, s_lo, cap)
    right = chain(s_hi, 1, cap)
    print("== pieces ==")
    ok = True
    for tag, ch, want in (("L", left, "neg"), ("R", right, "pos")):
        for (a, b, _) in ch:
            st_, uL, uH, plo, phi = decide(a, b, cap)
            ok = ok and st_ == want
            print("  %s [%9s, %9s] uL=%.12f uH=%.12f  P in [%+12.6e, %+12.6e] %s"
                  % (tag, a, b, float(uL), float(uH), float(plo), float(phi), st_))
    print("  left chain all neg: %s   right chain all pos: %s   (pieces: %d + %d)"
          % (all(x[2] == "neg" for x in left), all(x[2] == "pos" for x in right),
             len(left), len(right)))
    print("  straddle certificate positive: %s" % (st > 0))
    print()

    rlo, rhi = report_rung(s_d, s_c, cap)
    print()
    print("== exact final constants ==")
    print("  s_lo = %s ; s_hi = %s ; s_d = %s ; s_c = %s" % (s_lo, s_hi, s_d, s_c))
    print("  rung lower = %.15f   (denominator digits %d)" % (float(rlo), rlo.denominator.bit_length() * 30103 // 100000))
    print("  rung upper = %.15f   (denominator digits %d)" % (float(rhi), rhi.denominator.bit_length() * 30103 // 100000))
    print("  certified decimal bracket: [787283384/10000000, 787283385/10000000]")
    print("     lower margin %.3e   upper margin %.3e"
          % (float(rlo - F(787283384, 10 ** 7)), float(F(787283385, 10 ** 7) - rhi)))


if __name__ == "__main__":
    main()