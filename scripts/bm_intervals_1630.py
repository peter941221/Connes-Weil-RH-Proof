#!/usr/bin/env python3
"""1630 numeric: the Beurling-Malliavin interval family of the tree's phase.

gamma(x) = 2 pi x log(pi) - 2 arg Gamma(1/4 + pi I x)   (the argument of m)
phi_a(x) = gamma(x) + a x                               (a >= 0, a corresponds to 4 pi log(1/lambda))

BM(phi) := components of { x : phi(x) != phi*(x) },  phi*(x) = max_{[x,inf)} phi
(definition quoted from Makarov-Poltoratski, Invent. Math. 180 (2010) 443-480,
 section 1.3; "short" = SUM over BM intervals with d(l) >= 1 of d^{beta-2} l^2 < inf).

Grid work is O(n): one forward pass of values, one backward pass of right maxima.
"""
import mpmath as mp

mp.mp.dps = 25
PI = mp.pi


def gam(x):
    x = mp.mpf(x)
    z = mp.mpc(mp.mpf('0.25'), PI * x)
    return 2 * PI * x * mp.log(PI) - 2 * mp.im(mp.loggamma(z))


def phi(x, a):
    return gam(x) + a * mp.mpf(x)


def golden_max(f, lo, hi, iters=80):
    gr = (mp.sqrt(5) - 1) / 2
    a, b = mp.mpf(lo), mp.mpf(hi)
    c, d = b - gr * (b - a), a + gr * (b - a)
    for _ in range(iters):
        if f(c) > f(d):
            b = d
        else:
            a = c
        c, d = b - gr * (b - a), a + gr * (b - a)
    return (a + b) / 2


def bisect(f, lo, hi, iters=120):
    a, b = mp.mpf(lo), mp.mpf(hi)
    fa = f(a)
    for _ in range(iters):
        m = (a + b) / 2
        if f(m) * fa > 0:
            a, fa = m, f(m)
        else:
            b = m
    return (a + b) / 2


def bm_analysis(a, lo=-14, hi=14, n=5601):
    xs = [lo + (hi - lo) * i / (n - 1) for i in range(n)]
    vals = [phi(x, a) for x in xs]
    rmax = [None] * n
    m = vals[-1]
    for i in range(n - 1, -1, -1):
        if vals[i] > m:
            m = vals[i]
        rmax[i] = m
    inside = [i for i in range(n) if rmax[i] - vals[i] > mp.mpf('1e-10')]
    if not inside:
        print("  a = %-10s : no BM interval in the window" % mp.nstr(a, 8))
        return
    runs = []
    s = p = inside[0]
    for i in inside[1:]:
        if i == p + 1:
            p = i
        else:
            runs.append((s, p))
            s = p = i
    runs.append((s, p))
    print("  a = %-10s : %d BM interval(s) in [%s, %s]" % (mp.nstr(a, 8), len(runs), lo, hi))
    for (s, e) in runs:
        x0, x1 = xs[s], xs[e]
        l = x1 - x0
        d = mp.mpf(0) if x0 <= 0 <= x1 else min(abs(x0), abs(x1))
        rm = [None] * (e - s + 1)
        m = vals[e]
        for i in range(e, s - 1, -1):
            if vals[i] > m:
                m = vals[i]
            rm[i - s] = m
        dx = (mp.mpf(hi) - mp.mpf(lo)) / (n - 1)
        tot = mp.mpf(0)
        for i in range(s, e + 1):
            xw = xs[i]
            tot += (rm[i - s] - vals[i]) / (PI * (1 + xw * xw)) * dx
        print("      [%s, %s]  l = %s  d = %s  INT (phi*-phi) dPi = %s"
              % (mp.nstr(x0, 8), mp.nstr(x1, 8), mp.nstr(l, 8), mp.nstr(d, 8), mp.nstr(tot, 6)))


print("gamma point values:")
for x in ['-3.0', '-2.0', '-1.0', '-0.5', '0', '0.5', '1.0', '1.5', '2.0', '3.0', '5.0']:
    print("   gamma(%6s) = %s" % (x, mp.nstr(gam(x), 12)))

print("\nincrements gamma(x+0.2) - gamma(x):")
for x in ['-2.0', '-1.2', '-0.8', '0', '0.8', '1.2', '2.0', '4.0']:
    xa = mp.mpf(x)
    print("   at %6s : %s" % (x, mp.nstr(gam(xa + mp.mpf('0.2')) - gam(xa), 8)))

xmax = golden_max(gam, mp.mpf('0.5'), mp.mpf('2.0'))
print("\nargmax on (0.5, 2) = %s   gamma = %s" % (mp.nstr(xmax, 12), mp.nstr(gam(xmax), 12)))
xstar = bisect(lambda t: gam(t) - gam(xmax), mp.mpf('-8'), mp.mpf('-1'))
print("x* in (-8,-1) with gamma(x*) = gamma(argmax):  x* = %s" % mp.nstr(xstar, 12))
print("   l = argmax - x* = %s , d = 0 (interval contains 0)" % mp.nstr(xmax - xstar, 12))

print("\nBM families (window [-14,14], 5601 points):")
for a in ['0', '1.0', '8.710344', '28.943517']:
    bm_analysis(mp.mpf(a))

print("\nclass-gap table |gamma(x)| / |x|^beta:")
for x in [10, 100, 1000, 10000]:
    xa = mp.mpf(x)
    print("   x=%5d  |gamma| = %s" % (x, mp.nstr(abs(gam(xa)), 10)))
    for b in ['1', '0.5', '0.1']:
        bb = mp.mpf(b)
        print("      beta=%4s : ratio = %s   ratio/log|x| = %s"
              % (b, mp.nstr(abs(gam(xa)) / xa ** bb, 8), mp.nstr(abs(gam(xa)) / xa ** bb / mp.log(xa), 8)))