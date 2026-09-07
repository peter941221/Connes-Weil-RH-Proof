#!/usr/bin/env python3
# Record 1220 (v2): entrywise envelope probe for the 1219 E2-E5 campaign.
#
# Exact Fraction arithmetic throughout; mpmath is used ONLY for float
# sanity echoes and never feeds any bound.  All enclosures are proven
# shapes that map 1:1 onto planned Lean lemmas:
#   exp brick   : e^z in [S_N, S_N + rem] (positive series + geometric tail)
#   log brick   : log q = k log 2 + 2 artanh((m-1)/(m+1)) + remainder
#   pi brick    : Machin-type arctan partial sums with alternating remainder
#   gamma brick : H_20 - log 21 + sum (-1)^m T_m(21)/m, E-M ladder for T_m
#   bump ladder : b^(k)(x) = b(x) D_k(g',...,g^(k)), D-recursion exact,
#                 |g^(j)(x)| <= j!/2 (1-X)^(-j-1), X = max |x| on the interval
#   per-cell    : F(s,y) = b(s) b(y/2-s), Taylor in s at c_B (coefficients
#                 a_k as tight intervals: g^(j) at rational points are exact
#                 rationals, b values via the exp brick), y-drift bounds via
#                 the mixed product rule, Taylor remainder via the ladder.
#   P factors   : Legendre polys of degree <= 7 enter EXACTLY as bivariate
#                 polynomials; per-cell integrals are exact rationals.
#
# Registered branch (1220 prereg section 4):
#   GO  : assembled (0,0)/(7,7) widths <= 5e-13 AND inside the 1217 boxes.
#   NO-GO: otherwise (ABORTED-UNINFORMATIVE; legal recoveries only).
#
# RH NOT claimed.

from fractions import Fraction as Fr
import sys

ZERO = Fr(0)
ONE = Fr(1)


def fact(n):
    r = 1
    for i in range(2, n + 1):
        r *= i
    return r


# ---------------------------------------------------------------- IV class
class IV:
    """Closed rational interval [lo, hi]."""

    __slots__ = ("lo", "hi")

    def __init__(self, lo, hi=None):
        if hi is None:
            hi = lo
        lo = Fr(lo)
        hi = Fr(hi)
        if lo > hi:
            raise ValueError("empty interval %s %s" % (lo, hi))
        self.lo = lo
        self.hi = hi

    def __repr__(self):
        return "IV[%s, %s]" % (float(self.lo), float(self.hi))

    def width(self):
        return self.hi - self.lo

    def mid(self):
        return (self.lo + self.hi) / 2

    def __add__(self, o):
        return IV(self.lo + o.lo, self.hi + o.hi)

    __radd__ = __add__

    def __neg__(self):
        return IV(-self.hi, -self.lo)

    def __sub__(self, o):
        return IV(self.lo - o.hi, self.hi - o.lo)

    def __mul__(self, o):
        a = self.lo * o.lo
        b = self.lo * o.hi
        c = self.hi * o.lo
        d = self.hi * o.hi
        return IV(min(a, b, c, d), max(a, b, c, d))

    __rmul__ = __mul__

    def scale(self, c):
        c = Fr(c)
        if c >= 0:
            return IV(c * self.lo, c * self.hi)
        return IV(c * self.hi, c * self.lo)

    def inv(self):
        if self.lo <= 0 <= self.hi:
            raise ValueError("division across zero")
        return IV(1 / self.hi, 1 / self.lo)


# ------------------------------------------------------------- exp brick
def _exp_pos_iv(z):
    """exp(z) enclosure for z >= 0; argument halved until the series
    window N+2 covers it, then interval-squared back."""
    if z.hi > 12:
        half = IV(z.lo / 2, z.hi / 2)
        e2 = _exp_pos_iv(half)
        return e2 * e2
    zlo, zhi = z.lo, z.hi
    n = 40
    flo = Fr(1)  # k = 0 term
    fhi = Fr(1)
    term_lo = Fr(1)
    term_hi = Fr(1)
    for k in range(1, n + 1):
        term_lo = term_lo * zlo / k
        term_hi = term_hi * zhi / k
        flo += term_lo
        fhi += term_hi
    # remainder z^(n+1)/(n+1)! * 1/(1 - z/(n+2)) for z <= zhi < n+2
    rem = zhi ** (n + 1) / fact(n + 1) / (1 - zhi / (n + 2))
    return IV(flo, fhi + rem)


def exp_iv(z):
    if z.lo >= 0:
        return _exp_pos_iv(z)
    if z.hi <= 0:
        return _exp_pos_iv(-z).inv()
    lo = _exp_pos_iv(IV(-z.lo)).inv().lo
    hi = _exp_pos_iv(IV(z.hi)).hi
    return IV(lo, hi)


# ------------------------------------------------------------- log brick
LOG2 = None


def _artanh_iv(w):
    """2 artanh(w) for rational w in [0, 1/3], as IV."""
    n = 60
    s_lo = Fr(0)
    s_hi = Fr(0)
    t_lo = w
    t_hi = w
    for k in range(n):
        p = 2 * k + 1
        s_lo += t_lo / p
        s_hi += t_hi / p
        t_lo *= w * w
        t_hi *= w * w
    rem = 2 * t_hi / (2 * n + 1) / (1 - w * w)
    return IV(2 * s_lo, 2 * s_hi + rem)


def _log_iv_positive(q):
    """log(q) for rational q > 0, as IV."""
    global LOG2
    if q <= 0:
        raise ValueError("log of nonpositive")
    # write q = 2^k * m with m in [1,2)
    k = q.numerator.bit_length() - q.denominator.bit_length()
    if k >= 1 or Fr(1) / 2 > q * (Fr(2) ** (-k)):
        # adjust so that m in [1,2)
        while q * Fr(2) ** (-k) >= 2:
            k += 1
        while q * Fr(2) ** (-k) < 1:
            k -= 1
    m = q * Fr(2) ** (-k)
    if LOG2 is None:
        LOG2 = _artanh_iv(Fr(1, 3))  # log 2 = 2 artanh(1/3)
    w = (m - 1) / (m + 1)
    return _artanh_iv(w) + LOG2.scale(k)


def log_iv(q):
    if not isinstance(q, Fr):
        q = Fr(q)
    if q >= 1:
        return _log_iv_positive(q)
    return _log_iv_positive(1 / q).scale(-1)  # log q = -log(1/q)


def log_iv_of_iv(z):
    """log of an interval with positive endpoints, via monotonicity."""
    lo = log_iv(z.lo).lo
    hi = log_iv(z.hi).hi
    return IV(lo, hi)


# -------------------------------------------------------------- pi brick
def _arctan_iv(x):
    """arctan(x) for rational |x| <= 1/2: partial sum S_N, then the
    alternating remainder |R| <= |x|^(2N+1)/(2N+1)."""
    n = 50
    s = Fr(0)
    t = x
    for k in range(n):
        term = t / (2 * k + 1)
        if k % 2 == 0:
            s += term
        else:
            s -= term
        t = t * x * x
    rem = abs(t) / (2 * n + 1)  # t now holds x^(2N+1)
    return IV(s - rem, s + rem)


PI = None


def pi_iv():
    """pi = 4 (arctan(1/2) + arctan(1/3))."""
    global PI
    if PI is None:
        PI = (_arctan_iv(Fr(1, 2)) + _arctan_iv(Fr(1, 3))).scale(4)
    return PI


# ----------------------------------------------------------- gamma brick
_BERN = None


def bernoulli(n):
    """Bernoulli numbers B_0..B_n via sum_{k} C(m+1,k) B_k = 0 (B1 = -1/2)."""
    global _BERN
    if _BERN is None:
        _BERN = [Fr(1), Fr(-1, 2)]
    while len(_BERN) <= n:
        m = len(_BERN)
        s = Fr(0)
        for k in range(m):
            s += Fr(binom(m + 1, k)) * _BERN[k]
        _BERN.append(-s / (m + 1))
    return _BERN[n]


def binom(n, k):
    return Fr(fact(n), fact(k) * fact(n - k))


def powfalling(m, j):
    """RISING factorial m(m+1)...(m+j-1): d^j/dx^j x^-m has magnitude
    (m)_j^rising x^(-m-j)."""
    r = 1
    for t in range(j):
        r *= m + t
    return r


def tm_iv(m, n0, j_terms):
    """T_m(n0) = sum_{k>=n0} k^-m by Euler-Maclaurin, exact IV."""
    n0 = Fr(n0)
    acc = IV(n0 ** (1 - m) / (m - 1))
    acc = acc + IV(n0 ** (-m) / 2)
    for j in range(1, j_terms + 1):
        B2j = bernoulli(2 * j)
        c = B2j * powfalling(m, 2 * j - 1) / fact(2 * j)
        term = c * n0 ** (-m - 2 * j + 1)
        acc = acc + IV(term)
    # remainder <= 2x first omitted term (terms decrease by ~(m+2j)/(2 pi n0))^2
    j = j_terms + 1
    B2j = bernoulli(2 * j)
    rem = 2 * abs(B2j * powfalling(m, 2 * j - 1) / fact(2 * j)) * n0 ** (-m - 2 * j + 1)
    return IV(acc.lo - rem, acc.hi + rem)


GAMMA = None


def gamma_iv():
    """gamma = H_20 - log 21 + sum_{m>=2} (-1)^m T_m(21)/m  (+ remainder)."""
    global GAMMA
    if GAMMA is None:
        H20 = sum(Fr(1, k) for k in range(1, 21))
        acc = IV(H20) - log_iv(21)
        mtop = 14
        for m in range(2, mtop + 1):
            tm = tm_iv(m, 21, 8)
            term = tm.scale((-1) ** m / m)
            acc = acc + term
        # single tail bound for m > mtop: |T_(mtop+1)(21)|/(mtop+1) with
        # T_N(21) <= 21^(-N)/(N-1) (integral bound)
        m = mtop + 1
        rem_tot = Fr(21) ** (1 - m) / (m - 1) / m
        GAMMA = IV(acc.lo - rem_tot, acc.hi + rem_tot)
    return GAMMA


# --------------------------------------------------- rational poly tools
def padd(p, q):
    r = dict(p)
    for e, c in q.items():
        r[e] = r.get(e, ZERO) + c
    return {e: c for e, c in r.items() if c != 0}


def pmul(p, q):
    r = {}
    for e1, c1 in p.items():
        for e2, c2 in q.items():
            e = e1 + e2
            r[e] = r.get(e, ZERO) + c1 * c2
    return {e: c for e, c in r.items() if c != 0}


def ppow(p, n):
    r = {0: ONE}
    for _ in range(n):
        r = pmul(r, p)
    return r


def pder(p):
    r = {}
    for e, c in p.items():
        if e >= 1:
            r[e - 1] = r.get(e - 1, ZERO) + c * e
    return r


# ------------------------------------------------------------ Legendre
def legendre_coeffs(n):
    """P_n(x) = sum c_k x^k, exact dict."""
    p0 = {0: ONE}
    p1 = {1: ONE}
    if n == 0:
        return p0
    if n == 1:
        return p1
    for k in range(1, n):
        # (k+1) P_{k+1} = (2k+1) x P_k - k P_{k-1}
        a = pmul({1: ONE}, p1)
        t = {e: Fr(2 * k + 1) * c for e, c in a.items()}
        u = {e: Fr(-k) * c for e, c in p0.items()}
        p0, p1 = p1, padd(t, u)
        p1 = {e: c / (k + 1) for e, c in p1.items()}
    return p1


LEG = [legendre_coeffs(n) for n in range(8)]


def leg_der(p, d):
    for _ in range(d):
        p = pder(p)
    return p


# ------------------------------------------------------ bump derivative ladder
def g_deriv_bound(j, xlo, xhi):
    """|g^(j)| <= j!/2 * ((1-X)^-(j+1)) on [xlo,xhi], X = max|x|."""
    X = max(abs(xlo), abs(xhi))
    if X >= 1:
        raise ValueError("ladder interval touches singularity")
    return Fr(fact(j), 2) * Fr(1, (1 - X) ** (j + 1))


def g_deriv_value(j, c):
    """exact rational g^(j)(c) = j!/2 [(1-c)^-(j+1) + (-1)^j (1+c)^-(j+1)]."""
    return Fr(fact(j), 2) * (Fr(1) / Fr((1 - c) ** (j + 1))
                             + (Fr(1) if j % 2 == 0 else Fr(-1)) / Fr((1 + c) ** (j + 1)))


def bump_D(k):
    """D_k as dict monomial-tuple(exponents of v1..vk) -> signed coeff,
    where b^(k) = b * D_k(v1,...,vk), v_j = g^(j)."""
    D = {(): ONE}
    for _ in range(k):
        nxt = {}
        for mono, c in D.items():
            # d/dx term: for each present factor v_j (j>=1), replace v_j by
            # v_{j+1} and multiply by exponent
            for idx, e in enumerate(mono):
                if e == 0:
                    continue
                nm = list(mono) + [0]
                nm[idx] -= 1
                nm[idx + 1] += 1
                t = tuple(nm)
                nxt[t] = nxt.get(t, ZERO) + c * e
            # -v1 * term
            nm = list(mono) + [0]
            nm[0] += 1
            t = tuple(nm)
            nxt[t] = nxt.get(t, ZERO) - c
        D = nxt
    return D


D_CACHE = {}


def bump_D_bound(k, xlo, xhi):
    """upper bound for |b^(k)(x)| on [xlo,xhi] (rational).  The interval
    is intersected with (-1,1) first; b vanishes identically outside."""
    global D_CACHE
    key = (k, xlo, xhi)
    if key in D_CACHE:
        return D_CACHE[key]
    xlo = max(Fr(xlo), Fr(-1) + Fr(1, 10 ** 12))
    xhi = min(Fr(xhi), Fr(1) - Fr(1, 10 ** 12))
    if xlo > xhi:
        D_CACHE[key] = ZERO
        return ZERO
    if k == 0:
        r = bump_hi(xlo, xhi)
        D_CACHE[key] = r
        return r
    D = bump_D(k)
    V = [g_deriv_bound(j + 1, xlo, xhi) for j in range(k)]
    bhi = bump_hi(xlo, xhi)
    s = ZERO
    for mono, c in D.items():
        t = abs(c)
        for idx, e in enumerate(mono):
            t *= V[idx] ** e
        s += t
    r = s * bhi
    D_CACHE[key] = r
    return r


def bump_value_iv(c):
    """tight IV for b(c) = exp(-1/(1-c^2)) at rational |c| < 1."""
    g = Fr(1) / Fr(1 - c * c)
    return exp_iv(IV(-g))


def bump_hi(xlo, xhi):
    X = max(abs(Fr(xlo)), abs(Fr(xhi)))
    if X >= 1:
        return Fr(0)
    xmin = min(abs(Fr(xlo)), abs(Fr(xhi)))
    gmin = Fr(1) / Fr(1 - xmin * xmin)
    return exp_iv(IV(-gmin)).hi


_BDV_CACHE = {}


def bump_deriv_value_iv(m, x):
    """tight IV of b^(m)(x) at rational |x| < 1 (exact g-derivs, exp brick)."""
    key = (m, Fr(x))
    r = _BDV_CACHE.get(key)
    if r is not None:
        return r
    D = bump_D(m)
    acc = ZERO
    for mono, coef in D.items():
        t = Fr(coef)
        for idx, e in enumerate(mono):
            t *= g_deriv_value(idx + 1, x) ** e
        acc += t
    r = bump_value_iv(x) * IV(acc)
    if len(_BDV_CACHE) > 1500000:
        _BDV_CACHE.clear()
    _BDV_CACHE[key] = r
    return r


def F_s_deriv_value(k, c, ybar):
    """tight IV of d^k/ds^k [ b(s) b(y/2 - s) ] at s = c, y = ybar."""
    # = sum_m binom(k,m) (-1)^(k-m) b^(m)(c) b^(k-m)(u), u = ybar/2 - c
    u = Fr(ybar) / 2 - Fr(c)
    tot = IV(Fr(0))
    for m in range(k + 1):
        sgn = ONE if (k - m) % 2 == 0 else -ONE
        term = bump_deriv_value_iv(m, c).scale(Fr(binom(k, m)) * sgn)
        term = term * bump_deriv_value_iv(k - m, u)
        tot = tot + term
    return tot


def _u_box(slo, shi, ylo, yhi):
    ulo = Fr(ylo) / 2 - Fr(shi)
    uhi = Fr(yhi) / 2 - Fr(slo)
    return min(ulo, uhi), max(ulo, uhi)


def F_s_deriv_bound(k, slo, shi, ylo, yhi):
    """upper bound of |d^k/ds^k F(s,y)| on the box (product rule)."""
    ulo, uhi = _u_box(slo, shi, ylo, yhi)
    tot = ZERO
    for m in range(k + 1):
        tot += (Fr(binom(k, m)) * bump_D_bound(m, Fr(slo), Fr(shi))
                * bump_D_bound(k - m, ulo, uhi))
    return tot


def F_y_deriv_bound(k, slo, shi, ylo, yhi):
    """|d^k/dy^k F| on the box: dy = (1/2) du, factor 2^-k."""
    ulo, uhi = _u_box(slo, shi, ylo, yhi)
    tot = ZERO
    p = Fr(1) / Fr(2) ** k
    for m in range(k + 1):
        tot += (p * Fr(binom(k, m)) * bump_D_bound(m, Fr(slo), Fr(shi))
                * bump_D_bound(k - m, ulo, uhi))
    return tot


# ------------------------------------------------------------ partitions
GRID = Fr(1) / Fr(2) ** 20


def snap_down(f, bits=20):
    """largest multiple of 2^-bits not exceeding f (keeps cells finer)."""
    g = Fr(1) / Fr(2) ** bits
    return (f.numerator * (2 ** bits)) // f.denominator * g


def build_bands(smax, theta, vlo, vcap):
    """graded s-bands on [0, smax]; delta ~ theta / L(s) (theta ~ 0.3 so
    that (L*delta)^(V+1) is tiny for the Taylor order V), capped, snapped
    to the 2^-20 grid (all endpoints dyadic: no bignum denominator drift)."""
    bands = []
    s = ZERO
    L = lambda x: Fr(2) * x / Fr(1 - x * x) ** 2 if x > 0 else Fr(2)
    while s < smax:
        d = theta / L(s) if s > 0 else Fr(vcap)
        d = max(vlo, min(vcap, d))
        d = snap_down(d)
        if d <= 0:
            d = GRID
        if s + d > smax:
            d = snap_down(smax - s)
            if d <= 0:
                break
        bands.append((s, s + d))
        s += d
    return bands


def main():
    print("== 1220 probe v2: constants ==")
    piv = pi_iv()
    log2 = log_iv(2)
    giv = gamma_iv()
    q = exp_iv(IV(-4))
    # log tanh 2 = log(1-q) - log(1+q), q = e^-4 IV (monotone log)
    qlo, qhi = q.lo, q.hi
    ltm_lo = log_iv(1 - qhi).lo - log_iv(1 + qlo).hi
    ltm_hi = log_iv(1 - qlo).hi - log_iv(1 + qhi).lo
    log_tanh2 = IV(ltm_lo, ltm_hi)
    k4p = log_iv(4) + log_iv_of_iv(piv)
    kappa = k4p + giv + log_tanh2
    print("pi      width %.3e" % float(piv.width()))
    print("log 2   width %.3e" % float(log2.width()))
    print("gamma   width %.3e  (float %.15f)" % (float(giv.width()), float(giv.mid())))
    print("e^-4    width %.3e" % float(q.width()))
    print("logtanh2 width %.3e" % float(log_tanh2.width()))
    print("kappa   width %.3e  mid %.15f" % (float(kappa.width()), float(kappa.mid())))

    print()
    print("== sanity: gamma vs known 0.5772156649015329 ==")
    assert abs(float(giv.mid()) - 0.5772156649015329) < 1e-12
    print("OK")

    print()
    print("== bump ladder spot checks ==")
    # numeric check of ladder growth at s = 0.9 (float echo only)
    for k in (0, 2, 5, 10):
        bnd = bump_D_bound(k, Fr(9, 10) - Fr(1, 1000), Fr(9, 10) + Fr(1, 1000))
        print("k=%2d  bound on |b^(k)| near 0.9: %.3e" % (k, float(bnd)))

    print()
    print("== partitions sizing (theta scan) ==")
    for th in ("0.2", "0.3", "0.45"):
        theta = Fr(th)
        bands = build_bands(Fr(98, 100), theta, Fr(1, 5000), Fr(1, 50))
        print("theta=%s  s-bands on [0,0.98]: %d" % (th, len(bands)))




# =================================================================
# Part 2: exact moments, models, assembly
# =================================================================

# ---------- interval-coefficient polynomials (lists of IV, index = power) --
def ivp_add(p, q):
    n = max(len(p), len(q))
    out = []
    for i in range(n):
        a = p[i] if i < len(p) else IV(0)
        b = q[i] if i < len(q) else IV(0)
        out.append(a + b)
    return out


def ivp_scale(p, c):
    return [pi.scale(c) for pi in p]


def ivp_mul(p, q):
    out = [IV(0)] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            out[i + j] = out[i + j] + a * b
    return out


def ivp_int_centered(p, c, y0, y1):
    """exact integral over [y0,y1] of a poly given in powers of (y-c)."""
    acc = IV(0)
    for n, cn in enumerate(p):
        d0 = Fr(y0) - c
        d1 = Fr(y1) - c
        val = (d1 ** (n + 1) - d0 ** (n + 1)) / (n + 1)
        acc = acc + cn * IV(val)
    return acc


def ivp_shift_plain(p, c):
    """re-index a poly given in plain powers of y into powers of (y-c)."""
    out = [IV(0)] * len(p)
    for n, cn in enumerate(p):
        for k in range(n + 1):
            out[k] = out[k] + cn * IV(Fr(binom(n, k)) * Fr(c) ** (n - k))
    return out


def ivp_eval_iv(p, c, x):
    """evaluate centered poly at an interval x (offsets from c)."""
    acc = IV(0)
    pw = IV(1)
    for cn in p:
        acc = acc + cn * pw
        pw = pw * x
    return acc


# ---------- LogExpr (exact: rational + signed log-atoms) ------------------
class LogExpr:
    """exact value  c0 + sum_i w_i log(q_i)  (all rationals)."""

    __slots__ = ("c0", "terms")

    def __init__(self, c0=ZERO, terms=None):
        self.c0 = Fr(c0)
        self.terms = dict(terms or {})

    def __add__(self, o):
        if isinstance(o, Fr):
            return LogExpr(self.c0 + o, self.terms)
        t = dict(self.terms)
        for q, w in o.terms.items():
            nw = t.get(q, ZERO) + w
            if nw == 0:
                t.pop(q, None)
            else:
                t[q] = nw
        return LogExpr(self.c0 + o.c0, t)

    __radd__ = __add__

    def __sub__(self, o):
        if isinstance(o, Fr):
            return LogExpr(self.c0 - o, self.terms)
        t = dict(self.terms)
        for q, w in o.terms.items():
            nw = t.get(q, ZERO) - w
            if nw == 0:
                t.pop(q, None)
            else:
                t[q] = nw
        return LogExpr(self.c0 - o.c0, t)

    def __rsub__(self, o):
        return LogExpr(Fr(o), {}) - self

    def scale(self, c):
        c = Fr(c)
        return LogExpr(self.c0 * c, {q: w * c for q, w in self.terms.items()})

    __mul__ = scale
    __rmul__ = scale

    def enclose(self):
        acc_lo = self.c0
        acc_hi = self.c0
        for q, w in self.terms.items():
            li = log_iv(q)
            if w >= 0:
                acc_lo += w * li.lo
                acc_hi += w * li.hi
            else:
                acc_lo += w * li.hi
                acc_hi += w * li.lo
        return IV(acc_lo, acc_hi)


def enclose_scaled(le, ec):
    """value of (e^-c * le) where le is exact LogExpr and ec an interval
    containing the true e^-c >= 0."""
    X = le.enclose()
    return X * ec


# ---------- exact moments I(m,k) ------------------------------------------
_MOM = {}


def mom_I(m, k, a, b):
    """int_a^b s^m (1-s^2)^-k ds, exact LogExpr."""
    key = (m, k, a, b)
    r = _MOM.get(key)
    if r is not None:
        return r
    a = Fr(a)
    b = Fr(b)
    if a == b:
        r = LogExpr()
    elif k == 0:
        r = LogExpr((b ** (m + 1) - a ** (m + 1)) / (m + 1))
    elif m >= 2:
        # s^2 z^k = z^(k-1) - z^k
        r = mom_I(m - 2, k - 1, a, b) - mom_I(m - 2, k, a, b)
    elif m == 1:
        if k >= 2:
            za = Fr(1) / Fr((1 - a * a) ** (k - 1))
            zb = Fr(1) / Fr((1 - b * b) ** (k - 1))
            r = LogExpr((za - zb) / (2 * (k - 1)))
        else:
            la = LogExpr(ZERO, {1 - a * a: Fr(-1, 2)})
            lb = LogExpr(ZERO, {1 - b * b: Fr(-1, 2)})
            r = lb - la
    else:  # m == 0
        if k == 1:
            # artanh(b) - artanh(a) = 1/2 [log((1+b)/(1-b)) - log((1+a)/(1-a))]
            tb = LogExpr(1 + b, {1 - b: -1})
            ta = LogExpr(1 + a, {1 - a: -1})
            r = (tb - ta).scale(Fr(1, 2))
        else:
            za = a / Fr((1 - a * a) ** (k - 1))
            zb = b / Fr((1 - b * b) ** (k - 1))
            r = mom_I(0, k - 1, a, b).scale(Fr(2 * k - 1, 2 * (k - 1)))                 - LogExpr((zb - za) / (2 * (k - 1)))
    _MOM[key] = r
    return r


# ---------- bump model per s-ring ------------------------------------------
# b(s) = e^-z, z = 1/(1-s^2) in [zlo,zhi]; Taylor at c=(zlo+zhi)/2 to order
# N with N >= zhi + 2 so the partial sum A(z) = sum (-1)^n (z-c)^n / n! is
# decreasing and positive on [zlo,zhi]; then
#   e^-z in [A(zhi)*ec.lo - err, A(zlo)*ec.hi + err],  ec = e^-c interval.
class ZModel:
    __slots__ = ("r0", "r1", "zlo", "zhi", "c", "N", "ec", "err")

    def __init__(self, r0, r1, N=None):
        self.r0 = Fr(r0)
        self.r1 = Fr(r1)
        z1 = Fr(1) / Fr(1 - self.r0 * self.r0)
        z2 = Fr(1) / Fr(1 - self.r1 * self.r1)
        self.zlo, self.zhi = min(z1, z2), max(z1, z2)
        self.c = (self.zlo + self.zhi) / 2
        self.N = N if N is not None else int(self.zhi) + 6
        self.ec = exp_iv(IV(-self.c))
        half = (self.zhi - self.zlo) / 2
        emax = exp_iv(IV(-self.zlo)).hi
        self.err = emax * half ** (self.N + 1) / fact(self.N + 1)

    def A(self, z):
        """partial Taylor sum (scaled by e^c): sum (-1)^n (z-c)^n/n!."""
        acc = ONE
        d = z - self.c
        pw = ONE
        for n in range(1, self.N + 1):
            pw *= d
            acc += pw / fact(n) * (ONE if n % 2 == 0 else -ONE)
        return acc

    def enclosure(self):
        return IV(self.A(self.zhi) * self.ec.lo - self.err,
                  self.A(self.zlo) * self.ec.hi + self.err)


def poly_deriv_sup(p, x0, x1):
    """sup |p(x)| on [x0,x1] for an exact rational poly (dict) via
    interval evaluation (valid overestimate)."""
    if not p:
        return ZERO
    x0 = Fr(x0)
    x1 = Fr(x1)
    xlo, xhi = min(x0, x1), max(x0, x1)
    acc = IV(0)
    pw_lo = IV(1)
    # evaluate with interval x
    X = IV(xlo, xhi)
    pw = IV(1)
    tot = IV(0)
    for e in range(max(p) + 1):
        c = p.get(e, ZERO)
        if c:
            tot = tot + IV(c) * pw
        pw = pw * X
    return max(abs(tot.lo), abs(tot.hi))


LEG_DER_SUP_CACHE = {}
PB_DER_CACHE = {}


def leg_der_sup(j, x0, x1):
    """sup |P_j^(j)| on [x0,x1] (j-th derivative of Legendre j is const)."""
    key = (j, Fr(x0), Fr(x1))
    r = LEG_DER_SUP_CACHE.get(key)
    if r is None:
        r = poly_deriv_sup(leg_der(LEG[j], j), x0, x1)
        LEG_DER_SUP_CACHE[key] = r
    return r


def pb_der_parts(j, n, u0, u1):
    """sup over [u0,u1] of each piece needed for |Pb_j^(n)|:
    returns sum_m binom(n,m) * sup|P_j^(m)| * bar{b}^{(n-m)}."""
    key = (j, n, Fr(u0), Fr(u1))
    cached = PB_DER_CACHE.get(key)
    if cached is not None:
        return cached
    tot = ZERO
    for m in range(n + 1):
        s_m = poly_deriv_sup(leg_der(LEG[j], m), u0, u1)
        if s_m == 0:
            continue
        b_nd = bump_D_bound(n - m, u0, u1)
        tot += Fr(binom(n, m)) * s_m * b_nd
    PB_DER_CACHE[key] = tot
    return tot


# ---------- ring partitions and b^2 / b models -----------------------------
def build_rings(smax, theta, vlo, vcap, s_tay, s_max):
    """graded rings on [0, s_tay] (Taylor zone) + coarse rings up to s_max."""
    bands = build_bands(s_tay, theta, vlo, vcap)
    # coarse hybrid rings
    r = s_tay
    coarse = []
    step = Fr(1, 100)
    while r < s_max:
        d = min(step, s_max - r)
        coarse.append((r, r + d))
        r += d
    return bands, coarse


def bump2_rings(rings):
    """ZModels for b^2 = e^{-2z} on each ring."""
    out = []
    for (r0, r1) in rings:
        z1 = Fr(1) / Fr(1 - Fr(r0) ** 2)
        z2 = Fr(1) / Fr(1 - Fr(r1) ** 2)
        zlo, zhi = min(z1, z2), max(z1, z2)
        c = (zlo + zhi) / 2
        N = 2 * int(zhi) + 8
        ec = exp_iv(IV(-2 * c))
        half = (zhi - zlo) / 2
        emax = exp_iv(IV(-2 * zlo)).hi
        err = emax * (2 * half) ** (N + 1) / fact(N + 1)
        out.append(("b2", r0, r1, zlo, zhi, c, N, ec, err))
    return out


def A_partial(c, N, z, scale):
    """partial Taylor sum  sum_{n<=N} (-scale)^n (z-c)^n / n!, so that
    e^{-scale*z} = e^{-scale*c} * A + remainder.  A(z) must be positive
    and decreasing on the z-ring (checked by assertions)."""
    acc = ONE
    d = Fr(z) - c
    pw = ONE
    for n in range(1, N + 1):
        pw *= d
        t = pw / fact(n)
        if n % 2 == 1:
            t = -t
        acc += t * (Fr(scale) ** n)
    return acc


# ---------- entry assembly --------------------------------------------------
def gram_entry_C0(i, j, rings_b2, s_max):
    """C_ij(0) = 4 int_0^1 P_i P_j b^2 ds, via b^2 ring models + tail."""
    li = LEG[i]
    lj = LEG[j]
    acc = IV(0)
    tail = ZERO
    for tag, r0, r1, zlo, zhi, c, N, ec, err in rings_b2:
        # model: b^2 in [A(zhi)*ec.lo - err, A(zlo)*ec.hi + err]
        Az_hi = A_partial(c, N, zhi, 2)
        Az_lo = A_partial(c, N, zlo, 2)
        assert 0 < Az_hi <= Az_lo, (float(Az_hi), float(Az_lo))
        lo = Az_hi * ec.lo - err
        hi = Az_lo * ec.hi + err
        # int_{r0}^{r1} P_i P_j b^2 ds in [poly*lo, poly*hi] if poly >= 0
        poly = LogExpr()
        pw = [ONE]
        # coefficient of s^m in P_i*P_j
        coef = [ZERO] * (max(li) + max(lj) + 2)
        for e1, c1 in li.items():
            for e2, c2 in lj.items():
                coef[e1 + e2] += c1 * c2
        for m, cm in enumerate(coef):
            if cm == 0:
                continue
            poly = poly + mom_I(m, 0, r0, r1).scale(cm)
        P = poly.enclose()
        # poly can change sign: multiply interval-wise
        vals = (P * IV(lo, hi))
        acc = acc + vals
    # tail beyond s_max: |P_iP_j| <= 64-ish, b^2 <= exp(-2 z(s_max))
    supij = ZERO
    for e1, c1 in li.items():
        for e2, c2 in lj.items():
            supij += abs(c1 * c2)
    zmax = Fr(1) / Fr(1 - Fr(s_max) ** 2)
    b2sup = exp_iv(IV(-2 * zmax)).hi
    tail = supij * b2sup * (1 - Fr(s_max))
    return IV(acc.lo * 4 - 4 * tail, acc.hi * 4 + 4 * tail)


# ---------- yW kernel:  W(y) = 2 e^{y/2} / (e^y - e^{-y}) -------------------
#   H(y) = W(y)*(C(y) - C0) + B(y)*C0   with  B = W*(1 - e^{-y/2}),
#   yW(y) = y*W(y) = y/(2 sinh(y/2)) + y/(2 cosh(y/2))  is smooth, yW(0)=1.
Y_MAL = Fr(7, 10)   # cells with y1 <= Y_MAL use the Maclaurin branch

_EULER = [Fr(1)]


def euler_even(n):
    """E_{2n} of the sech generating function (E0=1, E2=-1, E4=5, ...)."""
    global _EULER
    while len(_EULER) <= n:
        m = len(_EULER)
        s = Fr(0)
        for jj in range(m):
            s += Fr(binom(2 * m, 2 * jj)) * _EULER[jj]
        _EULER.append(-s)
    return _EULER[n]


_YW_MAL = None


def yw_maclaurin():
    """yW as a plain-power poly on [0, Y_MAL] + uniform tail bound.
    y/(2 sinh(y/2)) = sum_k c_k (y/2)^(2k), c_k = (2-2^(2k)) B_{2k}/(2k)!;
    y/(2 cosh(y/2)) = sum_j E_{2j} (y/2)^(2j+1) / (2j)!.
    Term bounds (t = y/2): |c_k| t^(2k) <= (10/3) (t/pi)^(2k)  [zeta <= 5/3],
    |E_{2j}| t^(2j+1)/(2j)! <= 4t (4t^2/pi^2)^j  [Dirichlet beta <= 1]."""
    global _YW_MAL
    if _YW_MAL is not None:
        return _YW_MAL
    N1 = 14
    N2 = 14
    deg = max(2 * N1, 2 * N2 + 1)
    coeffs = [IV(0)] * (deg + 1)
    for k in range(N1 + 1):
        ck = (2 - Fr(2) ** (2 * k)) * bernoulli(2 * k) / fact(2 * k)
        coeffs[2 * k] = coeffs[2 * k] + IV(ck / Fr(2) ** (2 * k))
    for jj in range(N2 + 1):
        Ej = euler_even(jj)
        coeffs[2 * jj + 1] = coeffs[2 * jj + 1] + IV(
            Ej / (fact(2 * jj) * Fr(2) ** (2 * jj + 1)))
    t = Y_MAL / 2
    pil = pi_iv().lo
    r1 = (t / pil) ** 2
    tail1 = Fr(10, 3) * r1 ** (N1 + 1) / (1 - r1)
    r2 = 4 * t * t / (pil * pil)
    tail2 = 4 * t * r2 ** (N2 + 1) / (1 - r2)
    _YW_MAL = (coeffs, IV(tail1 + tail2))
    return _YW_MAL


def yw_moments_cell(y0, y1, kmax):
    """Zk[k] = int_{y0}^{y1} (y-yhat)^k * yW(y) dy for k <= kmax (intervals,
    all model tails folded in).  Maclaurin branch on y1 <= Y_MAL; else the
    geometric series yW = 2 y sum_{j>=0} e^{-(4j+1)y/2} (needs y0 > 0)."""
    y0 = Fr(y0)
    y1 = Fr(y1)
    yhat = (y0 + y1) / 2
    d0 = y0 - yhat
    d1 = y1 - yhat
    MM = kmax + 212
    M = [(d1 ** (k + 1) - d0 ** (k + 1)) / (k + 1) for k in range(MM)]
    Ms = [abs(m) for m in M]
    Sabs = [(abs(d1) ** (k + 1) + abs(d0) ** (k + 1)) / (k + 1)
            for k in range(kmax + 1)]
    out = [IV(0) for _ in range(kmax + 1)]
    if y1 <= Y_MAL:
        coeffs, tailw = yw_maclaurin()
        coeffs = ivp_shift_plain(coeffs, yhat)   # plain powers -> (y - yhat)
        for n, cn in enumerate(coeffs):
            if n > MM - kmax - 2:
                break
            for k in range(kmax + 1):
                out[k] = out[k] + cn * IV(M[k + n])
        for k in range(kmax + 1):
            e = tailw.hi * sum(Ms[k:k + len(coeffs)])
            out[k] = IV(out[k].lo - e, out[k].hi + e)
        return yhat, out
    assert y0 > 0, "geometric yW branch needs y0 > 0"
    err_tot = Fr(0)
    j = 0
    while True:
        lam = Fr(4 * j + 1, 2)
        head = exp_iv(IV(-lam * y0)).hi
        if head * 2 * y1 * (y1 - y0) <= Fr(1, 10 ** 24):
            break
        N_t = 24
        while True:
            rem = head * (lam * (y1 - y0) / 2) ** (N_t + 1) / fact(N_t + 1)
            if rem <= Fr(1, 10 ** 22) or N_t >= 200:
                break
            N_t += 16
        err_tot += rem
        E = exp_iv(IV(-lam * yhat))
        for k in range(kmax + 1):
            acc = IV(0)
            for n in range(N_t + 1):
                cn = E * IV((-lam) ** n / fact(n))
                acc = acc + cn * (IV(yhat) * IV(M[k + n]) + IV(M[k + n + 1]))
            out[k] = out[k] + acc.scale(2)
        j += 1
    lam0 = Fr(4 * j + 1, 2)
    head0 = exp_iv(IV(-lam0 * y0)).hi
    gt = 2 * y1 * head0 / (1 - exp_iv(IV(-2 * y0)).hi) * (y1 - y0)
    for k in range(kmax + 1):
        e = (err_tot + gt) * Sabs[k]
        out[k] = IV(out[k].lo - e, out[k].hi + e)
    return yhat, out


_IB = None


def I_B_global():
    """int_0^4 B(y) dy,  B = W*(1 - e^{-y/2}) = yW * htilde,
    htilde(y) = (1 - e^{-y/2})/y = sum_{m>=1} (-1)^(m+1) y^(m-1)/(2^m m!).
    [0, Y_MAL]: product poly + cross-tail;  [Y_MAL, 4]: termwise exponentials
    B = 2 sum_j (e^{-lam_j y} - e^{-(lam_j+1) y}), lam_j = (4j+1)/2."""
    global _IB
    if _IB is not None:
        return _IB
    d, tailw = yw_maclaurin()
    N_h = 24
    h = [IV(0)] * N_h
    for m in range(1, N_h + 1):
        h[m - 1] = IV(Fr((-1) ** (m + 1), 2 ** m * fact(m)))
    htail = Fr(1) / Fr(2 ** (N_h + 1) * fact(N_h + 1))
    prod = ivp_mul(d, h)
    acc = IV(0)
    for n, cn in enumerate(prod):
        acc = acc + cn * IV(Y_MAL ** (n + 1) / (n + 1))
    hmax = Fr(1, 2)  # htilde decreases from 1/2 on [0, Y_MAL]
    dmax = ZERO
    pw = ONE
    for cn in d:
        dmax += max(abs(cn.lo), abs(cn.hi)) * pw
        pw *= Y_MAL
    cross = (tailw.hi * hmax + htail * dmax + tailw.hi * htail) * Y_MAL
    acc = IV(acc.lo - cross, acc.hi + cross)
    acc2 = IV(0)
    j = 0
    while True:
        lam = Fr(4 * j + 1, 2)
        if exp_iv(IV(-lam * Y_MAL)).hi * 2 / lam <= Fr(1, 10 ** 24):
            break
        e1 = exp_iv(IV(-lam * Y_MAL)) - exp_iv(IV(-lam * 4))
        mu = lam + Fr(1, 2)   # B = W*(1-e^{-y/2}): shift by 1/2, not 1
        e2 = exp_iv(IV(-mu * Y_MAL)) - exp_iv(IV(-mu * 4))
        acc2 = acc2 + (e1 * IV(1 / lam) - e2 * IV(1 / mu)).scale(2)
        j += 1
    lam0 = Fr(4 * j + 1, 2)
    head0 = exp_iv(IV(-lam0 * Y_MAL)).hi
    gt = 2 * head0 / (1 - exp_iv(IV(-2 * Y_MAL)).hi) * 2 / lam0
    _IB = acc + acc2 + IV(-gt, gt)
    return _IB


def leg_neg_coeffs(i):
    """coefficients of P_i(-s) as a dense list."""
    pi = LEG[i]
    out = [ZERO] * (max(pi) + 1 if pi else 1)
    for e, c in pi.items():
        out[e] = c * ((-1) ** e)
    return out


# ---------- global bump models ---------------------------------------------
S_MAX = Fr(99, 100)          # |s| beyond this: b <= e^-50, pure tail
ZM_B = None                  # global z-model for b   on |s| <= S_MAX
ZM_B2 = None                 # global z-model for b^2 on |s| <= S_MAX


def zpoly_coeffs(zm):
    """coefficients of the z-poly  sum_j zp[j] z^j  equal to sum_n
    (-1)^n (z-c)^n / n!  (the e^c-scaled Taylor partial sum)."""
    zp = [ZERO] * (zm.N + 1)
    for n in range(zm.N + 1):
        pw = [ZERO] * (n + 1)
        pw[0] = ONE
        cur = ONE
        for t in range(n):
            # (z-c)^(t+1) = (z-c)^t * (z-c)
            nxt = [ZERO] * (t + 2)
            for e2 in range(t + 1):
                nxt[e2] += pw[e2] * (-zm.c)
                nxt[e2 + 1] += pw[e2]
            pw = nxt
        sgn = ONE if n % 2 == 0 else -ONE
        for j in range(n + 1):
            zp[j] += sgn * pw[j] / fact(n)
    return zp


def init_models():
    global ZM_B, ZM_B2
    # z = 1/(1-s^2) spans [1, 1/(1-S_MAX^2)] for |s| <= S_MAX
    ZM_B = ZModel(Fr(0), S_MAX)
    ZM_B.N = 160
    ZM_B.err = exp_iv(IV(-ZM_B.zlo)).hi * ((ZM_B.zhi - ZM_B.zlo) / 2) ** 161 / fact(161)
    ZM_B2 = ZModel(Fr(0), S_MAX)
    # for b^2 = e^{-2z} the enclosure formula uses scale-2 Taylor; the err
    # below uses the (2*half)-Lagrange form with e^{-2 zlo}
    ZM_B2.N = 300
    ec2 = exp_iv(IV(-2 * ZM_B2.c))
    ZM_B2.ec = ec2
    ZM_B2.err = exp_iv(IV(-2 * ZM_B2.zlo)).hi * (ZM_B2.zhi - ZM_B2.zlo) ** 301 / fact(301)


def band_raw_moments(i, a, b, tmax, zm):
    """R[t] = int_a^b P_i(-s) bump_model(s) (s - cB)^t ds  for t <= tmax,
    where cB = (a+b)/2;  each R[t] is (LogExpr, ec-interval)."""
    cB = (Fr(a) + Fr(b)) / 2
    li = leg_neg_coeffs(i)
    zp = zpoly_coeffs(zm)
    # cache of mom_I per (m, j)
    mmax = (len(li) - 1) + tmax if li else tmax
    Q = {}
    out = []
    for t in range(tmax + 1):
        # coeff of s^m in P_i(-s) (s-cB)^t
        pw = [ONE]
        for _ in range(t):
            nxt = [ZERO] * (len(pw) + 1)
            for e2, c2 in enumerate(pw):
                nxt[e2] += c2 * (-cB)
                nxt[e2 + 1] += c2
            pw = nxt
        coef = [ZERO] * (len(pw) + (len(li) if li else 0))
        for e1, c1 in enumerate(li):
            if c1 == 0:
                continue
            for e2, c2 in enumerate(pw):
                coef[e1 + e2] += c1 * c2
        le = LogExpr()
        for m, cm in enumerate(coef):
            if cm == 0:
                continue
            for j, zj in enumerate(zp):
                if zj == 0:
                    continue
                key = (m, j)
                q = Q.get(key)
                if q is None:
                    q = mom_I(m, j, a, b)
                    Q[key] = q
                le = le + q.scale(cm * zj)
        out.append((le, zm.ec))
    return out


# ---------- u-Taylor coefficients at a point --------------------------------
def pb_coef_iv(j, n, u_c):
    """Pb_j^(n)(u_c) / n!  as an interval (tight): e^{-z(u_c)} times an
    exact rational combination."""
    uc = Fr(u_c)
    acc = IV(0)
    for m in range(n + 1):
        # P_j^(m)(u_c) exact rational
        pm = Fr(poly_eval_exact(leg_der(LEG[j], m), uc))
        if pm == 0:
            continue
        acc = acc + bump_deriv_value_iv(n - m, uc).scale(pm * Fr(binom(n, m)))
    return acc.scale(Fr(1, fact(n)))


def poly_eval_exact(p, x):
    acc = ZERO
    pw = ONE
    for e in range(max(p) + 1 if p else 0):
        c = p.get(e, ZERO)
        acc += c * pw
        pw *= x
    return acc


# ---------- entry pipeline --------------------------------------------------
P24 = [(2,2),(3,3),(4,2),(5,5),(7,7),(8,2),(9,3),(11,11),(13,13),
       (16,2),(17,17),(19,19),(23,23),(25,5),(27,3),(29,29),(31,31),
       (32,2),(37,37),(41,41),(43,43),(47,47),(49,7),(53,53)]

NU_CAP = 22
PAIR_SKIP = Fr(1, 10 ** 18)   # pair total-contribution below this: skipped
REM_TARGET = Fr(1, 10 ** 14)  # per-leaf estimated u-Taylor remainder


def sqrt_iv(n, bits=100):
    """sqrt(n) for integer n via exact rational bisection sandwich."""
    n = int(n)
    a = 0
    while (a + 1) ** 2 <= n:
        a += 1
    lo = Fr(a)
    hi = Fr(a + 1)
    for _ in range(bits):
        m = (lo + hi) / 2
        if m * m <= n:
            lo = m
        else:
            hi = m
    return IV(lo, hi)


def build_s_bands():
    """graded bands on (0, S_TAY] + coarse bands to S_MAX; mirrored."""
    s_tay = Fr(24, 25)   # 0.96: Taylor zone
    graded = build_bands(s_tay, Fr(3, 10), Fr(1, 5000), Fr(1, 50))
    coarse = []
    r = s_tay
    while r < S_MAX:
        d = min(Fr(1, 100), S_MAX - r)
        coarse.append((r, r + d))
        r += d
    bands = graded + coarse
    return bands


_S_BANDS = None
_RINGS_B2 = None
_C0_CACHE = {}
_RAW_MOM_CACHE = {}
_YP_CACHE = {}
_PB_CACHE = {}


def _frac_text(s):
    return Fr(s)


def _checkpoint_write(path, payload):
    import json
    from pathlib import Path
    target = Path(path)
    tmp = target.with_suffix(target.suffix + ".tmp")
    tmp.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    tmp.replace(target)


def _unlock_int_str_digits():
    # entry endpoints carry 1e4-1e6 digit denominators; CPython 3.11+ caps
    # int->str at 4300 digits (CVE-2020-10735), so the exact-rational
    # checkpoint serialization would raise ValueError at the print site.
    # 0 disables the cap.  Serialization-only: no enclosure is affected.
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(0)


def _ensure_models():
    """lazy shared-model init (hoisted from entry_box for the parallel driver)."""
    global _S_BANDS, _RINGS_B2
    if _S_BANDS is None:
        _S_BANDS = build_s_bands()
    if _RINGS_B2 is None:
        _RINGS_B2 = bump2_rings([(0, S_MAX)])
        _RINGS_B2[0] = _RINGS_B2[0][:6] + (220,) + _RINGS_B2[0][7:]


def entry_box(i, j, kappa, log_ivals, ib, verbose=False, bands=None):
    """assemble the entry interval  kappa*C0 + int_0^4 H + C0*int B;
    H-integral via the bracket form int W (C - C0) over a joint adaptive
    (y, s) partition per (sign, s-band).
    bands=None -> all s-bands; else a caller-chosen slice (parallel driver)."""
    _ensure_models()
    bands = _S_BANDS if bands is None else bands
    C0 = _C0_CACHE.get((i, j))
    if C0 is None:
        C0 = gram_entry_C0(i, j, _RINGS_B2, S_MAX)
        _C0_CACHE[(i, j)] = C0

    def Lfun(x):
        return Fr(2) * x / (Fr(1) - x * x) ** 2 if x > 0 else Fr(2)

    yp_cache = _YP_CACHE
    totalH = IV(0)
    slack = Fr(0)
    nleaf = [0]
    nu = NU_CAP
    for sign in (1, -1):
        for (a, b) in bands:
            # pre-split at Y_MAL: the Maclaurin branch of yw_moments_cell
            # needs y1 <= Y_MAL and the geometric branch needs y0 > 0, so no
            # cell may straddle Y_MAL (bisections preserve the invariant)
            stack = [(Fr(0), Y_MAL, Fr(a), Fr(b)),
                     (Y_MAL, Fr(4), Fr(a), Fr(b))]
            while stack:
                y0, y1, s0, s1 = stack.pop()
                ds = s1 - s0
                dy = y1 - y0
                u0 = y0 / 2 - s1
                u1 = y1 / 2 - s0
                ucl0 = max(u0, -S_MAX)
                ucl1 = min(u1, S_MAX)
                if ucl0 > ucl1:
                    continue
                bs = bump_hi(s0, s1)
                bu = bump_hi(ucl0, ucl1)
                scale = bs * bu * ds * dy * 512
                if scale <= PAIR_SKIP:
                    slack = slack + scale
                    continue
                hw = dy / 4 + ds / 2
                umax = max(abs(ucl0), abs(ucl1))
                Lh = Lfun(umax)
                est = scale * (Lh * hw) ** (nu + 1) / fact(nu + 1) * 30
                floor_hit = (dy <= Fr(1, 4096)) and (ds <= GRID)
                if est > REM_TARGET and not floor_hit:
                    if dy / 4 >= ds / 2:
                        m = (y0 + y1) / 2
                        stack.append((y0, m, s0, s1))
                        stack.append((m, y1, s0, s1))
                    else:
                        m = (s0 + s1) / 2
                        stack.append((y0, y1, s0, m))
                        stack.append((y0, y1, m, s1))
                    continue
                nleaf[0] += 1
                yhat = (y0 + y1) / 2
                cB = (s0 + s1) / 2
                # Yp[p] = int_cell y^p W dy (p = 1..nu), from Zk of yW
                YP = yp_cache.get((y0, y1))
                if YP is None:
                    _, Zk = yw_moments_cell(y0, y1, nu + 2)
                    YP = [None]
                    for p in range(1, nu + 1):
                        acc = IV(0)
                        for c in range(p):
                            acc = acc + IV(Fr(binom(p - 1, c))
                                           * yhat ** (p - 1 - c)) * Zk[c]
                        YP.append(acc)
                    yp_cache[(y0, y1)] = YP
                # raw-moment enclosures per s-leaf (entry-dependent, cached)
                key = (s0, s1, i)
                RX = _RAW_MOM_CACHE.get(key)
                if RX is None:
                    _MOM.clear()
                    R = band_raw_moments(i, s0, s1, nu, ZM_B)
                    RX = [enclose_scaled(le, ec) for (le, ec) in R]
                    _RAW_MOM_CACHE[key] = RX
                pb = []
                for n in range(nu + 1):
                    pkey = (j, n, yhat / 2 - cB)
                    value = _PB_CACHE.get(pkey)
                    if value is None:
                        value = pb_coef_iv(j, n, yhat / 2 - cB)
                        _PB_CACHE[pkey] = value
                    pb.append(value)
                # honest u-Taylor truncation bound: |w^n - w0^n| <= n hw^(n-1) y/2
                t1 = pb_der_parts(j, nu + 1, ucl0, ucl1) * 2 * hw ** (nu + 1) / fact(nu + 1)
                t2 = pb_der_parts(j, nu + 2, ucl0, ucl1) * 2 * hw ** (nu + 2) / fact(nu + 2)
                rho = t2 / t1 if t1 > 0 else Fr(0)
                rem_tail = t1 / (1 - rho) if rho < 1 else t1 + 2 * t2
                # pair-level error, y-weighted: <= 1.2 bs ds dy (nu+1) t1 / (hw (1-rho))
                rem_pair = Fr(6, 5) * bs * ds * dy * (nu + 1) * rem_tail / hw
                # pair contribution: 2 sum_n pb[n] sum_p binom(n,p) 2^-p Yp[p] Mr[n-p]
                tot = IV(0)
                Mr_cache = {}
                for n in range(1, nu + 1):
                    inner = IV(0)
                    for p in range(1, n + 1):
                        q = n - p
                        Mr = Mr_cache.get(q)
                        if Mr is None:
                            acc = IV(0)
                            for t in range(q + 1):
                                # w0^q = (-1)^q ((s-cB) + yhat/2)^q
                                cc = Fr(binom(q, t)) * (yhat / 2) ** (q - t)
                                if q % 2 == 1:
                                    cc = -cc
                                acc = acc + RX[t].scale(cc)
                            Mr = acc
                            Mr_cache[q] = Mr
                        inner = inner + IV(Fr(binom(n, p)) / 2 ** p) * YP[p] * Mr
                    tot = tot + pb[n] * inner
                totalH = totalH + tot.scale(2) + IV(-rem_pair, rem_pair)
    if verbose:
        print("  leaves: %d   skipped-slack: %.3e" % (nleaf[0], float(slack)))
    entry = kappa * C0 + totalH + C0 * ib
    return entry, C0, totalH, slack


_RBAND = {}


def main2():
    import json
    _unlock_int_str_digits()
    print("== 1220 probe v2: entry assembly ==")
    init_models()
    piv = pi_iv()
    giv = gamma_iv()
    q = exp_iv(IV(-4))
    lt = IV(log_iv(1 - q.hi).lo - log_iv(1 + q.lo).hi,
            log_iv(1 - q.lo).hi - log_iv(1 + q.hi).lo)
    kappa = log_iv(4) + log_iv_of_iv(piv) + giv + lt
    print("kappa mid %.15f width %.2e" % (float(kappa.mid()), float(kappa.width())))

    # band sizing echo
    bands = build_s_bands()
    print("s-bands (both zones, one side): %d" % len(bands))

    # 1217 committed boxes
    with open("docs/proofs/1217_m_boxes_cert.json", encoding="utf-8") as f:
        cert = json.load(f)

    ib = I_B_global()
    print("I_B mid %.15f width %.2e" % (float(ib.mid()), float(ib.width())))

    import os
    requested = os.environ.get("PROBE_ENTRY", "0,0;7,7")
    entries = []
    for token in requested.split(";"):
        i_text, j_text = token.split(",")
        entries.append((int(i_text), int(j_text)))
    checkpoint_path = os.environ.get(
        "PROBE_CHECKPOINT", "docs/proofs/1220_entrywise_checkpoint.json")
    checkpoint = {"mode": "single-entry-checkpoint", "entries": {}}
    from pathlib import Path
    if Path(checkpoint_path).exists():
        with open(checkpoint_path, encoding="utf-8") as f:
            checkpoint = json.load(f)

    for (i, j) in entries:
        key = "%d,%d" % (i, j)
        if key in checkpoint.get("entries", {}):
            print("entry (%d,%d): cached checkpoint" % (i, j), flush=True)
            continue
        print("entry (%d,%d): begin" % (i, j), flush=True)
        entry, C0, H, slack = entry_box(i, j, kappa, None, ib, verbose=True)
        box = cert["entries"][key]
        lo = _frac_text(box["lo"])
        hi = _frac_text(box["hi"])
        ok = (entry.lo >= lo) and (entry.hi <= hi)
        print("entry (%d,%d): [%.15f, %.15f] width %.3e" %
              (i, j, float(entry.lo), float(entry.hi), float(entry.width())))
        print("  box  (%s): [%.15f, %.15f] width %.3e  margin_in=%s" %
              (key, float(lo), float(hi), float(hi - lo), ok))
        print("  C0 mid %.15f  H mid %.15f" % (float(C0.mid()), float(H.mid())))
        checkpoint.setdefault("entries", {})[key] = {
            "lo": str(entry.lo), "hi": str(entry.hi),
            "width": str(entry.width()), "target_lo": str(lo),
            "target_hi": str(hi), "contained": ok,
            "C0_mid": str(C0.mid()), "H_mid": str(H.mid()),
            "slack": str(slack)
        }
        _checkpoint_write(checkpoint_path, checkpoint)


def _entry_worker(i, j, kappa, ib, band_slice, idx):
    """pool task: full sign loop over one interleaved band slice."""
    entry, C0, totalH, slack = entry_box(
        i, j, kappa, None, ib, verbose=True, bands=band_slice)
    return idx, totalH, slack


def _entry_worker_star(task_tuple):
    """imap_unordered passes ONE object per task; forward the unpacked
    tuple to _entry_worker (starmap semantics with streaming results)."""
    return _entry_worker(*task_tuple)


def main3():
    """parallel driver: fork-shared caches, workers per interleaved s-band
    slice.  Interval/Fraction addition is exact-associative, so the
    canonical-order sum of slice partials equals the sequential sum
    bit-for-bit; the leaf machinery is untouched."""
    import json
    import multiprocessing as mp
    _unlock_int_str_digits()
    from pathlib import Path
    sys.setrecursionlimit(100000)
    print("== 1220 probe v3: parallel driver ==", flush=True)
    init_models()
    piv = pi_iv()
    giv = gamma_iv()
    q = exp_iv(IV(-4))
    lt = IV(log_iv(1 - q.hi).lo - log_iv(1 + q.lo).hi,
            log_iv(1 - q.lo).hi - log_iv(1 + q.hi).lo)
    kappa = log_iv(4) + log_iv_of_iv(piv) + giv + lt
    print("kappa mid %.15f width %.2e" % (float(kappa.mid()), float(kappa.width())),
          flush=True)
    _ensure_models()
    bands = _S_BANDS
    print("s-bands (both zones, one side): %d" % len(bands), flush=True)
    with open("docs/proofs/1217_m_boxes_cert.json", encoding="utf-8") as f:
        cert = json.load(f)
    ib = I_B_global()
    print("I_B mid %.15f width %.2e" % (float(ib.mid()), float(ib.width())),
          flush=True)

    import os
    requested = os.environ.get("PROBE_ENTRY", "0,0;7,7")
    entries = []
    for token in requested.split(";"):
        i_text, j_text = token.split(",")
        entries.append((int(i_text), int(j_text)))
    workers = int(os.environ.get("PROBE_WORKERS", "12"))
    checkpoint_path = os.environ.get(
        "PROBE_CHECKPOINT", "docs/proofs/1220_entrywise_checkpoint.json")
    checkpoint = {"mode": "single-entry-checkpoint", "entries": {}}
    if Path(checkpoint_path).exists():
        with open(checkpoint_path, encoding="utf-8") as f:
            checkpoint = json.load(f)

    # prime C0 in the PARENT so fork shares it copy-on-write
    C0s = {}
    for (i, j) in entries:
        if (i, j) not in _C0_CACHE:
            _C0_CACHE[(i, j)] = gram_entry_C0(i, j, _RINGS_B2, S_MAX)
        C0s[(i, j)] = _C0_CACHE[(i, j)]

    slices = [bands[r::workers] for r in range(workers)]
    pool = mp.Pool(workers)
    print("pool: %d workers x %d slices" % (workers, len(slices)), flush=True)

    for (i, j) in entries:
        key = "%d,%d" % (i, j)
        if key in checkpoint.get("entries", {}):
            print("entry (%d,%d): cached checkpoint" % (i, j), flush=True)
            continue
        print("entry (%d,%d): begin (parallel)" % (i, j), flush=True)
        items = [(i, j, kappa, ib, sl, r) for r, sl in enumerate(slices)]
        totalH = IV(0)
        slack = Fr(0)
        for (idx, th, sk) in pool.imap_unordered(
                _entry_worker_star, items, chunksize=1):
            print("  worker %2d done" % idx, flush=True)
            totalH = totalH + th
            slack = slack + sk
        C0 = C0s[(i, j)]
        entry = kappa * C0 + totalH + C0 * ib
        box = cert["entries"][key]
        lo = _frac_text(box["lo"])
        hi = _frac_text(box["hi"])
        ok = (entry.lo >= lo) and (entry.hi <= hi)
        print("entry (%d,%d): [%.15f, %.15f] width %.3e" %
              (i, j, float(entry.lo), float(entry.hi), float(entry.width())))
        print("  box  (%s): [%.15f, %.15f] width %.3e  margin_in=%s" %
              (key, float(lo), float(hi), float(hi - lo), ok))
        print("  C0 mid %.15f  H mid %.15f" % (float(C0.mid()), float(totalH.mid())))
        checkpoint.setdefault("entries", {})[key] = {
            "lo": str(entry.lo), "hi": str(entry.hi),
            "width": str(entry.width()), "target_lo": str(lo),
            "target_hi": str(hi), "contained": ok,
            "C0_mid": str(C0.mid()), "H_mid": str(totalH.mid()),
            "slack": str(slack)
        }
        _checkpoint_write(checkpoint_path, checkpoint)
    pool.close()
    pool.join()


if __name__ == "__main__":
    # PROBE_DRIVER=seq selects the sequential v2 driver (S0 reference runs);
    # default is the parallel v3 driver.  Driver choice only: identical
    # per-entry numerics (bit-for-bit by exact-associativity of IV/Fr sums).
    import os as _os
    if _os.environ.get("PROBE_DRIVER", "par") == "seq":
        main2()
    else:
        main3()
