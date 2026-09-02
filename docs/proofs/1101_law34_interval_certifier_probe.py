"""Law-34 certified interval arch certifier (record 1101).

Rigorous evaluation of the `orbitWindowSemiLocalGate` functional
Q = arch + prime on EXPLICIT carrier functions f = coeffs @ basis
(legendre x smooth_bump or sine on [-a, a], exactly the 1100b carrier),
with every quadrature remainder bounded by a theorem-valid REGISTERED
formula (v2, pre-run amendment 1101 section 3.1): float64 REFERENCE
VALUES computed vectorized, certified by REGISTERED forward error
analysis (|fl - exact| <= 2^-52 * op-count * magnitude-sum tracked per
node and per leg), with all theorem remainders (ellipse, endpoint balls,
mesh Simpson, Taylor ladder) and the GL node/weight perturbation term
UNCHANGED from the v1 interval design; interval arithmetic (python-flint
`arb`, G-eng, REQUIRED, no fallback) drives the final assembly,
constants, and `IV.span` enclosures.  The certified widths are the same
class the v1 intervals produced (v1's h'''' interval at y = s0 was
~1e28-wide by engine rounding; v2's registered width is the same scale
by 2^-52 * term-magnitude -- both killed by the span^5 remainder).

Certified quantities per function:
  arch(f)  = C_ARCH * F0 + I_body + F0 * log(tanh a)     C_ARCH = log 4pi + gamma
  I_body   = int_0^{2a} h(y) dy,  h = (e^{y/2} F - F0)/sinh,  h(0) = F0/2
  F^(k)(y) = int_{-a}^{a-y} f(u) f^(k)(u+y) du
  prime(f) = 2 * sum_q (Lambda(q)/sqrt(q)) * F(log q)   (visible prime powers)

u-integration (certified; pre-registration table, eta = 0.02 per doc):
interior Gauss-Legendre core on x in [-1+eta, 1-eta-y/a] with the
ellipse remainder |E| <= 8 M_rho rho^{1-2n} / (rho^2-1), rho = 1 + 0.9
* eta/half, n_gl = 4096, and M_rho a CLOSED-FORM theorem bound (triangle
inequality + |1-z^2| >= Delta = 0.9 (2 eta - eta^2), |exp(-1/(1-z^2))|
<= exp(1/Delta), |poly(z)| <= P Rx^deg, |R_m(z)| <= N_m Rx^deg / Delta^{2m};
Delta and the bounds verified by G-mrho on the ellipse boundary); plus two
endpoint balls of width eta (legendre family only; the sine family is
entire and needs none) with |int| <= eta a B_0 B_k from the closed-form
pointwise bound B_k = bsup (1/a)^k sum_j C(k,j) P_j N_{k-j} (1.98 eta)^
{-2(k-j)}, bsup = exp(-1/(2 eta - eta^2)), sup-at-inner-edge REGISTERED
(eta = 0.02 < 1/32); plus the REGISTERED per-node GL node/weight
backward error 2^-53 a half sum_i w_i (a|x_i| |dH/dx|_i + |H|_i) with
|H|, |dH/dx| the _fvals per-node magnitudes at the same float64 nodes
(the v1 n*sup|H| worst-case form over-counts by up to 8 orders on
high-derivative-scale carriers -- section 3.1); plus the v2 forward-error
term 2^-52 * 9000 * (magnitude sum of the GL summation).

y-integration (certified): first cell [0, s0] (s0 = 2^-35) by the Taylor
ladder s0 h0 + s0^2 h1/2 + s0^3 h2/3 + s0^4 h3/4 with h0..h3 from
F0, F2 = -1/2 int (f')^2, F4 = 1/24 int (f'')^2 (series of N = e^{y/2}F
- F0 over sinh; the y^5 coefficient would need F^(6)(0) and is NOT used)
plus the 4th-order remainder s0^4 M4/24 with M4 = sup|h''''| on [0,s0] by
interval evals at 4 points, x a REGISTERED (1 + 4 s0) growth margin; the
body by composite Simpson on the adaptive mesh y_{j+1} = y_j (1+theta)
with per-cell remainder span^5 M4_cell / 90, M4_cell from interval h''''
evals at 3 nodes x a REGISTERED (1 + 16 theta) margin; theta is solved
from the certified-width target via the leading term 24 theta^5 / 90.

Gates: G-eng, G-deriv (f' containment + order-2 signature), G-mrho
(region bounds verified on the ellipse boundary), G-nest (halving theta
halves the certified width, nested), G-int (certified arch contains the
committed 1100b corrected float64 values, 1e-5 bias allowance), G-prime
(certified prime leg contains the float64 recomputation), G-rows
(moment/orthonormality, DISCARD class).

Pre-registration: 1101_law34_interval_certifier_preregistration.md
(committed before this run).  Numerical evidence with certified-interval
bounds; RH unclaimed; GATE 1 untouched.
"""

from __future__ import annotations

import importlib.util
import json
import math
import os
import sys
from fractions import Fraction

import numpy as np
from numpy.polynomial.legendre import leggauss
from scipy.linalg import eigh

# ---------------------------------------------------------------- G-eng
try:
    from flint import arb  # noqa: F401
    import flint as _flint
except Exception as exc:  # pragma: no cover
    sys.exit(f"ABORT: G-eng python-flint unavailable: {exc}")

_ENGINE_STR = ("0.57721566490153286060651209008240243104215933593992359880"
               "59767234884867267766646709369470632917467495146314472498"
               "0824824805048139380423")
_PI_STR = ("3.141592653589793238462643383279502884197169399375105820974944"
           "59230781640628620899862803482534211706798214808651328230664709"
           "384460955058223172535940812848")
if not (hasattr(arb(1.0), "exp") and hasattr(arb(1.0), "log")
        and hasattr(arb(1.0), "sinh") and hasattr(arb(1.0), "cosh")
        and hasattr(arb(1.0), "tanh")):
    sys.exit("ABORT: G-eng flint.arb missing method transcendentals")
print(f"G-eng: python-flint {getattr(_flint, '__version__', '?')} loaded")


# ------------------------------------------------------- interval wrapper
class IV:
    """Interval wrapper over flint.arb (directed rounding built in)."""

    __slots__ = ("iv",)

    def __init__(self, x):
        if isinstance(x, IV):
            self.iv = x.iv
        elif isinstance(x, arb):
            self.iv = x
        elif isinstance(x, Fraction):
            self.iv = arb(x.numerator) / arb(x.denominator)
        elif isinstance(x, (float, int)):
            self.iv = arb(x)
        elif isinstance(x, str):
            self.iv = arb(x)  # "m +/- r" interval strings (G-eng verified)
        else:
            raise TypeError(f"IV: unsupported {type(x)}")

    @classmethod
    def span(cls, lo, hi):
        """Interval [lo, hi] exactly via the 'mid +/- rad' string form."""
        m = (lo + hi) / 2.0
        r = (hi - lo) / 2.0
        if r == 0.0:
            return cls(float(m))
        return cls(f"{float(m)!r} +/- {float(r)!r}")

    @classmethod
    def unit(cls):
        return cls.span(-1.0, 1.0)

    def _as(self, o):
        return o if isinstance(o, IV) else IV(o)

    def __add__(self, o): return IV(self.iv + self._as(o).iv)
    def __radd__(self, o): return self + o
    def __sub__(self, o): return IV(self.iv - self._as(o).iv)
    def __rsub__(self, o): return IV(self._as(o).iv - self.iv)
    def __mul__(self, o): return IV(self.iv * self._as(o).iv)
    def __rmul__(self, o): return self * o
    def __truediv__(self, o): return IV(self.iv / self._as(o).iv)
    def __neg__(self): return IV(-self.iv)
    def __pow__(self, n):
        if not isinstance(n, int):
            raise ValueError("IV.__pow__ is int-only")
        if n >= 0:
            return IV(self.iv ** n)
        return IV(1) / IV(self.iv ** (-n))
    def exp(self): return IV(self.iv.exp())
    def log(self): return IV(self.iv.log())
    def sinh(self): return IV(self.iv.sinh())
    def cosh(self): return IV(self.iv.cosh())
    def tanh(self): return IV(self.iv.tanh())
    def sin(self): return IV(self.iv.sin())
    def cos(self): return IV(self.iv.cos())
    def absmax(self):
        lo = float(self.iv.mid()) - float(self.iv.rad())
        hi = float(self.iv.mid()) + float(self.iv.rad())
        return max(abs(lo), abs(hi))
    def absmin(self):
        lo = float(self.iv.mid()) - float(self.iv.rad())
        hi = float(self.iv.mid()) + float(self.iv.rad())
        if lo <= 0.0 <= hi:
            return 0.0
        return min(abs(lo), abs(hi))
    def width(self): return 2.0 * float(self.iv.rad())
    def midf(self): return float(self.iv.mid())
    def contains_float(self, v):
        return (float(self.iv.mid()) - float(self.iv.rad())) <= v \
            <= (float(self.iv.mid()) + float(self.iv.rad()))


C_EULER = IV(_ENGINE_STR)   # Euler-Mascheroni at 105 digits (interval parse)
C_PI = IV(_PI_STR)          # pi at 105 digits (sine branch keeps float pi)
C_ARCH = (IV(4) * C_PI).log() + C_EULER  # log(4pi) + gamma (1020 rig)


# ----------------------------------------------------- exact polynomial kit
class Poly:
    __slots__ = ("c",)
    def __init__(self, c):
        self.c = [Fraction(x) for x in c]
        while self.c and self.c[-1] == 0:
            self.c.pop()
    @staticmethod
    def zero(): return Poly([Fraction(0)])
    @staticmethod
    def one(): return Poly([Fraction(1)])
    @staticmethod
    def var(): return Poly([Fraction(0), Fraction(1)])
    def add(self, o):
        n = max(len(self.c), len(o.c))
        return Poly([(self.c[i] if i < len(self.c) else Fraction(0)) +
                     (o.c[i] if i < len(o.c) else Fraction(0)) for i in range(n)])
    def sub(self, o): return self.add(o.neg())
    def neg(self): return Poly([-x for x in self.c])
    def mul(self, o):
        if not self.c or not o.c:
            return Poly.zero()
        r = [Fraction(0)] * (len(self.c) + len(o.c) - 1)
        for i, ci in enumerate(self.c):
            for j, cj in enumerate(o.c):
                r[i + j] += ci * cj
        return Poly(r)
    def deriv(self):
        return Poly([Fraction(i + 1) * self.c[i + 1]
                     for i in range(len(self.c) - 1)])
    def coeff_abs_sum(self):
        return float(sum(abs(c) for c in self.c))
    def deg(self):
        return len(self.c) - 1
    def eval_iv(self, x):
        acc = IV(Fraction(0))
        for coef in reversed(self.c):
            acc = acc * x + IV(coef)
        return acc


def rho_chains(max_order):
    """R_m(x) = N_m(x) / (1-x^2)^{2m} with INTEGER coefficient lists.

    Recurrence (exact, derived from R_{m+1} = R'_m + R_m rho'):
      N_{m+1} = N'_m (1-x^2)^2 + N_m [(4m-2)x - 4m x^3],
      den_{m+1} = (1-x^2)^{2m+2}.
    All coefficients are exact integers bounded by ~16^m m! (m = 8 -> well
    inside 2^50; REGISTERED guard below aborts if the bound is exceeded so
    the float representations stay exact-in-double).
    """
    num = [[1]]
    den = [[1]]
    q2 = [1, 0, -2, 0, 1]              # (1 - x^2)^2
    for m in range(max_order):
        nm = num[-1]
        dm = den[-1]
        # N'_m
        d = [(i + 1) * nm[i + 1] for i in range(len(nm) - 1)]
        # convolve with q2 and with [(4m-2)x - 4m x^3]
        t = [0, 4 * m - 2, 0, -4 * m]
        out = [0] * (len(d) + len(q2) - 1)
        for i, a in enumerate(d):
            for j, b in enumerate(q2):
                out[i + j] += a * b
        out2 = [0] * (len(nm) + len(t) - 1)
        for i, a in enumerate(nm):
            for j, b in enumerate(t):
                out2[i + j] += a * b
        nn = [out[i] + (out2[i] if i < len(out2) else 0)
              for i in range(len(out))]
        num.append(nn)
        den.append(_sq_times(dm))
    l1 = [sum(abs(c) for c in n) for n in num]
    maxc = max(max(abs(c) for c in n) for n in num)
    if maxc > 2 ** 50:
        sys.exit(f"ABORT: G-eng rho-chain coefficients exceed 2^50 ({maxc})")
    return num, den, l1, [len(n) - 1 for n in num]


def _sq_times(poly):
    """poly * (1-x^2)^2 with integer coefficients."""
    out = [0] * (len(poly) + 4)
    for i, a in enumerate(poly):
        out[i] += a
        out[i + 2] += -2 * a
        out[i + 4] += a
    return out


def legendre_coeffs(n):
    p0 = Poly([Fraction(1)])
    if n == 0:
        return p0
    p1 = Poly([Fraction(0), Fraction(1)])
    if n == 1:
        return p1
    for k in range(1, n):
        nxt = p1.mul(Poly([Fraction(0), Fraction(2 * k + 1)]))
        nxt = nxt.sub(p0.mul(Poly([Fraction(k)])))
        nxt = nxt.mul(Poly([Fraction(1, k + 1)]))
        p0, p1 = p1, nxt
    return p1


_binom = [[Fraction(1)]]
for _n in range(1, 24):
    _row = [Fraction(1)]
    for _k in range(1, _n):
        _row.append(_binom[_n - 1][_k - 1] + _binom[_n - 1][_k])
    _row.append(Fraction(1))
    _binom.append(_row)

_CHAINS = 8  # bump R_m and Legendre-derivative orders kept

_BINOM_F = [[float(_binom[k][j]) for j in range(k + 1)] for k in range(_CHAINS)]

# v2 forward-error arithmetic: every elementary float64 op is correct to
# <= 2^-53 relative; registered pair helpers carry (value, certified width)
# with margins (1 op error <= 2^-52 * magnitude).
_FEPS = 2.0 ** -52


def wadd(x, y):
    v = x[0] + y[0]
    w = x[1] + y[1] + _FEPS * 4.0 * (abs(x[0]) + abs(y[0]))
    return (v, w)


def wsub(x, y):
    v = x[0] - y[0]
    w = x[1] + y[1] + _FEPS * 4.0 * (abs(x[0]) + abs(y[0]))
    return (v, w)


def wmul(x, y):
    mx = abs(x[0]) + x[1]
    my = abs(y[0]) + y[1]
    v = x[0] * y[0]
    w = x[1] * my + y[1] * mx + _FEPS * 4.0 * mx * my
    return (v, w)


def wscale(x, c):
    return (c * x[0], abs(c) * x[1])


# ----------------------------------------------------------- carrier
class Carrier:
    """f(u) = p(u/a) exp(-1/(1-(u/a)^2)) on (-a, a), or the sine family.

    Certified machinery:
      f_x(x, k)  : interval (d/du)^k f at u = a x, strictly interior x
      ball_bound : closed-form pointwise sup on endpoint ball cells
      core_gl    : Gauss-Legendre core value + certified remainders
      _mrho      : closed-form theorem bound of max|g| over the core
                   ellipse (REGISTERED formula, no sampling)
    """

    ETA = 0.02             # endpoint ball width (per pre-registration doc; < 1/32)
    N_GL = 4096            # interior core GL nodes (exponential headroom)
    NODE_BITS = 52         # float64 node/weight rounding (registered)

    def __init__(self, radius, coeffs, family):
        self.a = float(radius)
        self.family = family
        self.coeffs = [float(c) for c in coeffs]
        if family == "legendre":
            p = Poly.zero()
            for j, c in enumerate(self.coeffs):
                p = p.add(legendre_coeffs(j).mul(Poly([Fraction(c)])))
            self.p = p
            self.pd = [p]
            for _ in range(_CHAINS):
                self.pd.append(self.pd[-1].deriv())
            self.pd_iv = [[IV(c) for c in q.c] for q in self.pd]
            self.P_j = [q.coeff_abs_sum() for q in self.pd]
            self.D_j = [max(q.deg(), 0) for q in self.pd]
            rn, rd, rl1, rdeg = rho_chains(_CHAINS)
            self.rho_num_iv = [[IV(float(c)) for c in n] for n in rn]
            self.rho_den_iv = [[IV(float(c)) for c in n] for n in rd]
            self.rho_l1 = [float(v) for v in rl1]
            self.rho_deg = rdeg
            # v2 float64 arrays (coefficients are dyadic with |num| < 2^50,
            # hence EXACT in double; rounding of the evaluation itself is
            # registered inside _C_LEG_OPS, not assumed away)
            self.pd_f = [[float(x) for x in q.c] or [0.0] for q in self.pd]
            self.rho_num_f = [[float(x) for x in n] for n in rn]
        else:
            self.p = None
            self.pd = []
            self.pd_iv = []
            self.P_j = []
            self.D_j = []

    @staticmethod
    def _horner_iv(coefs, x):
        # coefs stored ASCENDING (c[i] = coeff of x^i): Horner must run
        # from the HIGHEST degree down
        acc = IV(Fraction(0))
        for c in reversed(coefs):
            acc = acc * x + c
        return acc

    def _rho_iv(self, m, x):
        return (self._horner_iv(self.rho_num_iv[m], x)
                / self._horner_iv(self.rho_den_iv[m], x))

    @staticmethod
    def _horner_f(coefs, x):
        out = 0.0
        for c in reversed(coefs):
            out = out * x + c
        return out

    def _rho_f(self, m, x):
        nm = self.rho_num_iv[m]
        dn = self.rho_den_iv[m]
        return self._horner_f([float(c.midf()) for c in nm], x) / \
            self._horner_f([float(c.midf()) for c in dn], x)

    # ---------------- point/interval values
    def f_x(self, x, k):
        """Interval (d/du)^k f at u = a x (|x| < 1 required); x IV."""
        x = x if isinstance(x, IV) else IV(x)
        a = self.a
        if self.family == "sine":
            acc = IV(Fraction(0))
            for j, c in enumerate(self.coeffs, start=1):
                arg = (x + IV(1)) * IV(j * math.pi / 2.0)
                v = arg.sin() if k % 2 == 0 else arg.cos()
                sign = 1.0 if (k // 2) % 2 == 0 else -1.0
                acc = acc + IV(c * sign) * v * IV((j * math.pi / 2.0) ** k)
            return acc / (a ** k)
        b = (-IV(1) / (IV(1) - x * x)).exp()
        total = IV(Fraction(0))
        for j in range(k + 1):
            total = total + (self._horner_iv(self.pd_iv[j], x)
                             * self._rho_iv(k - j, x)) * IV(float(_binom[k][j]))
        return total * b / (a ** k)

    def f_float(self, x, k):
        """Float64 (d/du)^k f at u = a x (G-deriv reference)."""
        from math import comb
        a = self.a
        if self.family == "sine":
            out = 0.0
            for j, c in enumerate(self.coeffs, start=1):
                arg = j * math.pi * (x + 1.0) / 2.0 + k * math.pi / 2.0
                out += c * math.sin(arg) * (j * math.pi / 2.0) ** k
            return out / (a ** k)
        b = math.exp(-1.0 / (1.0 - x * x))
        out = 0.0
        for j in range(k + 1):
            pn = self._horner_f([float(c.midf()) for c in self.pd_iv[j]], x)
            out += comb(k, j) * pn * self._rho_f(k - j, x)
        return out * b / (a ** k)

    # ---------------- REGISTERED closed forms
    def ball_bound(self, k, delta):
        """sup|f^(k)(u)| on |u/a| >= 1 - delta, closed form.

        bsup * (1/a)^k * sum_j C(k,j) P_j N_{k-j} (1.98 delta)^{-2(k-j)}
        with bsup = exp(-1/(2 delta - delta^2)); valid because
        (1 - x^2) >= (2 - delta) delta on the cell, |p^(j)| <= P_j,
        |R_m| <= N_m (1 - x^2)^(-2m), and each (b R_m) term is increasing on
        the cell (delta = 0.02 < 1/32, REGISTERED).
        """
        if self.family == "sine":
            bsup = math.exp(-1.0 / (2.0 * delta - delta * delta))
            total = sum(abs(c) * (j * math.pi / 2.0) ** k
                        for j, c in enumerate(self.coeffs, start=1))
            return bsup * total / (self.a ** k)
        bsup = math.exp(-1.0 / (2.0 * delta - delta * delta))
        total = 0.0
        for j in range(k + 1):
            total += (float(_binom[k][j]) * self.P_j[j] * self.rho_l1[k - j]
                      * (1.98 * delta) ** (-2 * (k - j)))
        return bsup * total / (self.a ** k)

    def _sup_core(self, k):
        """REGISTERED sup|f^(k)(a x)| over the CORE segment |x| <= 1-eta.

        Legendre family: max over q = 1-x^2 >= 2 eta - eta^2 of
        e^{-1/q} q^{-2m} is (2m/e)^{2m} for m >= 1 (interior saddle; 1 for
        m = 0), combined with |p^(j)| <= P_j and |N_m| <= rho_l1: valid on
        the whole core, unlike the ball edge formula and unlike the
        rho-ellipse bound (whose region must exclude the poles at +-1).
        Sine family: |sin| <= 1 pointwise.
        """
        a = self.a
        if self.family == "sine":
            return (sum(abs(c) * (j * math.pi / 2.0) ** k
                        for j, c in enumerate(self.coeffs, start=1))
                    / a ** k) * (1.0 + 1e-9)
        total = 0.0
        for j in range(k + 1):
            mm = k - j
            saddle = 1.0 if mm == 0 else (2.0 * mm / math.e) ** (2 * mm)
            total += (float(_binom[k][j]) * self.P_j[j]
                      * self.rho_l1[mm] * saddle)
        return (total / a ** k) * (1.0 + 1e-9)

    def _sup_whole(self, k):
        """sup|f^(k)| over the whole integration domain, closed form
        (core sup + ball sup: the ball term is REGISTERED to the inner
        edge, where each (b R_m) product increases)."""
        return max(self._sup_core(k), self.ball_bound(k, self.ETA)) \
            * (1.0 + 1e-9)

    def _ellipse_geom_f(self, yf):
        """Core interval [lo_i, hi_i] in x and rho for the GL ellipse
        (float shift yf; certified geometry, float64-representable)."""
        sigma = float(yf) / self.a
        lo_i = -1.0 + self.ETA
        hi_i = 1.0 - self.ETA - sigma
        if hi_i - lo_i <= 1e-12:
            return None
        mid = (lo_i + hi_i) / 2.0
        half = (hi_i - lo_i) / 2.0
        rho = 1.0 + 0.9 * self.ETA / max(half, 1e-12)
        return lo_i, hi_i, mid, half, rho, sigma

    def _ellipse_geom(self, y):
        if isinstance(y, IV):
            y = float(y.midf())
        return self._ellipse_geom_f(y)

    def _mrho(self, k, sigma, mid, half, rho):
        """REGISTERED closed-form theorem bound of max|g| over the x-ellipse.

        All factors are theorem bounds with the Delta floor REGISTERED:
        Delta = 0.9 (2 eta - eta^2), |1 - z^2| >= Delta on the region,
        |exp(-1/(1-z^2))| <= exp(1/Delta), |poly(z)| <= P Rx^deg with
        Rx = |mid| + half a1 (+ |sigma| for the shifted factor).
        """
        a = self.a
        eta = self.ETA
        a1 = (rho + 1.0 / rho) / 2.0
        b1 = (rho - 1.0 / rho) / 2.0
        if self.family == "sine":
            hx = half * b1
            m = sum(abs(c) * (j * math.pi / 2.0) ** k
                    * math.exp(j * math.pi * hx / 2.0)
                    for j, c in enumerate(self.coeffs, start=1))
            m0 = sum(abs(c) * math.exp(j * math.pi * hx / 2.0)
                     for j, c in enumerate(self.coeffs, start=1))
            return a * half * (m * m0) / (a ** k) * (1.0 + 1e-9)
        delta = 0.9 * (2.0 * eta - eta * eta)
        rx = abs(mid) + half * a1
        exp_b = math.exp(1.0 / delta)      # per bump factor
        cores = []
        for kk in (0, k):
            ext = abs(sigma) if kk else 0.0
            rr = rx + ext
            s = 0.0
            for j in range(kk + 1):
                s += (float(_binom[kk][j]) * self.P_j[j]
                      * rr ** self.D_j[j]
                      * self.rho_l1[kk - j]
                      * rr ** self.rho_deg[kk - j]
                      / delta ** (2 * (kk - j)))
            cores.append(s)
        m = (a * half) * (cores[0] * cores[1] / (a ** k)) \
            * exp_b ** 2 * (1.0 + 1e-9)
        return max(m, 1e-30)

    # ---------------- v2 certified legs: float64 values + registered widths
    _C_FVAL = 4096         # per-node f^(k) evaluation chain (polyval+exp+products)
    _C_DOT = 512           # weight multiply + np.dot accumulation chain
    _C_ASM = 16            # per-node assembly ops (products into the summand)

    def _fvals(self, xs, kmax):
        """Vectorized f^(k)(u = a x), k = 0..kmax, with per-node magnitude
        sums M[k] >= sum of |intermediate terms| (feeds the registered
        forward-error width).  Requires all |xs| < 1 strictly."""
        a = self.a
        if self.family == "sine":
            V, M = [], []
            for k in range(kmax + 1):
                v = np.zeros_like(xs)
                m = np.zeros_like(xs)
                for j, c in enumerate(self.coeffs, start=1):
                    w = (j * math.pi / 2.0) ** k / a ** k
                    arg = j * math.pi * (xs + 1.0) / 2.0 + k * math.pi / 2.0
                    s = np.sin(arg)
                    v = v + (c * w) * s
                    m = m + abs(c * w) * np.abs(s)
                V.append(v)
                M.append(m)
            return V, M
        q = 1.0 - xs * xs
        b = np.exp(-1.0 / q)
        P = [np.polynomial.polynomial.polyval(xs, self.pd_f[j])
             for j in range(kmax + 1)]
        R = [np.polynomial.polynomial.polyval(xs, self.rho_num_f[mm])
             * q ** (-2 * mm) for mm in range(kmax + 1)]
        V, M = [], []
        for k in range(kmax + 1):
            v = np.zeros_like(xs)
            m = np.zeros_like(xs)
            for j in range(k + 1):
                t = (_BINOM_F[k][j] / a ** k) * b * P[j] * R[k - j]
                v = v + t
                m = m + np.abs(t)
            V.append(v)
            M.append(m)
        return V, M

    def _ell_term(self, sigma, mid, half, rho, k, km1=None, n_nodes=None):
        """REGISTERED ellipse theorem remainder of the GL core (float,
        the closed-form m_rho).  The node/weight-rounding perturbation is
        NOT here: it is the REGISTERED per-node backward-error sum,
        computed next to the per-node magnitudes that make it tight
        (section 3.1 amendment: the v1 `n_gl * sup|H|` worst-case form
        over-counts by up to 8 orders on high-derivative-scale carriers).
        n_nodes is the GL node count the ellipse remainder must match."""
        n_gl = self.N_GL if n_nodes is None else n_nodes
        if km1 is None:
            m_rho = self._mrho(k, sigma, mid, half, rho)
        else:  # square leg: H = f^(km1)^2
            m_rho = self._mrho(km1, sigma, mid, half, rho) ** 2
        return 8.0 * m_rho * rho ** (1 - 2 * n_gl) / (rho * rho - 1.0)

    def _pert_prod(self, weights, M, Ms, k, half, node_err, wrel):
        """REGISTERED per-node backward error of the product-leg core sum
        half*sum w_i f(a x_i) f^(k)(a x_i + y).  Nodes x_i -> x_i + e_i,
        weights w_i -> w_i + d_i, |e_i| <= node_err_i, |d_i| <=
        wrel * w_i (float64 path: node_err = 2^-53|x_i|, wrel = 2^-53;
        widow arb path: the certified Taylor/Kantorovich enclosure
        half-widths with wrel = 0, the weights being arb intervals
        themselves); the chain
        gives |dQ| <= a half sum_i w_i [ a node_err_i (M1_i Ms_k_i
        + M0_i Ms_{k+1,i}) + wrel M0_i Ms_k_i ] with M, Ms the _fvals
        per-node intermediate-term magnitudes (>= |f^(j)| at the nodes,
        up to a REGISTERED (1 + 2^-40) margin covering the difference
        between the evaluation node and the true node -- <= 1e-30)."""
        a = self.a
        d = node_err * a * (M[1] * Ms[k] + M[0] * Ms[k + 1])
        return a * half * (float(np.dot(weights, d))
                           + wrel * float(np.dot(weights, M[0] * Ms[k]))) \
            * (1.0 + 2.0 ** -40)

    def _pert_sq(self, xs, weights, M, m, half):
        """Per-node backward error of the square leg H = (f^(m)(a x))^2
        (y = 0): |dQ| <= 2^-53 a half sum w_i [ 2 a |x_i| M_m_i M_{m+1,i}
        + M_m_i^2 ]."""
        a = self.a
        d = np.abs(xs) * (2.0 * a * M[m] * M[m + 1]) + M[m] * M[m]
        return (2.0 ** -53) * a * half * float(np.dot(weights, d))

    def _legs_iv(self, yf, kmax, nodes, n_nodes):
        """arb interval legs F^(k)(yf), k = 0..kmax, at the CURRENT
        flint.ctx.prec (the REGISTERED 256-bit widow evaluation, doc
        section 3.1), each with its FULL width (per-node node/weight
        backward error + ellipse + balls; the f_x evaluations themselves
        round at 2^-256, negligible against them).  Full widths are the
        right choice for k >= 1: those legs enter the pole-free Q-bound
        M4Q (doc 3.1, _q4_sup) with O(1) coefficients and one mean-value
        step s0 * B_(k+1) each, and the per-node bound keeps every leg
        width <= ~1e-8 even for K-scale carriers (widow remainder then
        <= M4Q * s0^4/96 ~ 1e-40)."""
        a = self.a
        eta = self.ETA
        geom = self._ellipse_geom_f(yf)
        if geom is None:
            if self.family == "legendre":
                b0 = self.ball_bound(0, eta)
                return [IV(a * max(0.0, 2.0 - eta - yf / a) * b0
                            * self.ball_bound(k, eta) * 1.1) * IV.unit()
                        for k in range(kmax + 1)]
            b0 = self._sup_core(0)
            return [IV((2.0 * a - yf) * b0 * self._sup_core(k))
                    * IV.unit() for k in range(kmax + 1)]
        _, _, mid, half, rho, sigma = geom
        ns_a, ws_a, ns_f, ws_f, dmax = nodes
        # per-node magnitudes at the float64 reference nodes (>= the true
        # node values up to the registered (1+2^-40) margin: dmax <= 1e-26)
        xsf = mid + half * ns_f
        _, Mf = self._fvals(xsf, kmax + 1)
        _, Msf = self._fvals(xsf + sigma, kmax + 1)
        sx = IV(sigma)
        miv, hiv = IV(mid), IV(half)
        tot = [IV(Fraction(0)) for _ in range(kmax + 1)]
        for wn, wf in zip(ns_a, ws_a):
            x0 = miv + hiv * wn          # arb interval node (encloses x*_i)
            f0x = self.f_x(x0, 0)
            x1 = x0 + sx
            for k in range(kmax + 1):
                tot[k] = tot[k] + (f0x * self.f_x(x1, k)) * wf
        scale = IV(half * a)
        out = []
        for k in range(kmax + 1):
            # node/weight error: dmax per node, weights are arb intervals
            # (their own enclosure is carried by tot); no wrel term.
            rem = (self._pert_prod(ws_f, Mf, Msf, k, half, dmax, 0.0)
                   + self._ell_term(sigma, mid, half, rho, k,
                                    n_nodes=n_nodes))
            if self.family == "legendre":
                rem += (2.0 * self.ETA * a * self.ball_bound(0, eta)
                        * self.ball_bound(k, eta) * 1.1)
            out.append(tot[k] * scale + IV(rem + 1e-300) * IV.unit())
        return out

    def _leg(self, yf, k):
        """Certified F^(k)(y): returns (value_float64, certified_width)
        with width = forward-error + perturbation + ellipse + balls."""
        a = self.a
        geom = self._ellipse_geom_f(yf)
        if geom is None:
            # shrinking tail interval over the ball region: closed-form
            # pointwise bounds THERE (ball_bound for the bump family; the
            # entire sine family uses its derivative sup closed form)
            if self.family == "legendre":
                b0 = self.ball_bound(0, self.ETA)
                bk = self.ball_bound(k, self.ETA)
            else:
                b0 = self._sup_core(0)
                bk = self._sup_core(k)
            w = a * max(0.0, 2.0 - self.ETA - yf / a) * b0 * bk * 1.1
            return 0.0, w * (1.0 + 1e-9)
        _, _, mid, half, rho, sigma = geom
        nodes, weights = _GL_NODES
        xs = mid + half * nodes
        V, M = self._fvals(xs, k + 1)
        Vs, Ms = self._fvals(xs + sigma, k + 1)
        v = a * half * float(np.dot(weights, V[0] * Vs[k]))
        mag = a * half * float(np.dot(weights, M[0] * Ms[k]))
        arith = _FEPS * (self._C_FVAL + self._C_DOT + self._C_ASM) \
            * (mag + abs(v))
        rest = (self._pert_prod(weights, M, Ms, k, half,
                                (2.0 ** -53) * np.abs(xs), 2.0 ** -53)
                + self._ell_term(sigma, mid, half, rho, k))
        balls = 0.0
        if self.family == "legendre":
            balls = (2.0 * self.ETA * a
                     * self.ball_bound(0, self.ETA)
                     * self.ball_bound(k, self.ETA) * 1.1)
        return v, arith + rest + balls + 1e-300

    def _legsq(self, m):
        """Certified int (f^(m))^2 du over [-a, a] (core [-1+eta, 1-eta]
        + two balls for the legendre family; y = 0 square leg)."""
        a = self.a
        eta = self.ETA
        half = 1.0 - eta
        nodes, weights = _GL_NODES
        xs = half * nodes
        V, M = self._fvals(xs, m + 1)
        v = a * half * float(np.dot(weights, V[m] * V[m]))
        mag = a * half * float(np.dot(weights, M[m] * M[m]))
        arith = _FEPS * (2 * self._C_FVAL + self._C_DOT + self._C_ASM) \
            * (mag + abs(v))
        rest = (self._pert_sq(xs, weights, M, m, half)
                + self._ell_term(0.0, 0.0, half,
                                 1.0 + 0.9 * eta / half, m, km1=m))
        balls = 0.0
        if self.family == "legendre":
            bb = self.ball_bound(m, eta)
            balls = 2.0 * eta * a * bb * bb * 1.1
        return v, arith + rest + balls + 1e-300


def _precompute_gl(n):
    nodes, weights = leggauss(n)
    return nodes, weights


_GL_NODES = _precompute_gl(Carrier.N_GL)
_GL_ARB = None


def _gl_arb():
    """The 4096-node GL rule as arb INTERVALS: nodes z_i each enclosing
    the true node x*_i (half-width delta_i <= 1e-26 ASSERTED, measured
    ~3e-27) and weights w_i = 2/((1-x*^2) P'(x*)^2) enclosed through
    z_i.  Built ONCE (module cache) from the scipy float64 roots by
    ONE pass of the 3-term recurrence in arb (NODE_PREC bits) plus an
    interval-Taylor/mean-value certificate, per node:

        p = |P_n(x_hat)|   <= absmax(P pass 1)          (arb, outward)
        d = |P_n'(x_hat)|  >= absmin(D pass 1)
        delta1 = p / d                                   (Kantorovich)
        m = x_hat - P(x_hat)/P'(x_hat)                   (exact arb point)
        [P(m)]   subset P + P'(x_hat)e + [P''(x_hat) +/- N3*delta1]e^2/2
        [P'(m)]  subset P' + P''(x_hat)e +/- N3*delta1^2/2
        delta = absmax([P(m)]) / (absmin([P'(m)]) - max|P''|_seg*2*delta1)

    x*_i in [m_i - delta_i, m_i + delta_i] by the mean-value theorem:
    |m - x*| = |P(m)|/|P'(xi)| on the segment, whose |P'| lower bound
    is asserted positive; the scipy float64 root is only a STARTING
    VALUE -- its correctness is never assumed, and any failed
    assertion ABORTS.  The P_n(m), P_n'(m) values come from an
    interval TAYLOR EXPANSION around x_hat (NOT a second recurrence
    pass: the pass-1 input widths are amplified by (1+sqrt2)^n ~ 1e1568
    in a second recurrence, which overflows to +/-inf at the endpoint
    nodes -- pre-run finding), with [P''(x_hat)] read off the Legendre
    ODE `(1-x^2)P'' = 2xP' - n(n+1)P` from the SAME certified P1/D1
    intervals and [P'''|P''''] bounded by the registered endpoint
    suprema N3 = (n-2)(n-1)n(n+1)(n+2)(n+3)/48 (|P^(k)| is maximal at
    +-1): the quadratic term P''/2*delta1^2
    dominates the enclosure, delta ~ 3e-27, asserted <= 1e-26.  The
    3-term recurrence in arb AMPLIFIES each step's outward rounding
    like (1+sqrt2)^m <= 3^m (interval dependency, NOT mitigated by
    point inputs) -- a 256-bit build aborts at node 0 with `|P'|
    absmin <= 0`; at NODE_PREC = 6700 the pass-1 certified widths are
    <= ~1.5e-55 (below float64 visibility), the per-node assertions
    delta1 <= 1e-14 (Kantorovich regime), delta <= delta1/2
    (contraction) and delta <= 1e-26 EMPIRICALLY VERIFY the whole
    chain at runtime (ABORT otherwise), and the widow/DF node term
    dmax*~3.3e19 becomes <= ~1e-7 (the float64 2^-53|x| form was the
    ~3.7e3 overshoot) -- inside the ~2e-7 widow budget.  doc 3.1."""
    global _GL_ARB
    if _GL_ARB is not None:
        return _GL_ARB
    n = Carrier.N_GL
    fn, fw = _precompute_gl(n)
    old = _flint.ctx.prec
    _flint.ctx.prec = NODE_PREC
    try:
        m1 = IV(1)
        nn = IV(n)

        def pair(vals):
            # (P_n, P_n') at each POINT val via the 3-term recurrence,
            # m outer, vectorized over nodes (arb outward rounding)
            p0 = [m1] * len(vals)
            p1 = list(vals)
            for m in range(2, n + 1):
                cm = IV(2 * m - 1)
                c0 = IV(m - 1)
                im = IV(m)
                p0, p1 = p1, [(cm * v * q1 - c0 * q0) / im
                              for v, q0, q1 in zip(vals, p0, p1)]
            dz = [nn * (q0 - v * q1) / (m1 - v * v)
                  for v, q0, q1 in zip(vals, p0, p1)]
            return p1, dz

        xs = [IV(float(x)) for x in fn]
        P1, D1 = pair(xs)

        # registered endpoint suprema of the higher derivatives on
        # [-1,1] (exact integer products, one float rounding, margin):
        def _dk(k):
            num = 1
            for j in range(1, 2 * k + 1):
                num *= n - k + j
            return float(num) / (2.0 ** k * math.factorial(k)) \
                * (1.0 + 1e-9)
        N3 = _dk(3)
        nnv = IV(n * (n + 1))
        u = IV.unit()
        zints, wsz = [], []
        dmax = 0.0
        for i in range(len(xs)):
            xv = xs[i]
            di = D1[i].absmin()
            if di <= 0.0:
                sys.exit("ABORT: arb GL node %d: |P'| absmin <= 0" % i)
            delta1 = (P1[i].absmax() + 1e-60) / di   # Kantorovich radius
            if delta1 > 1e-14:
                sys.exit("ABORT: arb GL node %d: delta1 %.2e out of "
                         "Kantorovich regime" % (i, delta1))
            mn = xv - P1[i] / D1[i]     # arb Newton point (NOT m1!)
            e1 = mn - xv
            qv = m1 - xv * xv          # 1 - x_hat^2 (m1 is IV(1) above)
            if qv.absmin() <= 0.0:
                sys.exit("ABORT: arb GL node %d: q(x_hat) contains 0" % i)
            # [P''](x_hat) from the ODE at the EXACT float node x_hat:
            pp1 = (IV(2) * xv * D1[i] - nnv * P1[i]) / qv
            # P'' on the segment |x - x_hat| <= 2*delta1 (m and x*):
            pps = pp1 + IV(N3 * 2.0 * delta1) * u
            pm = P1[i] + D1[i] * e1 + pps * e1 * e1 / IV(2)
            dd1 = D1[i] + pp1 * e1 + IV(N3 * delta1 ** 2 / 2.0) * u
            dm = dd1.absmin() - pps.absmax() * 2.0 * delta1
            if dm <= 0.0:
                sys.exit("ABORT: arb GL node %d: |P'| lower bound <= 0"
                         % i)
            dlt = float(pm.absmax() / dm)
            if dlt > 0.5 * delta1:
                sys.exit("ABORT: arb GL node %d: no contraction "
                         "%.2e > %.2e" % (i, dlt, 0.5 * delta1))
            if dlt > 1e-26:
                sys.exit("ABORT: arb GL node %d enclosure too wide %.2e"
                         % (i, dlt))
            dmax = max(dmax, dlt)
            z = mn + IV(dlt) * u
            zints.append(z)
            # weight: P'(x*) enclosed through the segment; (1-z^2) via z
            dd = dd1 + pps * IV(dlt) * u
            dz = m1 - z * z            # 1 - z^2
            if dz.absmin() <= 0.0 or dd.absmin() <= 0.0:
                sys.exit("ABORT: arb GL node %d: weight factors ~ 0" % i)
            wsz.append(IV(2) / (dz * dd * dd))
    finally:
        _flint.ctx.prec = old
    _GL_ARB = (zints, wsz, fn, fw, dmax)
    print("  arb GL nodes certified (Taylor): dmax %.2e" % dmax, flush=True)
    return _GL_ARB
# the 256-bit widow evaluations (_q4_sup -> _legs_iv) use the
# arb-refined 4096-node rule (_gl_arb): at rho ~ 1.018 the k<=6 ellipse
# remainders there are <= ~1e-50 (sine) / <= ~1e-22 (legendre k=4); the
# node term is dmax * ~3.3e19 with enclosure dmax <= 1e-26 asserted
# (measured ~3e-27 -> contribution ~1e-7 per leg width), so every arb leg
# width is ball/ellipse/node-dominated.  The first-cell REMAINDER is the
# pole-free Q-bound M4Q * s0^4/96 (_q4_sup): M4Q ~ 1e3-1e4, so the widow
# remainder is ~1e-40 and the first_cell width is the ladder constants'
# width (<= ~1e-13); the old 4-point sup|h''''| loop certified ~3.7e3 for
# K16 because the Leibniz y^-5 terms (mid ~1e46) cannot cancel as
# intervals (diag13 finding).  The widow budget entry ~2e-7 (doc 3.1)
# holds.  WIDOW_PREC governs the per-cell f_x evaluations; building
# the rule needs a much larger precision because the arb 3-term
# recurrence amplifies its own per-step outward rounding like
# (1+sqrt2)^m <= 3^m (see _gl_arb).
WIDOW_PREC = 256
NODE_PREC = 6700     # _gl_arb recurrence precision (widths ~2^(6493-p))


# ------------------------------------------------------------- h machinery
class CertMachine:
    """Certified arch / prime / total for one explicit carrier function.

    v2 model: float64 reference values, every width a REGISTERED
    forward-error or theorem-remainder term; interval arithmetic for the
    final assembly and the Taylor ladder."""

    _C_CELL = 64  # per-cell Simpson assembly op bound

    def __init__(self, carrier, width_target=1e-6):
        self.carrier = carrier
        self.a = carrier.a
        self.s0 = 2.0 ** -35
        self.width_target = width_target
        v0, w0 = carrier._leg(0.0, 0)
        self.F0v, self.F0w = v0, w0
        self.F0 = IV.span(v0 - w0, v0 + w0)
        v1, w1 = carrier._legsq(1)
        self.F2 = -IV.span(v1 - w1, v1 + w1) / IV(2)
        v2, w2 = carrier._legsq(2)
        self.F4 = IV.span(v2 - w2, v2 + w2) / IV(24)
        # (1/sinh)^(m)(y) = u P_m(coth y):  P_{m+1} = -(P_m'(t^2-1) + t P_m)
        p = Poly([Fraction(1)])
        self._Pm = [p]
        for _ in range(4):
            p = p.deriv().mul(Poly([Fraction(-1), Fraction(0),
                                    Fraction(1)])).add(
                p.mul(Poly.var())).neg()
            self._Pm.append(p)
        self.mesh_theta = self._solve_theta(width_target)

    def _solve_theta(self, width_target):
        # leading per-cell remainder 24 theta^5 / 90 over ~ln(2a/s0)/ln(1+th)
        eps = max(width_target, 1e-12) / 4.0
        ln_ratio = math.log(2.0 * self.a / self.s0)
        theta = 1.0
        for _ in range(80):
            cells = ln_ratio / math.log(1.0 + theta)
            width = cells * 24.0 * theta ** 5 / 90.0
            if width <= eps or theta < 1e-4:
                break
            theta *= 0.9
        return max(theta, 1e-4)

    def _peval(self, poly, tv):
        acc = (0.0, 0.0)
        for c in reversed(poly.c):
            acc = wadd(wmul(acc, tv), (float(c), 0.0))
        return acc

    def _h04(self, yf):
        """(h(y), h''''(y)) as certified float pairs ((v, w), (v, w))."""
        L = [self.carrier._leg(yf, k) for k in range(5)]
        e = math.exp(yf / 2.0)
        ep = (e, _FEPS * 2.0 * e)
        N: list = [None] * 5
        N[0] = wsub(wmul(L[0], ep), (self.F0v, self.F0w))
        for j in range(1, 5):
            acc = (0.0, 0.0)
            for i in range(j + 1):
                term = wmul(L[j - i], ep)
                term = wscale(term, float(_binom[j][i]) / (2.0 ** i))
                acc = wadd(acc, term)
            N[j] = acc
        sh = math.sinh(yf)
        ch = math.cosh(yf)
        u = 1.0 / sh
        wu = _FEPS * 2.0 * u * (1.0 + yf * ch / sh)
        t = ch / sh
        wt = _FEPS * 4.0 * abs(t) * (1.0 + max(yf, 1.0))
        S = []
        for m in range(5):
            S.append(wmul((u, wu), self._peval(self._Pm[m], (t, wt))))
        h0 = wmul(N[0], S[0])
        h4 = (0.0, 0.0)
        for j in range(5):
            h4 = wadd(h4, wscale(wmul(N[j], S[4 - j]), float(_binom[4][j])))
        return h0, h4

    def _h_consts(self):
        f0, f2, f4 = self.F0, self.F2, self.F4
        n1 = f0 / IV(2)
        n2 = f0 / IV(8) + f2
        n3 = f0 / IV(48) + f2 / IV(2)
        n4 = f0 / IV(384) + f2 / IV(8) + f4
        h0 = n1
        h1 = n2
        h2 = n3 - h0 / IV(6)
        h3 = n4 - h1 / IV(6)
        return h0, h1, h2, h3

    def _q4_sup(self):
        """M4Q = sup |Q''''| on [0, s0] for Q = N0 - T3 * sinh (doc 3.1).

        T3 = h0 + h1 y + h2 y^2 + h3 y^3 is the Taylor-3 polynomial of
        h = N0/sinh at 0 (_h_consts is exact coefficient matching), so Q
        and Q'..Q''' vanish at 0; Taylor's theorem in integral form gives
        |Q(y)| <= M4Q y^4 / 24 and, with sinh(y) >= y,

            rem = int_0^s0 (h - T3) <= M4Q * s0^4 / 96.

        Why not sup |h''''|: the Leibniz expansion h'''' = sum C N^j S^(4-j)
        has individual terms ~ y^-5 * N0 ~ 1e46 (K16 diag13) that cancel in
        the true value; interval arithmetic cannot represent the
        cancellation, so the OLD 4-sample-point M4 loop certified a
        remainder of s0^4/24 * 6e46 = 3.7e3 -- sound but 40 orders over
        budget.  Q'''' carries NO poles: N0'''' is pure Leibniz of e^(y/2)F
        against the leg sup-norms B_i, and (T3*sinh)'''' uses only
        cosh(s0) <= 1.000...1.  Every ingredient is a theorem bound:
        legs F^(k)(s0) via arb _legs_iv on the certified _gl_arb rule
        (WIDOW_PREC), one mean-value step each (|F^(i)(y) - F^(i)(s0)|
        <= s0 * B_{i+1}), and the top step by Cauchy-Schwarz
        sup|F^(7)| <= sqrt(F0 * 2a) * sup|f^(7)| with the REGISTERED
        closed-form _sup_whole(7)."""
        c = self.carrier
        n_nodes = Carrier.N_GL
        s0 = self.s0
        old = _flint.ctx.prec
        _flint.ctx.prec = WIDOW_PREC
        try:
            nodes = _gl_arb()  # arb Taylor-enclosed rule (doc 3.1)
            L = c._legs_iv(s0, 6, nodes, n_nodes)
        finally:
            _flint.ctx.prec = old
        # top of the mean-value ladder: sup|F^(7)| <= ||f||_2 ||f^(7)||_2
        b7 = (math.sqrt(max(float(self.F0.absmax()), 0.0) * 2.0 * self.a)
              * c._sup_whole(7)) * (1.0 + 1e-9) + 1e-300
        B = [0.0] * 7
        B[6] = float(L[6].absmax()) + s0 * b7
        for i in range(5, -1, -1):
            B[i] = float(L[i].absmax()) + s0 * B[i + 1]
        E = 1.0 + 0.5 * s0 + s0 * s0        # e^(y/2) on [0, s0]
        M = E * sum(float(_binom[4][i]) * B[i] / float(2 ** (4 - i))
                    for i in range(5))
        ch = math.cosh(s0) * (1.0 + 4.0 * _FEPS)
        M += ch * sum(float(_binom[4][k]) * float(h.absmax())
                      for k, h in enumerate(self._h_consts()))
        return M

    def first_cell(self):
        h0, h1, h2, h3 = self._h_consts()
        s0 = IV(self.s0)
        ladder = s0 * h0 + (s0 ** 2) * h1 / IV(2) + (s0 ** 3) * h2 / IV(3) \
            + (s0 ** 4) * h3 / IV(4)
        rem = IV(self._q4_sup() * (1.0 + 16.0 * _FEPS) / 96.0
                 * self.s0 ** 4 + 1e-300) * IV.unit()
        return ladder + rem

    def _body_pass(self, th):
        bv, bw, cells = 0.0, 0.0, 0
        y = self.s0
        end = 2.0 * self.a
        cache = {}

        def hh(yy):
            r = cache.get(yy)
            if r is None:
                r = self._h04(yy)
                cache[yy] = r
            return r

        while True:
            y_next = min(y * (1.0 + th), end)
            ym = 0.5 * (y + y_next)
            h0a, h4a = hh(y)
            h0b, h4b = hh(ym)
            h0c, h4c = hh(y_next)
            span = y_next - y
            combo = h0a[0] + h0c[0] + 4.0 * h0b[0]
            v = span * combo / 6.0
            w = span * (h0a[1] + h0c[1] + 4.0 * h0b[1]) / 6.0 \
                + _FEPS * self._C_CELL * span * (
                    abs(h0a[0]) + abs(h0c[0]) + 4.0 * abs(h0b[0])
                    + abs(combo)) / 6.0
            m4 = max(abs(h4a[0]) + h4a[1],
                     abs(h4b[0]) + h4b[1],
                     abs(h4c[0]) + h4c[1])
            rem = (span ** 5) * m4 * (1.0 + 16.0 * th) / 90.0
            bv += v
            bw += w + rem
            cells += 1
            if y_next >= end:
                break
            y = y_next
            if cells > 400000:
                print("  [budget] y-cells capped at 400000")
                break
        return bv, bw, cells

    def body(self, refine=True):
        th = self.mesh_theta
        bv = bw = 0.0
        cells = 0
        for _ in range(6):
            bv, bw, cells = self._body_pass(th)
            if not refine or bw <= self.width_target or th <= 1e-4:
                break
            th = max(th / 2.0, 1e-4)
        self.mesh_theta = th
        w = bw * (1.0 + 1e-9) + abs(bv) * _FEPS * 8.0 + 1e-300
        return IV.span(bv - w, bv + w), cells, th

    def arch(self, stats=None):
        first = self.first_cell()
        body_iv, cells, th = self.body()
        tail = self.F0 * IV(self.a).tanh().log()
        arch_iv = C_ARCH * self.F0 + first + body_iv + tail
        if stats is not None:
            stats["theta"] = th
            stats["y_cells"] = cells
            stats["ladder_w"] = first.width()
            stats["body_w"] = body_iv.width()
        return arch_iv

    def prime(self, terms):
        av, aw = 0.0, 0.0
        for q, wf in terms:
            v, w = self.carrier._leg(math.log(q), 0)
            av += 2.0 * wf * v
            aw += abs(2.0 * wf) * (w + _FEPS * 4.0 * abs(v))
        aw += abs(av) * _FEPS * 8.0 + 1e-300
        return IV.span(av - aw, av + aw)


# ------------------------------------------------------- float64 directions
def _import_1100b():
    here = os.path.dirname(os.path.abspath(__file__))
    spec = importlib.util.spec_from_file_location(
        "probe1100b", os.path.join(here, "1100b_first_cell_gate_scan_probe.py"))
    assert spec is not None and spec.loader is not None
    mod = importlib.util.module_from_spec(spec)
    sys.modules["probe1100b"] = mod
    spec.loader.exec_module(mod)
    return mod

P1100B = _import_1100b()

DIRS = [
    ("plain a=2 leg b0", 2.0, 16, "legendre", "plain"),
    ("plain a=4 leg b0", 4.0, 24, "legendre", "plain"),
    ("plain a=2 sine b2", 2.0, 20, "sine", "plain"),
    ("top a=2 leg K=16", 2.0, 16, "legendre", "top"),
    ("top a=4 leg K=24", 4.0, 24, "legendre", "top"),
    ("top a=2 sine K=20", 2.0, 20, "sine", "top"),
    ("totaltop a=2 leg K=16", 2.0, 16, "legendre", "total"),
    ("totaltop a=4 leg K=24", 4.0, 24, "legendre", "total"),
    ("totaltop a=2 sine K=20", 2.0, 20, "sine", "total"),
]


def direction(radius, k, family, mode):
    """Return (probe, coeffs, combo, cond_g, orth).  coeffs: null-space
    coords (plain: basis unit row e_j; top: eigenvector); combo: basis
    coords of the function (plain: e_j)."""
    probe = P1100B.OrbitGateProbe(radius=radius, basis_size=k,
                                  grid_size=P1100B.SCAN_GRID,
                                  envelope_power=1, basis_family=family,
                                  include_primes=True, include_first_cell=True)
    funcs, _sv, coefficients, cond_g, orth = probe._orthonormal_null_functions()
    probe.coefficients = coefficients
    if mode == "plain":
        idx = 0 if family == "legendre" else 2
        coeffs = np.zeros(k)
        coeffs[idx] = 1.0
        combo = coeffs
    else:
        m = probe.arch_matrix(funcs)
        if mode == "total":
            m = m + probe.prime_matrix(funcs)
        ev, evc = eigh((m + m.T) / 2.0, np.eye(m.shape[0]))
        coeffs = evc[:, -1]
        combo = probe.coefficients @ coeffs
    return probe, coeffs, combo, cond_g, orth


def corrected_float64(probe, combo):
    """The committed-1100b corrected arch value of f = combo @ basis."""
    function = probe.basis.T @ np.asarray(combo, dtype=float).ravel()
    mine, _f0, corr, _lags = P1100B.arch_reconstructed(function, probe.step)
    return mine + P1100B.first_cell_of(corr, function.size, probe.step)


def prime_float64(probe, coeffs, funcs):
    """Float64 recomputation of the prime leg; mirrors prime_matrix."""
    out = 0.0
    for q, weight in probe.prime_terms:
        shifted = probe._shifted_functions(math.log(q))
        corr = probe.step * (funcs @ shifted.T)
        out += 2.0 * weight * float(np.sum(coeffs * (coeffs @ corr)))
    return out


# ------------------------------------------------------------------ gates
def run_g_eng():
    x = IV.span(-0.5, 0.5)
    y = x * IV(3)
    if not (y.contains_float(-1.5) and y.contains_float(1.5)):
        sys.exit("ABORT: G-eng interval arithmetic smoke failed")
    if not abs((IV(2) ** 10 - IV(1024)).midf()) < 1e-30:
        sys.exit("ABORT: G-eng arb pow failed")
    print("  G-eng ok (arb interval ops, pow, +/- string constructor)")


def run_g_deriv(carrier):
    rng = np.random.default_rng(7)
    worst = 0.0
    a = carrier.a
    for _ in range(12):
        x = -0.9 + 1.8 * rng.random()
        # h = 1e-5: at h = 1e-4 the FD truncation term f'''h^2/6 (<=
        # _sup_whole(3) * h^2 / 6 ~ 2e-5 on the registered phase-1
        # carrier, sine K=20 top) exceeded the registered tolerance
        # 1e-6*max(1,|fd|) and the gate ABORTED at x = -0.890522 --
        # the threshold is UNCHANGED, only the mechanism step is
        # re-registered so a correct chain can pass (doc 3.1).
        h = 1e-5
        # f_x / f_float are d/du derivatives at u = a x; the divided
        # difference steps in x, so compare against (1/a) * d/dx
        fd = (carrier.f_float(x + h, 0) - carrier.f_float(x - h, 0)) \
            / (2 * h) / a
        iv = carrier.f_x(IV(x), 1)
        slack = abs(iv.midf() - fd) - iv.width() / 2.0
        worst = max(worst, slack)
        if slack > 1e-6 * max(1.0, abs(fd)):
            sys.exit(f"ABORT: G-deriv f' containment at x={x:.6f}")
    # Order-2 (Richardson) signature: the second-difference quotient
    # q(t) -> f''(x) with error t^2 f''''(x)/12, so the successive
    # differences r1 = q(t)-q(t/2), r2 = q(t/2)-q(t/4) have |r1/r2| -> 4
    # for a C^4 float evaluator.  (v1/v2 ITSELF would tend to 1; and a
    # signed max(v2, floor) with f''<0 explodes -- both traps avoided.)
    def _q2(x0, t):
        return (carrier.f_float(x0 + t, 0) - 2 * carrier.f_float(x0, 0)
                + carrier.f_float(x0 - t, 0)) / (t * t)
    x = 0.31
    _t = 2e-3
    r1 = _q2(x, _t) - _q2(x, _t / 2)
    r2 = _q2(x, _t / 2) - _q2(x, _t / 4)
    ratio = abs(r1) / max(abs(r2), 1e-300)
    if not (3.5 <= ratio <= 4.5):
        sys.exit(f"ABORT: G-deriv order-2 Richardson signature {ratio:.4f}")
    print(f"  G-deriv ok (worst f' slack {worst:.2e}, "
          f"f'' Richardson ratio {ratio:.3f})")


def run_g_mrho(carrier):
    """Region bounds |1-z^2| >= Delta and |Re(1/(1-z^2))| <= 1/Delta at
    64 boundary points of the core x-ellipse (arb, 3x margin)."""
    if carrier.family == "sine":
        print("  G-mrho n/a for the entire sine family (no bump)")
        return
    geom = carrier._ellipse_geom(IV(Fraction(0)))
    _, _, mid, half, rho, _ = geom
    a1 = (rho + 1.0 / rho) / 2.0
    b1 = (rho - 1.0 / rho) / 2.0
    delta = 0.9 * (2.0 * carrier.ETA - carrier.ETA ** 2)
    worst = None
    worst_re = 0.0
    for i in range(64):
        th = 2.0 * math.pi * i / 64.0
        w = complex(math.cos(th) * a1, math.sin(th) * b1)
        z = mid + half * w
        d = abs(1.0 - z * z)
        worst = d if worst is None else min(worst, d)
        re = (1.0 - z.real ** 2 + z.imag ** 2) / abs(1.0 - z * z) ** 2
        worst_re = max(worst_re, abs(re))
    if worst is None or worst < delta * 0.997:
        sys.exit(f"ABORT: G-mrho |1-z^2| floor {worst} < 0.997 Delta")
    if worst_re > (1.0 / delta) * 1.003:
        sys.exit(f"ABORT: G-mrho |Re 1/(1-z^2)| {worst_re:.3f} > 1.003/Delta")
    print(f"  G-mrho ok (min|1-z^2| {worst:.6f} >= Delta {delta:.6f}, "
          f"max|Re| {worst_re:.3f} <= 1/Delta {1.0/delta:.2f})")


def run_g_nest(carrier, width_target):
    m1 = CertMachine(carrier, width_target=width_target)
    m2 = CertMachine(carrier, width_target=width_target)
    b1, c1, t1 = m1.body(refine=False)
    m2.mesh_theta = t1 / 2.0
    b2, c2, _t2 = m2.body(refine=False)
    w1, w2 = b1.width(), b2.width()
    if not (w2 < w1 / 1.9):
        sys.exit(f"ABORT: G-nest widths {w1:.2e} -> {w2:.2e}")
    # nesting: both enclose the true body integral; require b2 inside b1
    # up to the registered assembly slack
    lo1 = b1.midf() - b1.width() / 2.0 - 1e-9
    hi1 = b1.midf() + b1.width() / 2.0 + 1e-9
    lo2 = b2.midf() - b2.width() / 2.0
    hi2 = b2.midf() + b2.width() / 2.0
    if not (lo2 >= lo1 and hi2 <= hi1):
        sys.exit(f"ABORT: G-nest not nested [{lo2:.3e},{hi2:.3e}] "
                 f"vs [{lo1:.3e},{hi1:.3e}]")
    print(f"  G-nest ok: width {w1:.2e} -> {w2:.2e} (ratio {w1/w2:.2f}, "
          f"theta {t1:.5f} -> {t1/2:.5f}, cells {c1} -> {c2})")


def run_g_int(report):
    for label, radius, k, family, mode in DIRS[:6]:
        probe, coeffs, combo, cond_g, orth = direction(radius, k, family, mode)
        if mode != "plain" and orth > 1e-10:
            continue
        carr = Carrier(radius, [float(c) for c in combo], family)
        mach = CertMachine(carr, width_target=2e-3)
        av = mach.arch()
        f64 = corrected_float64(probe, combo)
        ok = av.contains_float(f64 - 1e-5) and av.contains_float(f64 + 1e-5)
        if not ok:
            sys.exit(f"ABORT: G-int {label}: f64 {f64:+.8f} outside "
                     f"[{av.midf() - av.width()/2:+.8f}, "
                     f"{av.midf() + av.width()/2:+.8f}]")
        report["G-int"].append({"label": label, "f64": f64,
                                "L": av.midf() - av.width() / 2,
                                "U": av.midf() + av.width() / 2})
    print(f"  G-int ok: {len(report['G-int'])} dirs, widths "
          + ", ".join(f"{r['U'] - r['L']:.2e}" for r in report["G-int"]))


def run_g_prime(report):
    for label, radius, k, family, mode in DIRS[3:6]:
        probe, coeffs, combo, cond_g, orth = direction(radius, k, family, mode)
        if orth > 1e-10:
            continue
        carr = Carrier(radius, [float(c) for c in combo], family)
        mach = CertMachine(carr, width_target=2e-3)
        pv = mach.prime(probe.prime_terms)
        funcs, _sv, _coefficients, _cond, _orth = \
            probe._orthonormal_null_functions()
        f64 = prime_float64(probe, coeffs, funcs)
        ok = pv.contains_float(f64 - 5e-4) and pv.contains_float(f64 + 5e-4)
        if not ok:
            sys.exit(f"ABORT: G-prime {label}: f64 {f64:+.6f} outside "
                     f"[{pv.midf() - pv.width()/2:+.6f}, "
                     f"{pv.midf() + pv.width()/2:+.6f}]")
        report["G-prime"].append({"label": label, "f64": f64,
                                  "L": pv.midf() - pv.width() / 2,
                                  "U": pv.midf() + pv.width() / 2})
    print(f"  G-prime ok: {len(report['G-prime'])} dirs, widths "
          + ", ".join(f"{r['U'] - r['L']:.2e}" for r in report["G-prime"]))


# ------------------------------------------------------------------ main
def main() -> None:
    print("Law-34 certified interval arch certifier (record 1101)")
    print(f"C_ARCH = log(4pi) + gamma = {C_ARCH.midf():.15f}")
    report = {"directions": [], "G-int": [], "G-prime": [],
              "meta": {"eta": Carrier.ETA, "n_gl": Carrier.N_GL}}
    run_g_eng()
    # phase-1 gates on a=2 sine K=20 (cheapest decision-relevant carrier)
    probe0, _c0, combo0, _cond, _orth = direction(2.0, 20, "sine", "top")
    carr0 = Carrier(2.0, [float(c) for c in combo0], "sine")
    run_g_deriv(carr0)
    run_g_mrho(carr0)
    run_g_int(report)
    run_g_prime(report)
    run_g_nest(carr0, 1e-6)
    print()
    # phase-2 certified runs
    for label, radius, k, family, mode in DIRS[3:]:
        probe, coeffs, combo, cond_g, orth = direction(radius, k, family, mode)
        print(f"--- {label} (condG {cond_g:.1e} orth {orth:.1e})")
        if orth > 1e-10:
            print("  DISCARDED by G-rows (orth)")
            continue
        carr = Carrier(radius, [float(c) for c in combo], family)
        stats = {}
        # registered budget: arch half-width <= 5e-7; the widow ladder
        # contributes a fixed ~1.7e-7 half-width, so the body targets
        # 3e-7 (plus F0*C_ARCH ~1e-11)
        mach = CertMachine(carr, width_target=3e-7)
        av = mach.arch(stats)
        pv = mach.prime(probe.prime_terms)
        total = av + pv
        f64 = corrected_float64(probe, combo) if mode == "top" else None
        rec = {"label": label,
               "arch_L": av.midf() - av.width() / 2,
               "arch_U": av.midf() + av.width() / 2,
               "prime_L": pv.midf() - pv.width() / 2,
               "prime_U": pv.midf() + pv.width() / 2,
               "total_L": total.midf() - total.width() / 2,
               "total_U": total.midf() + total.width() / 2,
               "theta": stats["theta"], "y_cells": stats["y_cells"]}
        print(f"  arch  in [{rec['arch_L']:+.8f}, {rec['arch_U']:+.8f}] "
              f"(w {av.width():.2e})" +
              (f"  f64 {f64:+.8f}" if f64 is not None else ""))
        print(f"  prime in [{rec['prime_L']:+.8f}, {rec['prime_U']:+.8f}] "
              f"(w {pv.width():.2e})")
        print(f"  TOTAL in [{rec['total_L']:+.8f}, {rec['total_U']:+.8f}] "
              f"(w {total.width():.2e})  theta {stats['theta']:.5f} "
              f"cells {stats['y_cells']}")
        report["directions"].append(rec)
    h1c = [(r["label"], r["total_L"]) for r in report["directions"]
           if r["total_L"] > 0]
    h2c = [(r["label"], r["total_U"]) for r in report["directions"]
           if r["total_U"] < 0]
    out = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                       "1101_cert.json")
    with open(out, "w", encoding="utf-8") as fh:
        json.dump(report, fh, indent=1, default=str)
    print(f"certificate file: {out}")
    if h1c:
        print(f"VERDICT: H1c CERTIFIED-POSITIVE-GATE on {h1c}")
    elif h2c:
        print(f"VERDICT: H2c CERTIFIED-NEGATIVE-GATE on {h2c}")
    else:
        print("VERDICT: STRADDLE (no separation at the certified width)")
    print("END 1101")


if __name__ == "__main__":
    main()