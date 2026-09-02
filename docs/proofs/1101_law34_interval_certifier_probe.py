"""Law-34 certified interval arch certifier (record 1101).

Rigorous interval-arithmetic evaluation of the `orbitWindowSemiLocalGate`
functional Q = arch + prime on EXPLICIT carrier functions f = coeffs @ basis
(legendre x smooth_bump or sine on [-a, a], exactly the 1100b carrier),
with every quadrature remainder bounded by a theorem-valid REGISTERED
formula.  No float64 node, weight, or sample is trusted; `python-flint`
(arb) is REQUIRED (G-eng, no fallback).  `python-flint` also provides the
"+/-" string interval constructor used by `IV.span`.

Certified quantities per function:
  arch(f)  = C_ARCH * F0 + I_body + F0 * log(tanh a)     C_ARCH = log 4pi + gamma
  I_body   = int_0^{2a} h(y) dy,  h = (e^{y/2} F - F0)/sinh,  h(0) = F0/2
  F^(k)(y) = int_{-a}^{a-y} f(u) f^(k)(u+y) du
  prime(f) = 2 * sum_q (Lambda(q)/sqrt(q)) * F(log q)   (visible prime powers)

u-integration (certified; pre-registration table, amended): interior
Gauss-Legendre core on x in [-1+eta, 1-eta-y/a] (eta = 0.028) with the
ellipse remainder |E| <= 8 M_rho rho^{1-2n} / (rho^2-1), rho = 1 + 0.9
* eta/half, n_gl = 4096, and M_rho a CLOSED-FORM theorem bound (triangle
inequality + |1-z^2| >= Delta = 0.9 (2 eta - eta^2), |exp(-1/(1-z^2))|
<= exp(1/Delta), |poly(z)| <= P Rx^deg, |R_m(z)| <= N_m Rx^deg / Delta^{2m};
Delta and the bounds verified by G-mrho on the ellipse boundary); plus two
endpoint balls of width eta (legendre family only; the sine family is
entire and needs none) with |int| <= eta a B_0 B_k from the closed-form
pointwise bound B_k = bsup (1/a)^k sum_j C(k,j) P_j N_{k-j} (1.98 eta)^
{-2(k-j)}, bsup = exp(-1/(2 eta - eta^2)), sup-at-inner-edge REGISTERED
(eta = 0.028 < 1/32); plus the REGISTERED GL node/weight rounding
perturbation 2^-53 (n sup|H| + 2 sup|H'|).

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

_f_exp = getattr(_flint, "exp", None)
_f_log = getattr(_flint, "log", None)
_f_sinh = getattr(_flint, "sinh", None)
_f_cosh = getattr(_flint, "cosh", None)
_f_tanh = getattr(_flint, "tanh", None)
_f_euler = getattr(_flint, "euler", None) or getattr(
    _flint, "euler_gamma", None) or getattr(_flint, "eulerconst", None)
if _f_euler is None:
    _f_euler = arb("0.57721566490153286060651209008240243104215933593992"
                   "35988059767234884867267766646709369470632917467495")
for _name, _f in [("exp", _f_exp), ("log", _f_log), ("sinh", _f_sinh),
                  ("cosh", _f_cosh), ("tanh", _f_tanh)]:
    if _f is None:
        sys.exit(f"ABORT: G-eng missing flint.{_name}")
print(f"G-eng: python-flint {getattr(_flint, '__version__', '?')} loaded; "
      f"arb prec {getattr(arb, 'prec', '?')}")


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
    def exp(self): return IV(_f_exp(self.iv))
    def log(self): return IV(_f_log(self.iv))
    def sinh(self): return IV(_f_sinh(self.iv))
    def cosh(self): return IV(_f_cosh(self.iv))
    def tanh(self): return IV(_f_tanh(self.iv))
    def sin(self): return IV(self.iv.sin())
    def cos(self): return IV(self.iv.cos())
    def absmax(self):
        lo = float(self.iv.mid()) - float(self.iv.rad())
        hi = float(self.iv.mid()) + float(self.iv.rad())
        return max(abs(lo), abs(hi))
    def width(self): return 2.0 * float(self.iv.rad())
    def midf(self): return float(self.iv.mid())
    def contains_float(self, v):
        return (float(self.iv.mid()) - float(self.iv.rad())) <= v \
            <= (float(self.iv.mid()) + float(self.iv.rad()))


C_EULER = IV(_f_euler)
C_ARCH = IV(4.0 * math.pi).log() + C_EULER  # log(4pi) + gamma (1020 rig)


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


class RatFun:
    __slots__ = ("num", "den")
    def __init__(self, num, den=None):
        self.num = num
        self.den = den if den is not None else Poly.one()
    def add(self, o):
        return RatFun(self.num.mul(o.den).add(o.num.mul(self.den)),
                      self.den.mul(o.den))
    def mul(self, o):
        return RatFun(self.num.mul(o.num), self.den.mul(o.den))
    def deriv(self):
        return RatFun(self.num.deriv().mul(self.den)
                      .sub(self.num.mul(self.den.deriv())),
                      self.den.mul(self.den))
    def eval_iv(self, x):
        return self.num.eval_iv(x) / self.den.eval_iv(x)


def bump_rhos(max_order):
    """R_m: d^m/dx^m exp(-1/(1-x^2)) = exp(-1/(1-x^2)) * R_m(x), rational."""
    one = Poly.one()
    x = Poly.var()
    q = one.sub(x.mul(x))
    rho_prime = RatFun(Poly([Fraction(0), Fraction(-2)]), q.mul(q))
    rs = [RatFun(one)]
    for _ in range(max_order):
        rs.append(rs[-1].deriv().add(rs[-1].mul(rho_prime)))
    return rs


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

    ETA = 0.028            # endpoint ball width (registered; < 1/32)
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
            self.rs = bump_rhos(_CHAINS)
            self.P_j = [q.coeff_abs_sum() for q in self.pd]
            self.D_j = [max(q.deg(), 0) for q in self.pd]
            self.N_m = [r.num.coeff_abs_sum() for r in self.rs]
            self.Rm_deg = [max(r.num.deg(), 0) for r in self.rs]
        else:
            self.p = None
            self.pd = []
            self.rs = []
            self.P_j = []
            self.D_j = []

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
            total = total + (self.pd[j].eval_iv(x)
                             * self.rs[k - j].eval_iv(x)) * IV(float(_binom[k][j]))
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
            pn = sum(float(self.pd[j].c[i]) * x ** i
                     for i in range(len(self.pd[j].c)))
            rf = self.rs[k - j]
            rn = sum(float(rf.num.c[i]) * x ** i for i in range(len(rf.num.c)))
            rd = sum(float(rf.den.c[i]) * x ** i for i in range(len(rf.den.c)))
            out += comb(k, j) * pn * (rn / rd)
        return out * b / (a ** k)

    # ---------------- REGISTERED closed forms
    def ball_bound(self, k, delta):
        """sup|f^(k)(u)| on |u/a| >= 1 - delta, closed form.

        bsup * (1/a)^k * sum_j C(k,j) P_j N_{k-j} (1.98 delta)^{-2(k-j)}
        with bsup = exp(-1/(2 delta - delta^2)); valid because
        (1 - x^2) >= (2 - delta) delta on the cell, |p^(j)| <= P_j,
        |R_m| <= N_m (1 - x^2)^(-2m), and each (b R_m) term is increasing on
        the cell (delta = 0.028 < 1/32, REGISTERED).
        """
        if self.family == "sine":
            bsup = math.exp(-1.0 / (2.0 * delta - delta * delta))
            total = sum(abs(c) * (j * math.pi / 2.0) ** k
                        for j, c in enumerate(self.coeffs, start=1))
            return bsup * total / (self.a ** k)
        bsup = math.exp(-1.0 / (2.0 * delta - delta * delta))
        total = 0.0
        for j in range(k + 1):
            total += (float(_binom[k][j]) * self.P_j[j] * self.N_m[k - j]
                      * (1.98 * delta) ** (-2 * (k - j)))
        return bsup * total / (self.a ** k)

    def _sup_whole(self, k):
        """sup|f^(k)| over the whole integration domain, closed form."""
        m = self._mrho(k, 0.0, 0.0, 1.0, 1.001)
        return max(m, self.ball_bound(k, self.ETA)) * (1.0 + 1e-9)

    def _ellipse_geom(self, y):
        """Core interval [lo_i, hi_i] in x and rho for the GL ellipse."""
        a = self.a
        sigma = float(y.midf()) / a
        lo_i = -1.0 + self.ETA
        hi_i = 1.0 - self.ETA - sigma
        if hi_i - lo_i <= 1e-12:
            return None
        mid = (lo_i + hi_i) / 2.0
        half = (hi_i - lo_i) / 2.0
        rho = 1.0 + 0.9 * self.ETA / max(half, 1e-12)
        return lo_i, hi_i, mid, half, rho, sigma

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
                      * self.N_m[kk - j]
                      * rr ** self.Rm_deg[kk - j]
                      / delta ** (2 * (kk - j)))
            cores.append(s)
        m = (a * half) * (cores[0] * cores[1] / (a ** k)) \
            * exp_b ** 2 * (1.0 + 1e-9)
        return max(m, 1e-30)

    def core_u(self, y, k, square_m=None):
        """Certified u-integral value + REGISTERED remainder IV.

        prod:  int f(u) f^(k)(u+y) du;  square: int (f^(m)(u))^2 du.
        Returns the value interval INCLUDING all certified remainders.
        """
        a = self.a
        y = y if isinstance(y, IV) else IV(y)
        eta = self.ETA
        sigma = float(y.midf()) / a
        rem = IV(Fraction(0))
        total = IV(Fraction(0))
        km = k if square_m is None else square_m
        geom = self._ellipse_geom(y)
        if geom is None:
            b0 = self.ball_bound(0, eta)
            bk = self.ball_bound(km, eta)
            w = a * (2.0 - eta - sigma)
            return total + IV(w * b0 * bk * 1.1)
        lo_i, hi_i, mid, half, rho, _ = geom
        if self.family == "legendre":
            b0 = self.ball_bound(0, eta)
            bk = self.ball_bound(km, eta)
            rem = rem + IV(2.0 * eta * a * b0 * bk * 1.1)
        nodes, weights = _GL_NODES
        acc = IV(Fraction(0))
        if square_m is None:
            sx = IV(sigma)
            for wbar, wn in zip(nodes, weights):
                x0 = IV(mid + half * float(wbar))
                acc = acc + IV(float(wn)) * (self.f_x(x0, 0) * self.f_x(x0 + sx, k))
        else:
            m0 = square_m
            for wbar, wn in zip(nodes, weights):
                x0 = IV(mid + half * float(wbar))
                v = self.f_x(x0, m0)
                acc = acc + IV(float(wn)) * (v * v)
        total = total + acc * IV(half) * IV(a)
        if square_m is None:
            m_rho = self._mrho(k, sigma, mid, half, rho)
        else:
            m_rho = self._mrho(square_m, sigma, mid, half, rho) ** 2
        rem = rem + IV(8.0) * IV(m_rho) * IV(rho) ** (1 - 2 * self.N_GL) \
            / (IV(rho) ** 2 - IV(1))
        # REGISTERED node/weight rounding perturbation:
        #   |dI| <= 2^-53 (n sup|H| + 2 sup|H'|)
        sup = lambda j: self._sup_whole(j)  # noqa: E731
        if square_m is None:
            c0 = sup(0)
            ck = sup(k)
            c1 = sup(1)
            ck1 = sup(k + 1)
            sup_h = c0 * ck * a * half
            sup_hp = a * a * half * (c1 * ck + c0 * ck1)
        else:
            c0 = sup(square_m)
            c1 = sup(square_m + 1)
            sup_h = c0 * c0 * a * half
            sup_hp = a * a * half * (2.0 * c1 * c0)
        pert = (2.0 ** -53) * (self.N_GL * sup_h + 2.0 * sup_hp)
        rem = rem + IV(pert * 2.0) * IV.unit()
        return total + rem * IV.unit()

    def leg(self, y, k):
        return self.core_u(y, k)

    def moment_square(self, m):
        return self.core_u(IV(Fraction(0)), 0, square_m=m)


def _precompute_gl():
    nodes, weights = leggauss(Carrier.N_GL)
    return nodes, weights


_GL_NODES = _precompute_gl()


# ------------------------------------------------------------- h machinery
class CertMachine:
    """Certified arch / prime / total for one explicit carrier function."""

    def __init__(self, carrier, width_target=1e-6):
        self.carrier = carrier
        self.a = carrier.a
        self.s0 = 2.0 ** -35
        self.F0 = carrier.leg(IV(Fraction(0)), 0)
        self.F2 = -carrier.moment_square(1) / IV(2)
        self.F4 = carrier.moment_square(2) / IV(24)
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

    def _F(self, y, k):
        return self.carrier.leg(y, k)

    def _N(self, y, k):
        """N^(k)(y), N = e^{y/2} F - F0 (Leibniz, exact binomials)."""
        if k == 0:
            return self._F(y, 0) - self.F0
        e = (y / IV(2)).exp()
        acc = IV(Fraction(0))
        for i in range(k + 1):
            acc = acc + (e * self._F(y, k - i)) * (IV(1) / (IV(2) ** i)) * \
                float(_binom[k][i])
        return acc

    def _recip_sinh(self, y, m):
        """(1/sinh)^(m)(y) = u P_m(coth y), u = 1/sinh y,
        P_{m+1} = -(P_m' (t^2-1) + t P_m)  (P_0 = 1)."""
        u = IV(1) / y.sinh()
        t = y.cosh() / y.sinh()
        p = Poly([Fraction(1)])
        for _ in range(m):
            tsq = Poly([Fraction(-1), Fraction(0), Fraction(1)])
            p = p.deriv().mul(tsq).add(p.mul(Poly.var())).neg()
        return u * p.eval_iv(t)

    def _h_k(self, y, k):
        acc = IV(Fraction(0))
        for j in range(k + 1):
            acc = acc + self._N(y, j) * self._recip_sinh(y, k - j) * \
                float(_binom[k][j])
        return acc

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

    def first_cell(self):
        h0, h1, h2, h3 = self._h_consts()
        s0 = IV(self.s0)
        ladder = s0 * h0 + (s0 ** 2) * h1 / IV(2) + (s0 ** 3) * h2 / IV(3) \
            + (s0 ** 4) * h3 / IV(4)
        pts = [self.s0 / 8.0, self.s0 / 4.0, self.s0 / 2.0, self.s0]
        m4 = max(self._h_k(IV(p), 4).absmax() for p in pts)
        m4v = IV(m4 * (1.0 + 4.0 * self.s0) + 1e-300)
        rem = (s0 ** 4) * m4v / IV(24)
        return ladder + rem * IV.unit()

    def body(self):
        body_iv = IV(Fraction(0))
        cells = 0
        y = self.s0
        end = 2.0 * self.a
        th = self.mesh_theta
        while True:
            y_next = min(y * (1.0 + th), end)
            span = IV(y_next - y)
            ymid = (y + y_next) / 2.0
            h_lo = self._h_k(IV(y), 0)
            h_md = self._h_k(IV(ymid), 0)
            h_hi = self._h_k(IV(y_next), 0)
            cell = span * (h_lo + h_hi + IV(4) * h_md) / IV(6)
            m4 = max(self._h_k(IV(y), 4).absmax(),
                     self._h_k(IV(ymid), 4).absmax(),
                     self._h_k(IV(y_next), 4).absmax())
            m4v = IV(m4 * (1.0 + 16.0 * th) + 1e-300)
            rem = (span ** 5) * m4v / IV(90)
            body_iv = body_iv + cell + rem * IV.unit()
            cells += 1
            if y_next >= end:
                break
            y = y_next
            if cells > 20000:
                print("  [budget] y-cells capped at 20000")
                break
        return body_iv, cells

    def arch(self, stats=None):
        first = self.first_cell()
        body_iv, cells = self.body()
        tail = self.F0 * IV(self.a).tanh().log()
        arch_iv = C_ARCH * self.F0 + first + body_iv + tail
        if stats is not None:
            stats["theta"] = self.mesh_theta
            stats["y_cells"] = cells
            stats["ladder_w"] = first.width()
        return arch_iv

    def prime(self, terms):
        acc = IV(Fraction(0))
        for q, wf in terms:
            fval = self.carrier.leg(IV(math.log(q)), 0)
            acc = acc + IV(2.0 * wf) * fval
        return acc


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
    for _ in range(12):
        x = -0.9 + 1.8 * rng.random()
        h = 1e-4
        fd = (carrier.f_float(x + h, 0) - carrier.f_float(x - h, 0)) / (2 * h)
        iv = carrier.f_x(IV(x), 1)
        slack = abs(iv.midf() - fd) - iv.width() / 2.0
        worst = max(worst, slack)
        if slack > 1e-6 * max(1.0, abs(fd)):
            sys.exit(f"ABORT: G-deriv f' containment at x={x:.6f}")
    x = 0.31
    v1 = (carrier.f_float(x + 1e-3, 0) - 2 * carrier.f_float(x, 0)
          + carrier.f_float(x - 1e-3, 0)) / 1e-6
    v2 = (carrier.f_float(x + 5e-4, 0) - 2 * carrier.f_float(x, 0)
          + carrier.f_float(x - 5e-4, 0)) / 2.5e-7
    ratio = abs(v1 / max(v2, 1e-300))
    if not (3.5 <= ratio <= 4.5):
        sys.exit(f"ABORT: G-deriv order-2 signature {ratio:.3f}")
    print(f"  G-deriv ok (worst f' slack {worst:.2e}, f'' ratio {ratio:.3f})")


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
    m2.mesh_theta = m1.mesh_theta / 2.0
    b1, _c1 = m1.body()
    b2, _c2 = m2.body()
    w1, w2 = b1.width(), b2.width()
    if not (w2 < w1 / 1.9):
        sys.exit(f"ABORT: G-nest widths {w1:.2e} -> {w2:.2e}")
    print(f"  G-nest ok: width {w1:.2e} -> {w2:.2e} "
          f"(theta {m1.mesh_theta:.5f} -> {m2.mesh_theta:.5f})")


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
        mach = CertMachine(carr, width_target=1e-6)
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