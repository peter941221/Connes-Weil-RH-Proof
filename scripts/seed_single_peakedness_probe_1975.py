#!/usr/bin/env python3
"""Single-peakedness probe of the seed transition (record 1975).

The third rung of the seed ladder is the transcendental constant
`8 * T'' x*` (record 1974), where `x*` is the interior zero of `T'''` on the
left half.  This rig prices the missing input, the single-peakedness of `T''`
on `(0, 1/2)`, in the half-width coordinate

    s = 1 - 2 x,        x = (1 - s) / 2,        s in (0, 1),

in which the left half is `s > 0` (the right half is the reflection).

Ingredients (all hand-derived from the committed closed forms of records
1973/1974 and re-derived here, then checked numerically against the committed
third-derivative closed form):

    G   ((1-s)/2) = 8 (1 + s^2) / (1 - s^2)^2,
    G'  ((1-s)/2) = -32 s (3 + s^2) / (1 - s^2)^3,
    G'' ((1-s)/2) = 192 (1 + 6 s^2 + s^4) / (1 - s^2)^4,
    u := 1 - 2 T ((1-s)/2) = tanh (v / 2),     v = 4 s / (1 - s^2),

so on the open window the three bracket terms of `T'''` clear to

    T''' x = 16 (1 - u^2) * P(s, u) / (1 - s^2)^6,

    P(s, u) = 4 (3 u^2 - 1) (1 + s^2)^3 - 12 u s (1 + s^2) (3 + s^2) (1 - s^2)
              + 3 (1 + 6 s^2 + s^4) (1 - s^2)^2
            = alpha(s) u^2 - beta(s) u + gamma(s),

    alpha = 12 (1 + s^2)^3                       > 0,
    beta  = 12 s (1 + s^2) (3 + s^2) (1 - s^2)   >= 0 on [0, 1],
    gamma = 3 (1 + 6 s^2 + s^4) (1 - s^2)^2 - 4 (1 + s^2)^3
          = -1 - 42 s^4 + 8 s^6 + 3 s^8 = -1 + s^4 (3 s^4 + 8 s^2 - 42) < 0.

`gamma < 0 < alpha` puts the two roots of `P(s, .)` on opposite sides of `0`,
so for `u > 0`

    sign (P (s, u)) = sign (u - uPlus s),
    uPlus s = (beta s + sqrt (Delta s)) / (2 alpha s),
    Delta s = beta s ^ 2 - 4 alpha s * gamma s > 0.

Hence the sign of `T'''` on the left half is the sign of one explicit
one-variable comparison: `tanh (v/2)` against the quadratic irrationality
`uPlus s`.  This rig (a) checks the factored identity against the committed
third-derivative closed form, (b) reports the exact polynomial coefficients of
`Delta`, (c) scans the comparison for its single crossing and its margins.

Output: the identity residuals, the expansions of alpha, beta, gamma and Delta,
the crossing location, the margins of `u - uPlus` on either side, and the
range of `uPlus`.
"""

import math
from fractions import Fraction as F

PROVENANCE = "record 1975 single-peakedness probe; formulas from records 1973/1974"


# ---------------------------------------------------------------- committed forms


def T(x):
    if x <= 0.0:
        return 0.0
    if x >= 1.0:
        return 1.0
    w = (1.0 - 2.0 * x) / (x * (1.0 - x))
    if w > 700.0:
        return 0.0
    return 1.0 / (1.0 + math.exp(w))


def G(x):
    return 1.0 / x**2 + 1.0 / (1.0 - x) ** 2


def G1(x):
    return -2.0 / x**3 + 2.0 / (1.0 - x) ** 3


def G2(x):
    return 6.0 / x**4 + 6.0 / (1.0 - x) ** 4


def T3(x):
    """Committed third-derivative closed form (record 1974)."""
    t = T(x)
    if t == 0.0 or t == 1.0:
        return 0.0
    u = 1.0 - 2.0 * t
    return t * (1.0 - t) * (
        (3.0 * u * u - 1.0) / 2.0 * G(x) ** 3 + 3.0 * u * G(x) * G1(x) + G2(x)
    )


# ------------------------------------------------------------ factored s-form


def P(s, u):
    """thirdOrderBracket: 4 (3u^2 - 1)(1+s^2)^3 - 12us(1+s^2)(3+s^2)(1-s^2)
    + 3(1+6s^2+s^4)(1-s^2)^2."""
    return (
        4.0 * (3.0 * u * u - 1.0) * (1.0 + s * s) ** 3
        - 12.0 * u * s * (1.0 + s * s) * (3.0 + s * s) * (1.0 - s * s)
        + 3.0 * (1.0 + 6.0 * s * s + s**4) * (1.0 - s * s) ** 2
    )


def alpha(s):
    return 12.0 * (1.0 + s * s) ** 3


def beta(s):
    return 12.0 * s * (1.0 + s * s) * (3.0 + s * s) * (1.0 - s * s)


def gamma(s):
    return 3.0 * (1.0 + 6.0 * s * s + s**4) * (1.0 - s * s) ** 2 - 4.0 * (1.0 + s * s) ** 3


def v_of(s):
    return 4.0 * s / (1.0 - s * s)


def u_of(s):
    return math.tanh(0.5 * v_of(s))


def uPlus(s):
    d = beta(s) ** 2 - 4.0 * alpha(s) * gamma(s)
    return (beta(s) + math.sqrt(d)) / (2.0 * alpha(s))


def T3_factored(s):
    return 16.0 * (1.0 - u_of(s) ** 2) * P(s, u_of(s)) / (1.0 - s * s) ** 6


def bisect(f, lo, hi, tol=1e-15):
    flo = f(lo)
    for _ in range(300):
        mid = 0.5 * (lo + hi)
        fm = f(mid)
        if fm == 0.0 or hi - lo < tol:
            return mid
        if (flo < 0.0) == (fm < 0.0):
            lo, flo = mid, fm
        else:
            hi = mid
    return 0.5 * (lo + hi)


# ------------------------------------------------------------ exact coefficients


def main():
    print("provenance:", PROVENANCE)

    # 1. the factored identity against the committed closed form.
    print("\n[1] T'''((1-s)/2) vs 16 (1-u^2) P(s,u) / (1-s^2)^6")
    worst = 0.0
    for s in (0.0, 0.05, 0.1, 0.2, 0.3, 0.4, 0.5, 0.5635, 0.6, 0.7, 0.8, 0.9, 0.95, 0.99):
        x = (1.0 - s) / 2.0
        a, b = T3(x), T3_factored(s)
        rel = abs(a - b) / max(1.0, abs(a))
        worst = max(worst, rel)
        print(f"    s={s:<7} committed={a: .10e}  factored={b: .10e}  rel={rel:.2e}")
    print(f"    worst relative residual: {worst:.2e}")
    print(f"    endpoint values: P(0,0) = {P(0.0, 0.0):.10f} (exact -1),"
          f" 16*P/(.)**6 at s=0 = {T3_factored(0.0):.10f} (exact T'''(1/2) = -16)")

    # 2. exact coefficients of gamma and Delta as polynomials in s^2.
    print("\n[2] exact polynomial coefficients (Fractions, s^2 = w)")
    for w in (F(1, 4), F(1, 9), F(1, 2), F(4, 25)):
        gamma_direct = 3 * (1 + 6 * w + w * w) * (1 - w) ** 2 - 4 * (1 + w) ** 3
        gamma_claim = -1 - 42 * w * w + 8 * w**3 + 3 * w**4
        print(f"    w={w}  gamma={gamma_direct}  claimed={gamma_claim}  equal={gamma_direct == gamma_claim}")
    print("    gamma = -1 + s^4 (3 s^4 + 8 s^2 - 42); on [0,1] the bracket"
          " 3s^4+8s^2-42 <= -31 < 0, so gamma <= -1 < 0.")

    def delta_exact(s):
        s = F(s)
        a = 12 * (1 + s * s) ** 3
        b = 12 * s * (1 + s * s) * (3 + s * s) * (1 - s * s)
        g = -1 - 42 * s**4 + 8 * s**6 + 3 * s**8
        return b * b - 4 * a * g

    d0 = delta_exact(F(1, 2))
    print(f"    Delta(1/2) = {d0} = {float(d0):.10f}")
    d1 = delta_exact(F(1))
    print(f"    Delta(1)   = {d1} = {float(d1):.10f} (= 4 * 384^2? -> {4 * 384 * 384})")

    # 3. the comparison u - uPlus: single crossing, margins, range of uPlus.
    f = lambda s: u_of(s) - uPlus(s)
    print("\n[3] the comparison u(s) - uPlus(s) on (0,1)")
    for s in (0.0, 0.1, 0.2, 0.3, 0.4, 0.5, 0.55, 0.6, 0.7, 0.8, 0.9, 0.99):
        print(f"    s={s:<6} u={u_of(s):.10f}  uPlus={uPlus(s):.10f}  diff={f(s): .6e}")
    sstar = bisect(f, 0.5, 0.6)
    print(f"    crossing s* = {sstar:.12f}   (1974: x* = 0.218255829186 -> s* = {1 - 2 * 0.218255829186:.12f})")
    print(f"    u(s*) = {u_of(sstar):.12f}   uPlus(s*) = {uPlus(sstar):.12f}")
    print(f"    T'''(x*) factored = {T3_factored(sstar):.3e}")
    xstar = (1.0 - sstar) / 2.0
    t = T(xstar)
    T2 = t * (1.0 - t) * ((1.0 - 2.0 * t) * G(xstar) ** 2 + G1(xstar))
    print(f"    x* = (1-s*)/2 = {xstar:.12f}   T''(x*) = {T2:.12f}   (1974 rig: 9.841042301831)")

    hi_lo = bisect(f, 0.5, 0.6)
    # margins on each side, excluding a neighbourhood of the crossing
    left = min(f(s) for s in [i * 1e-3 for i in range(0, int(hi_lo * 1000))])
    right = min(f(s) for s in [hi_lo + i * 1e-3 for i in range(1, int((1 - hi_lo) * 1000))])
    print(f"    margins: left side min(u-uPlus) = {left:.6e} at s<{hi_lo:.4f};"
          f"  right side min = {right:.6e} at s>{hi_lo:.4f}")
    print(f"    uPlus range on (0,1): min={min(uPlus(s) for s in [i*1e-3 for i in range(1,1000)]):.6f}"
          f"  max={max(uPlus(s) for s in [i*1e-3 for i in range(1,1000)]):.6f}")

    # 4. rational brackets for the crossing (candidates for the Lean certificate).
    print("\n[4] rational sign candidates for the Lean certificate")
    for s in (0.5, 0.55, 0.56, 0.57, 0.58, 0.6):
        print(f"    s={s:<5} P(s,u(s)) = {P(s, u_of(s)): .6e}   sign(P)={1 if P(s, u_of(s)) > 0 else -1}"
              f"   u={u_of(s):.9f}  uPlus={uPlus(s):.9f}")
    print(f"    v(s) at the test points: v(0.55)={v_of(0.55):.6f} v(0.58)={v_of(0.58):.6f}")


if __name__ == "__main__":
    main()