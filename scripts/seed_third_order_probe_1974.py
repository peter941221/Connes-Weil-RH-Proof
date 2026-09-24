#!/usr/bin/env python3
"""Third-order probe of the seed ladder (record 1974).

The seed ladder of records 1972/1973 is
`derivOrderL1 j smoothSeed = 2 * integral of |iteratedDeriv j T|` with
`T = Real.smoothTransition`.  Rung 1 is the number 2, rung 2 the number 8.
This rig prices rung 3.

Closed forms used (hand-derived from the committed bricks; the transition is
`T x = 1 / (1 + exp w)`, `w = (1 - 2x) / (x (1 - x))` on the open window,
`T = 0` for `x <= 0`, `T = 1` for `x >= 1`):

    deriv T        = T (1 - T) G,
    T''            = T (1 - T) [ (1 - 2T) G^2 + G' ],
    T'''           = T (1 - T) [ ((3u^2 - 1)/2) G^3 + 3 u G G' + G'' ],
                     u = 1 - 2T,
    G   = x^-2 + (1-x)^-2,
    G'  = -2 x^-3 + 2 (1-x)^-3,
    G'' = 6 x^-4 + 6 (1-x)^-4.

The bracket coefficient `3 u G G'` is the point of this rig: the first hand
pass used `2 u G G'` and put the interior zero of `T'''` near `x = 0.33`.
The bracket is checked here against numerical differentiation of `T''`, so the
coefficient is read off the numbers, not from the hand pass.

Since `T'' >= 0` on `[0, 1/2]` (record 1973) and `T''` vanishes at `0` and
`1/2`, the total variation identity

    integral over [0, 1/2] of |T'''| = 2 * max T'' on [0, 1/2]

holds whenever `T''` is single-peaked there; this rig measures both sides so
the identity can be checked (it is NOT formalized: single-peakedness is the
open step).  Symmetry `T'''(1 - x) = T'''(x)` doubles the half-line value.

Output: the interior zero x*, the peak value `T''(x*)`, the quadrature value of
`2 * integral of |T'''|` on the whole line, and the residuals of the checks.
"""

import math

PROVENANCE = "record 1974 third-order probe; formulas from records 1972/1973"


def T(x):
    if x <= 0.0:
        return 0.0
    if x >= 1.0:
        return 1.0
    w = (1.0 - 2.0 * x) / (x * (1.0 - x))
    if w > 700.0:          # 1 / (1 + e^w) underflows; also keeps math.exp finite
        return 0.0
    return 1.0 / (1.0 + math.exp(w))


def G(x):
    return 1.0 / x**2 + 1.0 / (1.0 - x) ** 2


def G1(x):
    return -2.0 / x**3 + 2.0 / (1.0 - x) ** 3


def G2(x):
    return 6.0 / x**4 + 6.0 / (1.0 - x) ** 4


def T2(x):
    t = T(x)
    return t * (1.0 - t) * ((1.0 - 2.0 * t) * G(x) ** 2 + G1(x))


def T3(x):
    t = T(x)
    if t == 0.0 or t == 1.0:   # product form: no need to touch the poles of G
        return 0.0
    u = 1.0 - 2.0 * t
    return t * (1.0 - t) * (
        (3.0 * u * u - 1.0) / 2.0 * G(x) ** 3 + 3.0 * u * G(x) * G1(x) + G2(x)
    )


def T3_fd(x, h):
    """Central difference of T2, for the coefficient check."""
    return (T2(x + h) - T2(x - h)) / (2.0 * h)


def richardson(x):
    d1 = T3_fd(x, 1e-3)
    d2 = T3_fd(x, 5e-4)
    return (4.0 * d2 - d1) / 3.0


def bisect_zero(f, lo, hi, tol=1e-14):
    flo = f(lo)
    for _ in range(200):
        mid = 0.5 * (lo + hi)
        fmid = f(mid)
        if fmid == 0.0 or hi - lo < tol:
            return mid
        if (flo < 0.0) == (fmid < 0.0):
            lo, flo = mid, fmid
        else:
            hi = mid
    return 0.5 * (lo + hi)


def simpson(f, a, b, n):
    if n % 2:
        n += 1
    h = (b - a) / n
    s = f(a) + f(b)
    for i in range(1, n):
        s += (4.0 if i % 2 else 2.0) * f(a + i * h)
    return s * h / 3.0


def main():
    print("provenance:", PROVENANCE)

    # 1. coefficient check: closed form vs numerical differentiation of T''.
    print("\n[1] closed-form T''' vs Richardson central difference of T''")
    worst = 0.0
    for x in (0.02, 0.05, 0.1, 0.2, 0.218, 0.25, 0.3, 0.4, 0.45, 0.5,
              0.6, 0.7, 0.8, 0.9):
        a, b = T3(x), richardson(x)
        rel = abs(a - b) / max(1.0, abs(b))
        worst = max(worst, rel)
        print(f"    x={x:<6} closed={a: .10f}  fd={b: .10f}  rel={rel:.2e}")
    print(f"    worst relative residual: {worst:.2e}")
    print("    same check with the WRONG coefficient 2 u G G':")
    for x in (0.218, 0.3, 0.4):
        t = T(x)
        u = 1.0 - 2.0 * t
        wrong = t * (1.0 - t) * (
            (3.0 * u * u - 1.0) / 2.0 * G(x) ** 3 + 2.0 * u * G(x) * G1(x) + G2(x)
        )
        print(f"    x={x:<6} wrong={wrong: .10f}  fd={richardson(x): .10f}")

    # 2. special values.
    print("\n[2] special values")
    print(f"    T''' (1/2) = {T3(0.5):.12f}   (exact target -16)")
    print(f"    T'   (1/2) = {T(0.5) * (1 - T(0.5)) * G(0.5):.12f}   (exact 2)")
    print(f"    G''  (1/2) = {G2(0.5):.12f}   (exact 192)")

    # 3. symmetry.
    print("\n[3] symmetry T'''(1 - x) = T'''(x)")
    worst = 0.0
    for x in (0.1, 0.2, 0.3, 0.4):
        rel = abs(T3(x) - T3(1.0 - x)) / abs(T3(x))
        worst = max(worst, rel)
        print(f"    x={x:<5} T'''={T3(x): .10f}  T'''(1-x)={T3(1.0 - x): .10f}  rel={rel:.2e}")
    print(f"    worst relative residual: {worst:.2e}")

    # 4. interior zero of T''' on (0, 1/2] and the peak of T''.
    xstar = bisect_zero(T3, 0.02, 0.5)
    print("\n[4] interior zero of T''' and the peak of T''")
    print(f"    x* (zero of T''') = {xstar:.12f}")
    print(f"    peak T''(x*)      = {T2(xstar):.12f}")
    print(f"    T''' just below / above x*: {T3(xstar - 1e-4): .6e} / {T3(xstar + 1e-4): .6e}")
    print(f"    T'' at 0.1, 0.2, 0.3, 0.4, 0.5: "
          f"{T2(0.1):.6f} {T2(0.2):.6f} {T2(0.3):.6f} {T2(0.4):.6f} {T2(0.5):.6f}")

    # 5. quadrature of |T'''| over the whole line and the rung.
    print("\n[5] quadrature")
    for n in (20000, 200000):
        half = simpson(lambda x: abs(T3(x)), 0.0, 0.5, n // 2)
        full = 2.0 * half
        print(f"    n={n:<7} integral over [0,1/2] of |T'''| = {half:.10f}"
              f"    whole line = {full:.10f}    rung3 = 2 * full = {2.0 * full:.8f}")
    print(f"    identity check: half-line integral vs 2 * T''(x*) = {2.0 * T2(xstar):.10f}")
    print(f"    rung 3 as 8 * T''(x*) = {8.0 * T2(xstar):.8f}")
    print(f"    integral of T''' over [0,1/2] (should be 0): "
          f"{simpson(T3, 0.0, 0.5, 20000):.3e}")

    # 6. the cancellation is genuine: the leading term of the bracket has its
    # own zero elsewhere, so the zero of T''' is not the zero of 3 u^2 - 1.
    print("\n[6] bracket decomposition at x* and the leading-term zero")
    t = T(xstar)
    u = 1.0 - 2.0 * t
    lead = (3.0 * u * u - 1.0) * G(xstar) ** 3
    mid = 6.0 * u * G(xstar) * G1(xstar)
    tail = 2.0 * G2(xstar)
    print(f"    x*={xstar:.12f}  T={t:.12f}  u={u:.12f}  3u^2-1={3*u*u-1:.10f}")
    print(f"    bracket terms: lead={lead: .6e}  mid={mid: .6e}  tail={tail: .6e}"
          f"  sum={lead+mid+tail: .3e}")

    def lead_zero(x):
        tt = T(x)
        return 3.0 * (1.0 - 2.0 * tt) ** 2 - 1.0

    xl = bisect_zero(lead_zero, 0.25, 0.5)
    print(f"    zero of the leading term 3u^2-1 on (0.25, 0.5): x = {xl:.12f}")


if __name__ == "__main__":
    main()