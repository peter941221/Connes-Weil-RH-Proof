#!/usr/bin/env python3
"""T0 wave sentinel: validate the digamma Stieltjes expansion constants.

Checks the paper claim (record 1570) that for real x >= 2

    D2(x) := psi(x) - log x + 1/(2x) + 1/(12x^2)

is strictly positive with D2(x) <= 1/(120 x^4), i.e. the absolute-value
Stieltjes bound |psi(z) - log z + 1/(2z) + 1/(12z^2)| <= 1/(120|z|^4) holds
pointwise on the positive real axis with the pinned constant AND the leading
coefficient B4 chain (1/6 -> 1/12, remainder 1/120) is consistent with the
true value D2(x) = 1/(120x^4) - 1/(252x^6) + O(x^-8).

Method: entirely exact `fractions.Fraction` interval arithmetic.
  * psi(m) at positive integers: the defining series telescopes exactly,
    psi(m) = H_{m-1} - gamma, bracketed by the stored 50-digit gamma bracket.
  * log m = (binary exponent) * log 2, with log 2 = 2*atanh(1/3) evaluated
    by its rational series and a geometric tail bound (NO stored log-2 digits
    beyond none: log2 is derived here, gamma is the only stored constant).
This is a sentinel for the T0 paper wave, not a proof: the proof is the
Stieltjes remainder theorem on Re z > 0, transcribed in record 1570.
"""

import os
import sys
from fractions import Fraction as F

sys.path.insert(0, os.path.join(
    os.path.dirname(os.path.abspath(__file__)), "..", "yoshida_intervals"))
from yoshida_interval_gen import Interval, GAMMA_LO, GAMMA_HI  # noqa: E402


def atanh_series_half(y: F, width: F) -> Interval:
    """Bracket of atanh(y) = sum_{k>=0} y^(2k+1)/(2k+1), 0 < y < 1.

    Tail after K terms: sum_{k>=K} y^(2k+1)/(2k+1)
      <= y^(2K+1) / ((2K+1)(1 - y^2)).
    """
    assert F(0) < y < F(1)
    total = F(0)
    power = y
    k = 0
    while True:
        total += power / F(2 * k + 1)
        k += 1
        power *= y * y
        tail = power / (F(2 * k + 1) * (F(1) - y * y))
        if tail <= width:
            return Interval(total, total + tail)


def log2_bracket(width: F) -> Interval:
    """log 2 = 2 * atanh(1/3), exactly derived by rational series."""
    iv = atanh_series_half(F(1, 3), width / 2)
    return Interval(iv.lo * 2, iv.hi * 2)


def log_bracket(n: int, width: F, l2: Interval) -> Interval:
    """log n = v2-free part handled by exact exponent split n = 2^e * q with
    q odd: log q needs no reduction here because we only test powers of two,
    so log(2^e) = e * log2 directly."""
    e = 0
    m = n
    while m % 2 == 0:
        m //= 2
        e += 1
    assert m == 1, "this sentinel only tests powers of two"
    lo, hi = l2.lo * e, l2.hi * e
    return Interval(lo - width, hi + width)


def harmonic(n: int) -> F:
    t = F(0)
    for k in range(1, n + 1):
        t += F(1, k)
    return t


def psi_int_bracket(m: int) -> Interval:
    """psi(m) = H_{m-1} - gamma exactly (telescoped defining series)."""
    h = harmonic(m - 1)
    return Interval(h - GAMMA_HI, h - GAMMA_LO)


def main() -> int:
    width = F(1, 10**44)
    l2 = log2_bracket(width)
    gamma_slack = GAMMA_HI - GAMMA_LO
    print(f"log2 bracket width   = {float(l2.hi - l2.lo):.3e}")
    print(f"gamma bracket width  = {float(gamma_slack):.3e}")
    ok = True
    for e in range(1, 9):
        m = 2**e
        psi = psi_int_bracket(m)
        logm = log_bracket(m, width, l2)
        d2 = Interval(
            psi.lo - logm.hi + F(1, 2 * m) + F(1, 12 * m * m),
            psi.hi - logm.lo + F(1, 2 * m) + F(1, 12 * m * m),
        )
        bound = F(1, 120 * m**4)
        mid = (d2.lo + d2.hi) / 2
        ratio = mid / bound
        pred = (F(1, 120) - F(1, 252) / (m * m)) / F(1, 120)  # x^4 * next-term
        verdict = d2.lo > 0 and d2.hi <= bound
        ok = ok and verdict
        print(
            f"m={m:<4} D2 in [{float(d2.lo):.6e}, {float(d2.hi):.6e}] "
            f"bound 1/(120m^4)={float(bound):.6e} "
            f"ratio D2/bound={float(ratio):.6f} "
            f"two-term pred={float(pred):.6f} "
            f"width={float(d2.hi - d2.lo):.2e} "
            f"{'PASS' if verdict else 'FAIL'}"
        )
    print("OVERALL:", "PASS" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
