#!/usr/bin/env python3
"""T0 extension sentinel (record 1582): validate the psi'' / psi''' Stieltjes
chains used by the T0c / T0d derivative bounds.

Checks the paper claims that for real x >= 2

    D3(x) := psi''(x) + 1/x^2 + 1/x^3 + 1/(2x^4)
          in (0, 1/(6 x^6)],   leading terms  1/(6x^6) - 1/(6x^8) + 3/(10x^10),

    E4(x) := (2/x^3 + 3/x^4 + 2/x^5) - psi'''(x)
          in (0, 1/x^7],       leading terms  1/x^7 - (4/3)/x^9 + 3/x^11,

i.e. the absolute-value Stieltjes bounds used on the vertical line
|psi''(z) + 1/z^2 + 1/z^3 + 1/(2z^4)| <= (4 sqrt 2 / 6)|z|^-6 and
|psi'''(z) - 2/z^3 - 3/z^4 - 2/z^5| <= 4 sqrt(2) |z|^-7 hold pointwise on the
positive real axis with the pinned constants, and the leading coefficient
chains are consistent with the true remainders.

Method: entirely exact `fractions.Fraction` interval arithmetic, with NO
stored constants and no zeta/H bookkeeping: the polygamma sums are evaluated
directly by the Euler-Maclaurin (Hurwitz) form

    sum_{n>=q} n^(-s) in [ A + sum_{k=1..M} B_{2k}/(2k)! (s)_{2k-1} q^(-s-2k+1),
                           same + |first omitted term| ],

    A = q^(1-s)/(s-1) + q^(-s)/2,

where the remainder has the sign of, and is bounded by, the first omitted
term (classical EM property for the completely monotone x^-s; DLMF 12.3
family, the same citation family as record 1570's Stieltjes remainder).
With psi''(m) = -2 sum_{n>=m} n^-3 and psi'''(m) = 6 sum_{n>=m} n^-4 the
chain reduces D3 / E4 to pure coefficient algebra on Bernoulli numbers,
which is exactly what the sentinel validates.

This is a sentinel for the 1582 paper wave, not a proof: the proof is the
Stieltjes remainder theorem on Re z > 0, transcribed in the record.
"""

import os
import sys
from fractions import Fraction as F

sys.path.insert(0, os.path.join(
    os.path.dirname(os.path.abspath(__file__)), "..", "yoshida_intervals"))
from yoshida_interval_gen import Interval  # noqa: E402


def bernoulli(n: int) -> F:
    """B_2, B_4, B_6, B_8, B_10, B_12 as exact fractions."""
    return {2: F(1, 6), 4: F(-1, 30), 6: F(1, 42),
            8: F(-1, 30), 10: F(5, 66), 12: F(-691, 2730)}[n]


def rising(s: int, j: int) -> F:
    """(s)_j = s (s+1) ... (s+j-1), j >= 1."""
    t = F(1)
    for k in range(j):
        t *= s + k
    return t


def em_term(s: int, k: int, q: F) -> F:
    """B_{2k}/(2k)! * (s)_{2k-1} * q^(-s-2k+1)."""
    coef = bernoulli(2 * k) * rising(s, 2 * k - 1)
    for j in range(1, 2 * k + 1):
        coef /= F(j)
    return coef * q ** (-s - 2 * k + 1)


def tail_em_bracket(s: int, q: int, m_terms: int) -> Interval:
    """Bracket of sum_{n>=q} n^(-s), s in {3, 4}, q >= 1."""
    big = F(q)
    total = big ** (1 - s) / (s - 1) + big ** (-s) / 2
    for k in range(1, m_terms + 1):
        total += em_term(s, k, big)
    omitted = abs(em_term(s, m_terms + 1, big))
    assert omitted > 0
    return Interval(total, total + omitted)


def main() -> int:
    ok = True
    for e in range(1, 9):
        m = 2 ** e
        psi2 = Interval(-2 * tail_em_bracket(3, m, 4).hi,
                        -2 * tail_em_bracket(3, m, 4).lo)
        t4 = tail_em_bracket(4, m, 4)
        psi3 = Interval(6 * t4.lo, 6 * t4.hi)
        # D3(m) = psi''(m) + 1/m^2 + 1/m^3 + 1/(2 m^4)
        d3 = Interval(psi2.lo + F(1, m * m) + F(1, m ** 3) + F(1, 2 * m ** 4),
                      psi2.hi + F(1, m * m) + F(1, m ** 3) + F(1, 2 * m ** 4))
        b3 = F(1, 6 * m ** 6)
        r3 = (d3.lo + d3.hi) / 2 / b3
        p3 = 1 - F(1, m * m) + F(9, 5 * m ** 4)
        v3 = d3.lo > 0 and d3.hi <= b3
        # E4(m) = 2/m^3 + 3/m^4 + 2/m^5 - psi'''(m)
        lead = 2 * F(1, m ** 3) + 3 * F(1, m ** 4) + 2 * F(1, m ** 5)
        e4 = Interval(lead - psi3.hi, lead - psi3.lo)
        b4 = F(1, m ** 7)
        r4 = (e4.lo + e4.hi) / 2 / b4
        p4 = 1 - F(4, 3 * m * m) + F(3, m ** 4)
        v4 = e4.lo > 0 and e4.hi <= b4
        ok = ok and v3 and v4
        print(
            f"m={m:<4} D3/m-bound={float(r3):.6f} pred={float(p3):.6f} "
            f"{'PASS' if v3 else 'FAIL'}   "
            f"E4/m-bound={float(r4):.6f} pred={float(p4):.6f} "
            f"{'PASS' if v4 else 'FAIL'}"
        )
    print("OVERALL:", "PASS" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
