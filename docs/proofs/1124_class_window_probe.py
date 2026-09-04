"""Record 1124 convention-fidelity probe for the class window objects.

The first part is exact Fraction arithmetic: it re-derives the standard
Legendre monomial tables from the recurrence used by
``C1ClassWindowObjects.lean`` and compares them with the tables used by the
1112 Python pipeline.  The second part prints report-only floating-point
samples of the class window functions at 0 and at the two half/boundary
locations.  It installs no enclosure, threshold, gate value, or sign claim.

RH is not claimed.
"""

from fractions import Fraction
from math import exp


K = 8


def trim(poly):
    """Remove trailing zero coefficients from a constant-first polynomial."""
    out = list(poly)
    while len(out) > 1 and out[-1] == 0:
        out.pop()
    return out


def add(lhs, rhs):
    size = max(len(lhs), len(rhs))
    out = [Fraction(0) for _ in range(size)]
    for index, value in enumerate(lhs):
        out[index] += value
    for index, value in enumerate(rhs):
        out[index] += value
    return trim(out)


def scale(scalar, poly):
    return trim([scalar * value for value in poly])


def mul_x(poly):
    return [Fraction(0)] + list(poly)


def legendre_from_recurrence(limit):
    """Return P_0,...,P_limit from the Lean-side standard recurrence."""
    polys = [[Fraction(1)], [Fraction(0), Fraction(1)]]
    for n in range(limit - 1):
        numerator = add(
            scale(Fraction(2 * (n + 1) + 1), mul_x(polys[n + 1])),
            scale(Fraction(-(n + 1)), polys[n]),
        )
        polys.append(scale(Fraction(1, n + 2), numerator))
    return polys[: limit + 1]


# Exact constant-first monomial coefficients of the LEG tables used by 1112.
# These are the Fraction form of numpy.polynomial.legendre.leg2poly applied
# to the standard basis in degrees 0,...,7.
LEG_1112 = [
    [Fraction(1)],
    [Fraction(0), Fraction(1)],
    [Fraction(-1, 2), Fraction(0), Fraction(3, 2)],
    [Fraction(0), Fraction(-3, 2), Fraction(0), Fraction(5, 2)],
    [Fraction(3, 8), Fraction(0), Fraction(-15, 4), Fraction(0), Fraction(35, 8)],
    [Fraction(0), Fraction(15, 8), Fraction(0), Fraction(-35, 4), Fraction(0), Fraction(63, 8)],
    [Fraction(-5, 16), Fraction(0), Fraction(105, 16), Fraction(0), Fraction(-315, 16), Fraction(0), Fraction(231, 16)],
    [Fraction(0), Fraction(-35, 16), Fraction(0), Fraction(315, 16), Fraction(0), Fraction(-693, 16), Fraction(0), Fraction(429, 16)],
]


def eval_poly(poly, x):
    value = Fraction(0)
    for coefficient in reversed(poly):
        value = value * x + coefficient
    return value


def class_bump(x):
    """Report-only float twin of expNegInvGlue (1-x^2)."""
    if abs(x) >= 1.0:
        return 0.0
    return exp(-1.0 / (1.0 - x * x))


def class_window(u, index, scale_a):
    x = u / scale_a
    return float(eval_poly(LEG_1112[index], Fraction(x).limit_denominator(64))) * class_bump(x)


def main():
    generated = legendre_from_recurrence(K - 1)
    assert generated == LEG_1112
    print("1124 exact convention check: PASS (P0..P7 recurrence tables)")

    print("1124 report-only class-window samples")
    for scale_a in (2.0, 3.0, 4.0):
        print(f"a={scale_a:.0f}")
        for index in range(K):
            samples = [
                class_window(0.0, index, scale_a),
                class_window(scale_a / 2.0, index, scale_a),
                class_window(-scale_a / 2.0, index, scale_a),
                class_window(scale_a, index, scale_a),
                class_window(-scale_a, index, scale_a),
            ]
            print(f"  i={index}: " + " ".join(f"{value:.12g}" for value in samples))


if __name__ == "__main__":
    main()
