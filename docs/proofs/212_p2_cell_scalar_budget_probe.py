#!/usr/bin/env python3
"""Check the exact rational lower bound in Proof 212.

The proof uses only

    1/sqrt(2) > 707/1000
    log(2) > 693/1000.

The latter follows from four positive terms of
log(2)=2*atanh(1/3).  All acceptance checks below use Fraction; the floating
value is printed only for orientation.
"""

from fractions import Fraction
import math


CELL_COUNT = 8


def main() -> None:
    inverse_sqrt_two_lower = Fraction(707, 1000)
    assert inverse_sqrt_two_lower**2 < Fraction(1, 2)

    log_two_series_lower = 2 * sum(
        Fraction(1, (2 * k + 1) * 3 ** (2 * k + 1))
        for k in range(4)
    )
    log_two_lower = Fraction(693, 1000)
    assert log_two_series_lower > log_two_lower

    geometric_lower = sum(
        (CELL_COUNT - shift) * inverse_sqrt_two_lower**shift
        for shift in range(1, CELL_COUNT)
    )
    rayleigh_lower = (
        Fraction(2, CELL_COUNT) * log_two_lower * geometric_lower
    )
    assert rayleigh_lower > 2

    exact_float = (
        2
        * math.log(2)
        / CELL_COUNT
        * sum(
            (CELL_COUNT - shift) * 2 ** (-shift / 2)
            for shift in range(1, CELL_COUNT)
        )
    )

    print(f"log2_series_lower={log_two_series_lower}")
    print(f"rayleigh_rational_lower={rayleigh_lower}")
    print(f"rayleigh_rational_margin={rayleigh_lower - 2}")
    print(f"rayleigh_float={exact_float:.15f}")
    print(f"rayleigh_float_margin={exact_float - 2:.15f}")


if __name__ == "__main__":
    main()
