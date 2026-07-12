#!/usr/bin/env python3
"""Certify failure of the soft mean-zero pole-free Poincare bound.

The source form has jump kernel J(t) and potential kappa_a.  On mean-zero
functions, replacing J by its interval minimum gives a gap 2a*J(2a).  This
script evaluates kappa_a(0) in closed form with Arb and proves that the
resulting sufficient margin is strictly negative.
"""

from __future__ import annotations

import argparse


def prime_powers_up_to(c: int) -> list[tuple[int, int]]:
    primes: list[int] = []
    for candidate in range(2, c + 1):
        if all(candidate % prime for prime in primes):
            primes.append(candidate)
    result: list[tuple[int, int]] = []
    for prime in primes:
        prime_power = prime
        while prime_power <= c:
            result.append((prime_power, prime))
            prime_power *= prime
    return result


def certify(c: int, prec: int) -> None:
    from flint import arb, ctx

    ctx.prec = prec
    pi = arb.pi()
    a = arb(c).log() / 2
    u = (-a / 2).exp()

    # 2 * integral_0^a (J(t)-1/(2t)) dt.
    m1_zero = (
        (4 / a).log()
        + pi / 2
        - ((1 + u) / (1 - u)).log()
        - 2 * u.atan()
    )

    prime_degree = arb(0)
    for prime_power, prime in prime_powers_up_to(c):
        if prime_power * prime_power <= c:
            prime_degree += (
                2
                * arb(prime).log()
                * (arb(prime_power) ** arb("-0.5"))
            )

    kappa_zero = (
        -a.log()
        - (2 * pi).log()
        - arb.const_euler()
        - m1_zero
        - prime_degree
    )

    # J is decreasing, so min_{|t|<=2a} J(t)=J(2a).
    jump_gap = 2 * a * (-a).exp() / (1 - (-4 * a).exp())
    soft_margin = jump_gap + kappa_zero

    print(f"c={c} Arb_bits={prec}")
    print(f"a={a.str(20)}")
    print(f"m1(0)={m1_zero.str(20)}")
    print(f"prime_degree_at_0={prime_degree.str(20)}")
    print(f"kappa(0)={kappa_zero.str(20)}")
    print(f"mean_zero_jump_gap={jump_gap.str(20)}")
    print(f"soft_margin={soft_margin.str(20)}")
    if not soft_margin < 0:
        raise AssertionError("expected the soft Poincare margin to be negative")
    print("soft_min_kernel_poincare_route=rejected")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--c", type=int, nargs="+", default=[5, 13, 29, 53, 100])
    parser.add_argument("--prec", type=int, default=512)
    args = parser.parse_args()
    for c in args.c:
        certify(c, args.prec)


if __name__ == "__main__":
    main()
