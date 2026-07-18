#!/usr/bin/env python3
"""Numerical check for Proof 333's explicit CC20 delta branch.

This checks the asymptotic scale and the distributional Q cancellation. It does
not model the prolate series or the moving finite-S projection.
"""

from __future__ import annotations

import math


def sine_integral(value: float) -> float:
    if value < 0.0:
        return -sine_integral(-value)
    if value == 0.0:
        return 0.0
    if value <= 10.0:
        term = value
        total = term
        for index in range(200):
            term *= -(
                value * value * (2 * index + 1)
                / ((2 * index + 2) * (2 * index + 3) ** 2)
            )
            total += term
            if abs(term) <= 1.0e-17 * max(1.0, abs(total)):
                break
        return total

    inverse_square = 1.0 / (value * value)
    first_term = 1.0 / value
    second_term = inverse_square
    first_sum = first_term
    second_sum = second_term
    previous_first = abs(first_term)
    previous_second = abs(second_term)
    for order in range(1, 80):
        next_first = (
            -first_term * (2 * order) * (2 * order - 1) * inverse_square
        )
        next_second = (
            -second_term * (2 * order + 1) * (2 * order) * inverse_square
        )
        if abs(next_first) > previous_first or abs(next_second) > previous_second:
            break
        first_sum += next_first
        second_sum += next_second
        first_term = next_first
        second_term = next_second
        previous_first = abs(next_first)
        previous_second = abs(next_second)
    return (
        math.pi / 2.0
        - math.cos(value) * first_sum
        - math.sin(value) * second_sum
    )


def cc20_delta(rho: float) -> float:
    plus = 2.0 * math.pi * (1.0 + rho)
    minus = 2.0 * math.pi * (rho - 1.0)
    return 2.0 * math.sqrt(rho) * (
        sine_integral(plus) / plus + sine_integral(minus) / minus
    )


def simpson(function, lower: float, upper: float, intervals: int) -> float:
    if intervals % 2 != 0:
        raise ValueError("Simpson quadrature requires an even interval count")
    step = (upper - lower) / intervals
    total = function(lower) + function(upper)
    total += 4.0 * sum(
        function(lower + (2 * index - 1) * step)
        for index in range(1, intervals // 2 + 1)
    )
    total += 2.0 * sum(
        function(lower + 2 * index * step)
        for index in range(1, intervals // 2)
    )
    return total * step / 3.0


SUPPORT_RADIUS = 1.3


def q_test(u: float) -> float:
    scaled = u / SUPPORT_RADIUS
    if abs(scaled) >= 1.0:
        return 0.0
    one_minus_square = 1.0 - scaled * scaled
    return (
        6.0 / SUPPORT_RADIUS**2
        * one_minus_square
        * (1.0 - 5.0 * scaled * scaled)
        + 0.25 * one_minus_square**3
    )


def main() -> None:
    print("rho  sqrt(rho)*delta  rho^(3/2)*(delta-rho^(-1/2))")
    for rho in (100.0, 1000.0, 10000.0):
        value = cc20_delta(rho)
        print(
            f"{rho:5.0f} {math.sqrt(rho) * value:17.10f} "
            f"{rho**1.5 * (value - rho**-0.5):28.10f}"
        )

    annihilation = simpson(
        lambda u: math.exp(u / 2.0) * q_test(u),
        -SUPPORT_RADIUS,
        SUPPORT_RADIUS,
        4000,
    )
    print(f"weighted_Q_annihilation={annihilation:.12e}")

    for displacement in (5.0, 8.0, 10.0):
        pairing = simpson(
            lambda u: cc20_delta(math.exp(displacement - u)) * q_test(u),
            -SUPPORT_RADIUS,
            SUPPORT_RADIUS,
            12000,
        )
        print(
            f"z={displacement:4.1f} pairing={pairing:.12e} "
            f"half_power_scaled={pairing * math.exp(displacement / 2.0):.12e}"
        )


if __name__ == "__main__":
    main()
