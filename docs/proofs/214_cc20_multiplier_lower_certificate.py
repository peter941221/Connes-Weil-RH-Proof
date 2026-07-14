#!/usr/bin/env python3
"""Arb certificate for ell_CC20(t) >= 1/50 on the real line.

The compact interval [0, 50] is covered by Taylor balls centered on a uniform
grid.  At each center, Arb integrates delta(exp(x)) on [0, 8] and evaluates
both the multiplier and its first derivative.  The leading exp(-x/2) tail is
integrated exactly; the proved remainder

    |delta(exp(x)) - exp(-x/2)| <= 2 exp(-3x/2)

is charged explicitly.  The Taylor remainder uses the analytic bound
|ell_CC20''| < 100.

For t >= 50, the Riemann-Siegel derivative is increasing and one integration
by parts gives |delta_hat(t)| <= 100/t.  Arb checks the endpoint margin.
Evenness handles negative t.
"""

from __future__ import annotations

import argparse

from flint import acb, arb, ctx, fmpq


HALF = fmpq(1, 2)
THREE_HALVES = fmpq(3, 2)


def sine_integral_quotient(z: acb) -> acb:
    """Return Si(z)/z with the removable zero handled analytically."""
    if not abs(z) > arb(1) / 4:
        return (-z * z / 4).hypgeom(
            [HALF], [THREE_HALVES, THREE_HALVES]
        )
    return z.si() / z


def delta_log_coordinate(x: acb) -> acb:
    rho = x.exp()
    z_plus = 2 * acb.pi() * (1 + rho)
    z_minus = 2 * acb.pi() * (rho - 1)
    return 2 * (x / 2).exp() * (
        sine_integral_quotient(z_plus)
        + sine_integral_quotient(z_minus)
    )


def multiplier_and_derivative(
    t: arb,
    integration_cutoff: arb,
    tolerance: arb,
    eval_limit: int,
) -> tuple[arb, arb]:
    """Return the center enclosures before the explicit tail-error charge."""

    def integrand(x: acb, _analytic: bool) -> acb:
        phase = acb(t) * x
        # The imaginary part is d/dt of the real cosine integral.
        return delta_log_coordinate(x) * (
            phase.cos() - 1j * x * phase.sin()
        )

    integral_pair = acb.integral(
        integrand,
        arb(0),
        integration_cutoff,
        abs_tol=tolerance,
        rel_tol=tolerance,
        eval_limit=eval_limit,
        depth_limit=30,
    )

    alpha = arb(1) / 2
    z = acb(alpha, -t)
    exponential = (-z * integration_cutoff).exp()
    leading_tail = exponential / z
    leading_tail_derivative = 1j * exponential * (
        integration_cutoff / z + 1 / z**2
    )

    spectral_point = acb(arb(1) / 4, t / 2)
    theta_term = -arb.pi().log() + spectral_point.digamma().real
    theta_derivative = -spectral_point.polygamma(1).imag / 2

    multiplier = (
        theta_term
        + 2 * integral_pair.real
        + 2 * leading_tail.real
    )
    derivative = (
        theta_derivative
        + 2 * integral_pair.imag
        + 2 * leading_tail_derivative.real
    )
    return multiplier, derivative


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--bits", type=int, default=80)
    parser.add_argument("--step-denominator", type=int, default=25)
    parser.add_argument("--compact-max", type=int, default=50)
    parser.add_argument("--integration-cutoff", type=int, default=8)
    parser.add_argument("--tolerance", default="1e-9")
    parser.add_argument("--eval-limit", type=int, default=120000)
    args = parser.parse_args()

    ctx.prec = args.bits
    step = arb(1) / args.step_denominator
    radius = step / 2
    compact_max = arb(args.compact_max)
    integration_cutoff = arb(args.integration_cutoff)
    tolerance = arb(args.tolerance)
    target = arb(1) / 50
    second_derivative_bound = arb(100)

    beta = arb(3) / 2
    tail_exponential = (-beta * integration_cutoff).exp()
    value_tail_error = arb(4) / beta * tail_exponential
    derivative_tail_error = 4 * tail_exponential * (
        integration_cutoff / beta + 1 / beta**2
    )

    grid_count = args.compact_max * args.step_denominator + 1
    minimum_lower = None
    minimum_index = None
    for index in range(grid_count):
        t = arb(index) / args.step_denominator
        value, derivative = multiplier_and_derivative(
            t,
            integration_cutoff,
            tolerance,
            args.eval_limit,
        )
        taylor_lower = (
            value
            - value_tail_error
            - (abs(derivative) + derivative_tail_error) * radius
            - second_derivative_bound * radius**2 / 2
        )
        if not taylor_lower > target:
            raise AssertionError(
                "compact certificate failed at "
                f"index={index}, t={t}, lower={taylor_lower}"
            )
        lower_float = float(taylor_lower.lower())
        if minimum_lower is None or lower_float < minimum_lower:
            minimum_lower = lower_float
            minimum_index = index
        if index and index % 250 == 0:
            print(
                f"progress={index}/{grid_count - 1} "
                f"minimum_lower={minimum_lower:.12f}"
            )

    endpoint = arb(args.compact_max)
    endpoint_spectral_point = acb(arb(1) / 4, endpoint / 2)
    endpoint_theta = (
        -arb.pi().log() + endpoint_spectral_point.digamma().real
    )
    tail_lower = endpoint_theta - arb(100) / endpoint
    if not tail_lower > target:
        raise AssertionError(
            f"large-t certificate failed: lower={tail_lower}"
        )

    print(f"grid_count={grid_count}")
    print(f"compact_interval=[0,{args.compact_max}]")
    print(f"taylor_radius={radius}")
    print(f"value_tail_error={value_tail_error}")
    print(f"derivative_tail_error={derivative_tail_error}")
    print(f"minimum_compact_lower={minimum_lower:.15f}")
    print(
        "minimum_compact_location="
        f"{minimum_index / args.step_denominator:.12f}"
    )
    print(f"large_t_lower={tail_lower}")
    print("certificate=ell_CC20(t) > 1/50 for every real t")


if __name__ == "__main__":
    main()
