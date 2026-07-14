#!/usr/bin/env python3
"""Arb certificate against the row-only archimedean sign.

The target is the continuous CC20 form

    D_infinity = -2 Id + K_infinity

on one compact logarithmic interval. We impose the two independent pre-root
rows M_0(xi)=M_1(xi)=0 and give a fixed four-mode Dirichlet witness. The
finite-S scattering correction is deliberately absent: this is a standalone
certificate for the archimedean row-only claim.

After two integrations by parts, the Dirac jump cancels the -2 Id term and
the quadratic form is

    <xi,D_infinity xi>
      = 2 integral_0^L delta(exp(t)) H_g(t) dt,

where g=(d/dx+1/2)xi and H_g is its one-sided autocorrelation. H_g is an exact
finite exponential sum, leaving only one rigorous Arb integral.
"""

from __future__ import annotations

import argparse

from flint import acb, arb, ctx, fmpq


HALF = fmpq(1, 2)
THREE_HALVES = fmpq(3, 2)
MODES = (1, 2, 3, 5)


def sine_integral_quotient(z: acb) -> acb:
    """Entire extension of Si(z)/z used by the CC20 delta profile."""
    return (-z * z / 4).hypgeom(
        [HALF], [THREE_HALVES, THREE_HALVES]
    )


def delta_log(t: acb) -> acb:
    """delta(exp(t)) in the logarithmic coordinate."""
    rho = t.exp()
    z_plus = 2 * acb.pi() * (1 + rho)
    z_minus = 2 * acb.pi() * (rho - 1)
    return 2 * (t / 2).exp() * (
        sine_integral_quotient(z_plus)
        + sine_integral_quotient(z_minus)
    )


def row_one_coefficient(
    n: int, length: arb, pi: arb, exp_length: arb
) -> arb:
    """M_1 coefficient of a sine mode, up to a common factor."""
    frequency = arb(n) * pi / length
    parity = (-1) ** n
    return frequency * (1 - parity * exp_length) / (
        1 + frequency * frequency
    )


def witness_data() -> tuple[arb, dict[int, arb], arb, arb, arb]:
    """Return L, coefficients, row residuals, and norm squared."""
    length = arb(3) / 2 * arb(2).log()
    pi = arb.pi()
    # exp(3 log(2)/2) = 2 sqrt(2).
    exp_length = 2 * arb(2).sqrt()
    coefficients = {
        1: -arb(8) / 15,
        3: arb(1),
        5: arb(1),
    }
    row_one = {
        n: row_one_coefficient(n, length, pi, exp_length)
        for n in MODES
    }
    # M_0 is -8/15 + 1/3 + 1/5 = 0. Solve M_1 for c_2.
    coefficients[2] = -sum(
        coefficients[n] * row_one[n] for n in (1, 3, 5)
    ) / row_one[2]
    row_zero_residual = (
        coefficients[1]
        + coefficients[3] / 3
        + coefficients[5] / 5
    )
    row_one_residual = sum(
        coefficients[n] * row_one[n] for n in MODES
    )
    norm_squared = sum(
        coefficients[n] * coefficients[n] for n in MODES
    )
    return (
        length,
        coefficients,
        row_zero_residual,
        row_one_residual,
        norm_squared,
    )


def autocorrelation(
    length: arb, coefficients: dict[int, arb], t: acb
) -> acb:
    """H_g(t)=integral_0^(L-t) g(x+t) g(x) dx as a finite sum."""
    frequency_unit = arb.pi() / length
    normalization = (arb(2) / length).sqrt()
    exponential_coefficients: dict[int, acb] = {}
    for mode in MODES:
        frequency = arb(mode) * frequency_unit
        # g has sine amplitude normalization*c/2, and the coefficient of
        # exp(+i n pi x/L) is amplitude/(2i).
        sine_coefficient = normalization * coefficients[mode] / 4
        cosine_coefficient = (
            normalization * coefficients[mode] * frequency / 2
        )
        exponential_coefficients[mode] = acb(
            cosine_coefficient, -sine_coefficient
        )
        exponential_coefficients[-mode] = acb(
            cosine_coefficient, sine_coefficient
        )

    result = acb(0)
    for left_mode, left_coefficient in exponential_coefficients.items():
        phase = (
            acb(0, arb(left_mode) * frequency_unit) * t
        ).exp()
        for right_mode, right_coefficient in (
            exponential_coefficients.items()
        ):
            total_mode = left_mode + right_mode
            if total_mode == 0:
                integrated_phase = length - t
            else:
                integrated_phase = (
                    ((-1) ** total_mode)
                    * (
                        acb(0, -arb(total_mode) * frequency_unit) * t
                    ).exp()
                    - 1
                ) / acb(0, arb(total_mode) * frequency_unit)
            result += (
                left_coefficient
                * right_coefficient
                * phase
                * integrated_phase
            )
    return result


def integrate_certificate(
    length: arb,
    coefficients: dict[int, arb],
    pieces: int,
    tolerance: arb,
    eval_limit: int,
) -> acb:
    """Split the one-dimensional form integral into rigorous Arb pieces."""

    def integrand(t: acb, _analytic: bool) -> acb:
        return 2 * delta_log(t) * autocorrelation(
            length, coefficients, t
        )

    result = acb(0)
    for index in range(pieces):
        left = length * arb(index) / pieces
        right = length * arb(index + 1) / pieces
        result += acb.integral(
            integrand,
            left,
            right,
            abs_tol=tolerance,
            rel_tol=tolerance,
            eval_limit=eval_limit,
            depth_limit=30,
        )
    return result


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--bits", type=int, default=100)
    parser.add_argument("--pieces", type=int, default=8)
    parser.add_argument("--tolerance", default="1e-18")
    parser.add_argument("--eval-limit", type=int, default=100000)
    args = parser.parse_args()
    if args.bits < 40:
        raise ValueError("at least 40 Arb bits are required")
    if args.pieces < 1:
        raise ValueError("pieces must be positive")

    ctx.prec = args.bits
    (
        length,
        coefficients,
        row_zero_residual,
        row_one_residual,
        norm_squared,
    ) = witness_data()
    quadratic = integrate_certificate(
        length,
        coefficients,
        args.pieces,
        arb(args.tolerance),
        args.eval_limit,
    ).real
    rayleigh = quadratic / norm_squared
    if not quadratic > arb(1):
        raise AssertionError(
            f"quadratic lower bound failed: {quadratic}"
        )
    if not rayleigh > arb(1) / 2:
        raise AssertionError(f"Rayleigh lower bound failed: {rayleigh}")

    print(f"interval=[0,{length}]")
    print(f"modes={MODES}")
    print(f"coefficients={coefficients}")
    print(f"M0_residual={row_zero_residual}")
    print(f"M1_residual={row_one_residual}")
    print(f"norm_squared={norm_squared}")
    print(f"quadratic_lower={quadratic.lower()}")
    print(f"quadratic_upper={quadratic.upper()}")
    print(f"rayleigh_lower={rayleigh.lower()}")
    print(f"rayleigh_upper={rayleigh.upper()}")
    print("certificate=archimedean row-only sign is false")


if __name__ == "__main__":
    main()
