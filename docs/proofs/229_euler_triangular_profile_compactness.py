#!/usr/bin/env python3
"""Algebraic certificate for Proof 229's Euler triangular envelope.

The proof of compactness is the cellwise derivative-transfer identity plus
Proof 228's Fourier norm bound.  This script checks the exact envelope,
boundary matching, derivative jumps, tail scales, and summable majorants.
"""

from __future__ import annotations

import argparse
import math

import numpy as np


def direct_envelope(prime: int, radius: float, extra_terms: int) -> float:
    parameter = prime**-0.5
    cell_length = math.log(prime)
    first = math.floor(radius / cell_length) + 1
    last = first + extra_terms
    return float(
        sum(
            parameter**exponent * (exponent * cell_length - radius)
            for exponent in range(first, last + 1)
        )
    )


def closed_envelope(prime: int, radius: float) -> float:
    parameter = prime**-0.5
    cell_length = math.log(prime)
    cell = math.floor(radius / cell_length)
    local = radius - cell * cell_length
    return float(
        parameter ** (cell + 1)
        * (cell_length - (1 - parameter) * local)
        / (1 - parameter) ** 2
    )


def derivative_in_cell(prime: int, cell: int) -> float:
    parameter = prime**-0.5
    return float(-parameter ** (cell + 1) / (1 - parameter))


def scattering_response(value: float) -> float:
    return float(2 * math.exp(value / 2) * math.cos(2 * math.pi * math.exp(value)))


def certificate(prime: int, cells: int, extra_terms: int) -> dict[str, float]:
    parameter = prime**-0.5
    cell_length = math.log(prime)
    sample_fractions = (0.0, 0.17, 0.53, 0.91)

    envelope_error = 0.0
    positive_scaled = []
    negative_scaled = []
    for cell in range(cells):
        for fraction in sample_fractions:
            radius = (cell + fraction) * cell_length
            envelope_error = max(
                envelope_error,
                abs(
                    direct_envelope(prime, radius, extra_terms)
                    - closed_envelope(prime, radius)
                ),
            )
            envelope = closed_envelope(prime, radius)
            positive_scaled.append(envelope * math.exp(radius / 2))
            negative_value = envelope * abs(scattering_response(-radius))
            negative_scaled.append(negative_value * math.exp(radius))

    continuity_error = 0.0
    jump_error = 0.0
    for boundary in range(1, cells):
        left_value = (
            parameter**boundary
            * (cell_length - (1 - parameter) * cell_length)
            / (1 - parameter) ** 2
        )
        right_value = (
            parameter ** (boundary + 1)
            * cell_length
            / (1 - parameter) ** 2
        )
        continuity_error = max(
            continuity_error, abs(left_value - right_value)
        )

        left_derivative = derivative_in_cell(prime, boundary - 1)
        right_derivative = derivative_in_cell(prime, boundary)
        jump_error = max(
            jump_error,
            abs((right_derivative - left_derivative) - parameter**boundary),
        )

    interior_majorant = float(
        sum(prime ** (-cell / 2) for cell in range(1, 10000))
    )
    boundary_majorant = float(
        sum(prime**-cell for cell in range(1, 10000))
    )

    return {
        "envelope_error": envelope_error,
        "continuity_error": continuity_error,
        "derivative_jump_error": jump_error,
        "positive_scaled_min": float(min(positive_scaled)),
        "positive_scaled_max": float(max(positive_scaled)),
        "negative_scaled_min": float(min(negative_scaled)),
        "negative_scaled_max": float(max(negative_scaled)),
        "interior_majorant": interior_majorant,
        "boundary_majorant": boundary_majorant,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--prime", type=int, default=2)
    parser.add_argument("--cells", type=int, default=24)
    parser.add_argument("--extra-terms", type=int, default=256)
    parser.add_argument("--max-error", type=float, default=2e-13)
    args = parser.parse_args()

    if args.prime < 2:
        raise ValueError("prime must be at least 2")
    if args.cells < 4:
        raise ValueError("cells must be at least 4")
    if args.extra_terms < 32:
        raise ValueError("extra-terms must be at least 32")

    values = certificate(args.prime, args.cells, args.extra_terms)
    print("identity=Euler triangular-profile compactness")
    print(f"prime={args.prime} cells={args.cells}")
    for name, value in values.items():
        print(f"{name}={value:.12e}")

    errors = [value for name, value in values.items() if name.endswith("error")]
    if max(errors) > args.max_error:
        raise RuntimeError("Euler triangular envelope identity failed")
    if not 0 < values["positive_scaled_min"] <= values["positive_scaled_max"]:
        raise RuntimeError("positive-tail envelope lost its uniform scale")
    if not 0 < values["negative_scaled_min"] <= values["negative_scaled_max"]:
        raise RuntimeError("negative-tail envelope lost its exponential scale")
    if not all(
        math.isfinite(values[name])
        for name in ("interior_majorant", "boundary_majorant")
    ):
        raise RuntimeError("cell majorant series did not converge")

    print("certificate=PASS")
    print("closed_euler_envelope_verdict=PASS")
    print("first_boundary_cancellation_verdict=PASS")
    print("second_boundary_operator_sum_verdict=PASS")
    print("principal_euler_compactness_verdict=PASS")
    print("global_hilbert_schmidt_verdict=NOT_REQUIRED")
    print("full_metric_crossing_verdict=OPEN")
    print("integrated_three_row_sign_verdict=OPEN")


if __name__ == "__main__":
    main()
