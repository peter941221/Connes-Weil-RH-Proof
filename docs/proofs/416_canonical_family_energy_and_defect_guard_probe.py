#!/usr/bin/env python3
"""Finite certificate for Proof 416's Bernstein--Szego response."""

from __future__ import annotations

import argparse
import math

import numpy as np


def inverse_power_coefficients(power: int, radius: float, count: int) -> np.ndarray:
    """Taylor coefficients of (1-radius*z)^(-power)."""
    return np.array(
        [math.comb(power + index - 1, index) * radius**index for index in range(count)],
        dtype=np.float64,
    )


def correlation(coefficients: np.ndarray) -> np.ndarray:
    """Nonnegative Fourier coefficients of the squared boundary modulus."""
    count = coefficients.size
    return np.correlate(coefficients, coefficients, mode="full")[count - 1 :]


def moment(correlation_values: np.ndarray, index: int) -> float:
    return float(correlation_values[abs(index)])


def gram_and_shift_moment(
    dimension: int, correlation_values: np.ndarray
) -> tuple[np.ndarray, np.ndarray]:
    gram = np.array(
        [
            [moment(correlation_values, column - row) for column in range(dimension)]
            for row in range(dimension)
        ],
        dtype=np.float64,
    )
    shifted = np.array(
        [
            [
                moment(correlation_values, column + 1 - row)
                for column in range(dimension)
            ]
            for row in range(dimension)
        ],
        dtype=np.float64,
    )
    return gram, shifted


def monic_polynomial(power: int, radius: float, dimension: int) -> np.ndarray:
    """Coefficients of z^(dimension-power)*(z-radius)^power."""
    coefficients = np.zeros(dimension + 1, dtype=np.float64)
    for index in range(power + 1):
        degree = dimension - power + index
        coefficients[degree] = (
            math.comb(power, index) * (-radius) ** (power - index)
        )
    return coefficients


def orthogonality_residual(
    polynomial: np.ndarray, dimension: int, correlation_values: np.ndarray
) -> float:
    residual = 0.0
    for basis_degree in range(dimension):
        pairing = sum(
            coefficient
            * moment(correlation_values, basis_degree - polynomial_degree)
            for polynomial_degree, coefficient in enumerate(polynomial)
        )
        residual = max(residual, abs(pairing))
    return residual


def run_cohort(power: int, radius: float, dimension: int, series_terms: int) -> dict[str, float]:
    coefficients = inverse_power_coefficients(power, radius, series_terms)
    correlation_values = correlation(coefficients)
    gram, shifted = gram_and_shift_moment(dimension, correlation_values)
    normalized_shift = np.linalg.solve(gram, shifted)
    shift_trace = float(np.trace(normalized_shift))
    response = 2.0 * shift_trace
    expected_response = 2.0 * power * radius
    polynomial = monic_polynomial(power, radius, dimension)
    return {
        "power": float(power),
        "dimension": float(dimension),
        "condition": float(np.linalg.cond(gram)),
        "orthogonality": orthogonality_residual(
            polynomial, dimension, correlation_values
        ),
        "response": response,
        "expected": expected_response,
        "response_error": abs(response - expected_response),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--radius", type=float, default=0.3)
    parser.add_argument("--max-power", type=int, default=8)
    parser.add_argument("--dimension-padding", type=int, default=8)
    parser.add_argument("--series-terms", type=int, default=1024)
    args = parser.parse_args()

    if not 0.0 < args.radius < 0.65:
        raise SystemExit("--radius must lie in (0, 0.65) for this certificate")
    if args.max_power < 1:
        raise SystemExit("--max-power must be positive")

    powers = sorted({1, 2, 4, args.max_power})
    rows = []
    for power in powers:
        dimension = power + args.dimension_padding
        rows.append(run_cohort(power, args.radius, dimension, args.series_terms))

    print("+-------+-----------+---------------+---------------+---------------+")
    print("| power | dimension | response err  | orthog err    | cond(G)       |")
    print("+-------+-----------+---------------+---------------+---------------+")
    for row in rows:
        print(
            f"| {int(row['power']):5d} | {int(row['dimension']):9d} | "
            f"{row['response_error']:13.6e} | {row['orthogonality']:13.6e} | "
            f"{row['condition']:13.6e} |"
        )
    print("+-------+-----------+---------------+---------------+---------------+")

    maximum_response_error = max(row["response_error"] for row in rows)
    maximum_orthogonality_error = max(row["orthogonality"] for row in rows)
    largest_response = rows[-1]["response"]
    print(f"maximum_response_error={maximum_response_error:.12e}")
    print(f"maximum_orthogonality_error={maximum_orthogonality_error:.12e}")
    print(f"largest_exact_response={largest_response:.12e}")
    print("finite_defect_only_uniform_bound=REJECTED_ANALYTICALLY")
    print("canonical_energy_to_boundary_bound=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")

    tolerance = 2.0e-9
    if maximum_response_error > tolerance or maximum_orthogonality_error > tolerance:
        raise SystemExit("finite Bernstein--Szego certificate failed")


if __name__ == "__main__":
    main()
