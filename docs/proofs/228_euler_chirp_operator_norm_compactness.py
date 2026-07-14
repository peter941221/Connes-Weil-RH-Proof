#!/usr/bin/env python3
"""Nyström certificate for Proof 228's logarithmic chirp bound.

The proof is the exact change of variables from a logarithmic chirp to a
truncated scaled Fourier transform.  This script independently checks the
endpoint identities and the contrasting operator/HS norm scalings.

It does not prove the complete internal-profile estimate from Proof 227.
"""

from __future__ import annotations

import argparse
import math

import numpy as np


def scattering_response(values: np.ndarray) -> np.ndarray:
    return 2 * np.exp(values / 2) * np.cos(2 * np.pi * np.exp(values))


def trapezoid_weights(size: int, step: float) -> np.ndarray:
    weights = np.full(size, step)
    weights[0] *= 0.5
    weights[-1] *= 0.5
    return weights


def endpoint_identity_errors(
    prime: int, modes: int, differences: np.ndarray
) -> tuple[float, float]:
    parameter = prime**-0.5
    cell_length = math.log(prime)
    positive_error = 0.0
    negative_error = 0.0
    for exponent in range(1, modes + 1):
        frequency = prime**exponent
        shift = exponent * cell_length
        positive_left = parameter**exponent * scattering_response(
            differences + shift
        )
        positive_right = 2 * np.exp(differences / 2) * np.cos(
            2 * np.pi * frequency * np.exp(differences)
        )
        negative_left = parameter**exponent * scattering_response(
            differences - shift
        )
        negative_right = 2 * prime**(-exponent) * np.exp(
            differences / 2
        ) * np.cos(2 * np.pi * prime**(-exponent) * np.exp(differences))
        positive_error = max(
            positive_error,
            float(np.max(np.abs(positive_left - positive_right))),
        )
        negative_error = max(
            negative_error,
            float(np.max(np.abs(negative_left - negative_right))),
        )
    return positive_error, negative_error


def chirp_norms(
    prime: int, modes: int, size: int, interval_bound: float
) -> list[tuple[int, float, float, float, float]]:
    points = np.linspace(-interval_bound, interval_bound, size)
    step = float(points[1] - points[0])
    weights = trapezoid_weights(size, step)
    weighted = np.sqrt(weights)
    differences = points[:, None] - points[None, :]
    amplitude = np.exp(differences / 2)
    results = []

    for exponent in range(1, modes + 1):
        frequency = prime**exponent
        phase = 2 * np.pi * frequency * np.exp(differences)
        kernel = amplitude * np.exp(1j * phase)
        matrix = weighted[:, None] * kernel * weighted[None, :]
        singular_values = np.linalg.svd(matrix, compute_uv=False)
        operator_norm = float(singular_values[0])
        hilbert_schmidt_norm = float(np.linalg.norm(matrix, ord="fro"))
        bound = frequency**-0.5
        phase_step = float(
            2
            * np.pi
            * frequency
            * math.exp(2 * interval_bound)
            * step
        )
        results.append(
            (
                exponent,
                operator_norm,
                hilbert_schmidt_norm,
                bound,
                phase_step,
            )
        )
    return results


def polynomial_bound_sum(prime: int, power: int, terms: int = 10000) -> float:
    return float(
        sum(
            exponent**power * prime ** (-exponent / 2)
            for exponent in range(1, terms + 1)
        )
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--prime", type=int, default=2)
    parser.add_argument("--modes", type=int, default=8)
    parser.add_argument("--grid-size", type=int, default=800)
    parser.add_argument(
        "--interval-bound", type=float, default=0.5 * math.log(2)
    )
    parser.add_argument("--max-identity-error", type=float, default=2e-11)
    parser.add_argument("--bound-slack", type=float, default=1.03)
    parser.add_argument("--max-phase-step", type=float, default=2.8)
    parser.add_argument("--max-hs-relative-spread", type=float, default=2e-12)
    args = parser.parse_args()

    if args.prime < 2:
        raise ValueError("prime must be at least 2")
    if args.modes < 2:
        raise ValueError("modes must be at least 2")
    if args.grid_size < 128:
        raise ValueError("grid-size must be at least 128")
    if args.interval_bound <= 0:
        raise ValueError("interval-bound must be positive")

    differences = np.linspace(
        -2 * args.interval_bound, 2 * args.interval_bound, 257
    )
    positive_error, negative_error = endpoint_identity_errors(
        args.prime, args.modes, differences
    )
    results = chirp_norms(
        args.prime, args.modes, args.grid_size, args.interval_bound
    )

    print("identity=Euler logarithmic chirp operator-norm compactness")
    print(f"prime={args.prime} modes={args.modes}")
    print(f"positive_endpoint_identity_error={positive_error:.3e}")
    print(f"negative_endpoint_identity_error={negative_error:.3e}")
    print("mode_table=BEGIN")
    for exponent, operator_norm, hs_norm, bound, phase_step in results:
        print(
            f"m={exponent} lambda={args.prime**exponent} "
            f"operator_norm={operator_norm:.12f} "
            f"fourier_bound={bound:.12f} "
            f"hs_norm={hs_norm:.12f} "
            f"phase_step={phase_step:.6f}"
        )
    print("mode_table=END")

    hs_norms = np.array([result[2] for result in results])
    hs_relative_spread = float(
        (np.max(hs_norms) - np.min(hs_norms)) / np.mean(hs_norms)
    )
    quadratic_bound_sum = polynomial_bound_sum(args.prime, 2)
    print(f"hs_relative_spread={hs_relative_spread:.3e}")
    print(f"quadratic_weight_bound_sum={quadratic_bound_sum:.12f}")

    if max(positive_error, negative_error) > args.max_identity_error:
        raise RuntimeError("Euler endpoint identity failed")
    if max(result[4] for result in results) > args.max_phase_step:
        raise RuntimeError("grid does not resolve the fastest chirp")
    if any(
        result[1] > args.bound_slack * result[3] for result in results
    ):
        raise RuntimeError("discrete chirp norm exceeded the Fourier bound")
    if hs_relative_spread > args.max_hs_relative_spread:
        raise RuntimeError("positive-frequency HS norm should not decay")
    if not math.isfinite(quadratic_bound_sum):
        raise RuntimeError("polynomially weighted norm bound did not converge")

    print("certificate=PASS")
    print("chirp_fourier_conjugation_verdict=PASS")
    print("operator_norm_euler_sum_verdict=PASS")
    print("absolute_hs_sum_verdict=REJECTED_AS_UNNECESSARY")
    print("complete_internal_profile_verdict=OPEN")
    print("integrated_three_row_sign_verdict=OPEN")


if __name__ == "__main__":
    main()
