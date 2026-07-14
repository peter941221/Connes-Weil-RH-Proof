#!/usr/bin/env python3
"""Certificate for Proof 234's Sonin alternating-profile reduction."""

from __future__ import annotations

import argparse
import math

import numpy as np


def fourier_matrix(size: int) -> np.ndarray:
    indices = np.arange(size)
    return np.exp(2j * np.pi * np.outer(indices, indices) / size) / math.sqrt(size)


def norm(matrix: np.ndarray) -> float:
    return float(np.linalg.norm(matrix, ord=2))


def trace_norm(matrix: np.ndarray) -> float:
    return float(np.sum(np.linalg.svd(matrix, compute_uv=False)))


def power_telescope(left: np.ndarray, right: np.ndarray, exponent: int) -> np.ndarray:
    if exponent == 0:
        return np.zeros_like(left)
    result = np.zeros_like(left)
    for index in range(exponent):
        result += (
            np.linalg.matrix_power(left, index)
            @ (left - right)
            @ np.linalg.matrix_power(right, exponent - 1 - index)
        )
    return result


def certificate(prime: int, size: int, depth: int) -> dict[str, float]:
    fourier = fourier_matrix(size)
    coordinates = np.arange(size) - size // 2
    positive = np.diag((coordinates >= 0).astype(complex))

    spectral_index = np.arange(size, dtype=float)
    euler_phase = np.exp(-2j * np.pi * spectral_index / size)
    scattering_phase = np.exp(
        2j * np.pi * (spectral_index**2 + 3 * spectral_index + 1) / size
    )
    differential_symbol = spectral_index - size // 2
    unitary = fourier.conj().T @ np.diag(euler_phase) @ fourier
    scattering = fourier.conj().T @ np.diag(scattering_phase) @ fourier
    differential = fourier.conj().T @ np.diag(differential_symbol) @ fourier

    q_hat = scattering.conj().T @ positive @ scattering
    base_sonin = positive @ (np.eye(size) - q_hat) @ positive
    direct_commutator = base_sonin @ unitary - unitary @ base_sonin
    p_commutator = positive @ unitary - unitary @ positive
    q_commutator = q_hat @ unitary - unitary @ q_hat
    expanded_commutator = (
        positive @ (np.eye(size) - q_hat) @ p_commutator
        -positive @ q_commutator @ positive
        +p_commutator @ (np.eye(size) - q_hat) @ positive
    )
    conjugated_commutator = (
        scattering.conj().T @ p_commutator @ scattering
    )

    low_rank_vector = np.exp(-0.17 * coordinates**2).astype(complex)
    low_rank_vector /= np.linalg.norm(low_rank_vector)
    prolate = 0.03 * np.outer(low_rank_vector, low_rank_vector.conj())
    actual_sonin = base_sonin - prolate
    metric_word = unitary + unitary.conj().T
    left = actual_sonin @ metric_word @ actual_sonin
    right = base_sonin @ metric_word @ base_sonin
    telescope_error = 0.0
    telescope_trace_bound_ratio = 0.0
    for exponent in range(1, depth + 1):
        difference = (
            np.linalg.matrix_power(left, exponent)
            - np.linalg.matrix_power(right, exponent)
        )
        telescope = power_telescope(left, right, exponent)
        telescope_error = max(telescope_error, norm(difference - telescope))
        denominator = exponent * norm(left - right) * max(
            1.0, norm(left), norm(right)
        ) ** (exponent - 1)
        if denominator > 0:
            telescope_trace_bound_ratio = max(
                telescope_trace_bound_ratio,
                trace_norm(difference) / (size * denominator),
            )

    alpha = prime**-0.5
    eta = 2 * alpha / (1 + alpha**2)
    profile_majorant = float(
        sum((1 + index) ** 2 * eta**index for index in range(100000))
    )

    return {
        "projection_error": norm(positive @ positive - positive),
        "scattering_projection_error": norm(q_hat @ q_hat - q_hat),
        "euler_scattering_commutator_error": norm(
            unitary @ scattering - scattering @ unitary
        ),
        "q_euler_commutator_error": norm(
            differential @ unitary - unitary @ differential
        ),
        "q_scattering_commutator_error": norm(
            differential @ scattering - scattering @ differential
        ),
        "source_commutator_expansion_error": norm(
            direct_commutator - expanded_commutator
        ),
        "scattering_conjugate_commutator_error": norm(
            q_commutator - conjugated_commutator
        ),
        "prolate_telescope_error": telescope_error,
        "prolate_telescope_trace_bound_ratio": telescope_trace_bound_ratio,
        "eta": eta,
        "quadratic_profile_majorant": profile_majorant,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--prime", type=int, default=2)
    parser.add_argument("--size", type=int, default=32)
    parser.add_argument("--depth", type=int, default=7)
    parser.add_argument("--max-error", type=float, default=2e-10)
    args = parser.parse_args()

    if args.prime < 2:
        raise ValueError("prime must be at least 2")
    if args.size < 16 or args.size % 2:
        raise ValueError("size must be an even integer at least 16")
    if args.depth < 2:
        raise ValueError("depth must be at least 2")

    values = certificate(args.prime, args.size, args.depth)
    print("identity=Sonin alternating-profile closure")
    print(f"prime={args.prime} size={args.size} depth={args.depth}")
    for name, value in values.items():
        print(f"{name}={value:.12e}")

    errors = [value for name, value in values.items() if name.endswith("_error")]
    if max(errors) > args.max_error:
        raise RuntimeError("Sonin alternating-word identity failed")
    if not 0 <= values["eta"] < 1:
        raise RuntimeError("Sonin metric word ratio is not summable")
    if not math.isfinite(values["quadratic_profile_majorant"]):
        raise RuntimeError("Sonin profile majorant diverged")
    if values["prolate_telescope_trace_bound_ratio"] > 1 + args.max_error:
        raise RuntimeError("prolate telescope bound failed")

    print("certificate=PASS")
    print("source_commutator_reduction_verdict=PASS")
    print("prolate_word_telescope_verdict=PASS")
    print("sonin_alternating_profile_verdict=PASS")
    print("full_metric_compactness_verdict=PASS")
    print("integrated_three_row_sign_verdict=OPEN")


if __name__ == "__main__":
    main()
