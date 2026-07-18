"""Finite certificate for Proof 378's closed midpoint detector row."""

from __future__ import annotations

import argparse
import math

import numpy as np


def shift_matrix(size: int) -> np.ndarray:
    shift = np.zeros((size, size), dtype=complex)
    for column in range(size - 1):
        shift[column + 1, column] = 1.0
    return shift


def shift_power(shift: np.ndarray, exponent: int) -> np.ndarray:
    if exponent >= 0:
        return np.linalg.matrix_power(shift, exponent)
    return np.linalg.matrix_power(shift.conj().T, -exponent)


def range_projection(frame: np.ndarray) -> np.ndarray:
    orthonormal, triangular = np.linalg.qr(frame, mode="reduced")
    if float(np.min(np.abs(np.diag(triangular)))) <= 1e-12:
        raise ValueError("transported range lost rank")
    return orthonormal @ orthonormal.conj().T


def transported_sonin_projection(
    multiplier: np.ndarray,
    ambient_size: int,
    offset: int,
    model_dimension: int,
) -> np.ndarray:
    frame = np.zeros((ambient_size, model_dimension), dtype=complex)
    for column in range(model_dimension):
        start = offset + column
        frame[start : start + len(multiplier), column] = multiplier
    return range_projection(frame)


def canonical_midpoint(first: np.ndarray, second: np.ndarray) -> np.ndarray:
    bisector = first + second - np.eye(first.shape[0], dtype=complex)
    eigenvalues, eigenvectors = np.linalg.eigh(bisector)
    if float(np.min(np.abs(eigenvalues))) <= 1e-9:
        raise ValueError("canonical midpoint lost its strict angle")
    symmetry = eigenvectors @ np.diag(np.sign(eigenvalues)) @ eigenvectors.conj().T
    return 0.5 * (np.eye(first.shape[0], dtype=complex) + symmetry)


def relative_error(actual: complex | np.ndarray, expected: complex | np.ndarray) -> float:
    return float(
        np.linalg.norm(np.asarray(actual) - np.asarray(expected))
        / max(1.0, float(np.linalg.norm(np.asarray(expected))))
    )


def certificate(
    ambient_size: int,
    offset: int,
    model_dimension: int,
    seed: int,
) -> dict[str, float]:
    identity = np.eye(ambient_size, dtype=complex)
    shift = shift_matrix(ambient_size)
    outer = np.zeros((ambient_size, ambient_size), dtype=complex)
    outer[offset:, offset:] = np.eye(ambient_size - offset, dtype=complex)

    rng = np.random.default_rng(seed)
    root = np.zeros_like(shift)
    root_budget = 0.0
    for exponent in range(-4, 5):
        coefficient = (rng.normal() + 1j * rng.normal()) / (
            5.0 * (1.0 + abs(exponent)) ** 2
        )
        root += coefficient * shift_power(shift, exponent)
        if exponent != 0:
            root_budget += math.sqrt(abs(exponent)) * abs(coefficient)
    detector = root.conj().T @ root
    root_norm = float(np.linalg.norm(root, 2))
    single_projection_bound = math.sqrt(2.0) * root_budget
    endpoint_bound = 4.0 * single_projection_bound**2

    primes = [3, 5, 7, 11, 13, 17]
    delays = [1, 2, 3, 4, 5, 6]
    multiplier = np.array([1.0 + 0.0j])
    sonin_projections = [
        transported_sonin_projection(
            multiplier,
            ambient_size,
            offset,
            model_dimension,
        )
    ]
    for prime, delay in zip(primes, delays, strict=True):
        factor = np.zeros(delay + 1, dtype=complex)
        factor[0] = 1.0
        factor[delay] = -(prime**-0.5)
        multiplier = np.convolve(multiplier, factor)
        sonin_projections.append(
            transported_sonin_projection(
                multiplier,
                ambient_size,
                offset,
                model_dimension,
            )
        )

    quotient_projections = [outer - sonin for sonin in sonin_projections]
    endpoint_energies = [
        float(np.linalg.norm(root @ projection - projection @ root, "fro") ** 2)
        for projection in quotient_projections
    ]
    maximum_endpoint_violation = max(endpoint_energies) - endpoint_bound

    midpoint_constant = (math.sqrt(2.0) + 2.0) / 2.0
    maximum_midpoint_error = 0.0
    maximum_detector_violation = 0.0
    weighted_detector_energy = 0.0
    weighted_detector_bound = 0.0
    response_sum = 0.0 + 0.0j

    for index, prime in enumerate(primes):
        first = quotient_projections[index]
        second = quotient_projections[index + 1]
        midpoint = canonical_midpoint(first, second)
        difference = second - first
        complement = identity - midpoint
        range_corner = complement @ difference @ midpoint
        detector_corner = complement @ detector @ midpoint

        diagonal_error = max(
            np.linalg.norm(midpoint @ difference @ midpoint),
            np.linalg.norm(complement @ difference @ complement),
        )
        response = np.trace(detector @ difference)
        paired = 2.0 * np.real(
            np.trace(detector_corner.conj().T @ range_corner)
        )
        maximum_midpoint_error = max(
            maximum_midpoint_error,
            float(diagonal_error),
            relative_error(response, paired),
        )
        response_sum += response

        midpoint_commutator = root @ midpoint - midpoint @ root
        detector_energy = float(np.linalg.norm(detector_corner, "fro") ** 2)
        root_reduction_bound = 2.0 * root_norm**2 * float(
            np.linalg.norm(midpoint_commutator, "fro") ** 2
        )
        transfer_bound = 4.0 * midpoint_constant**2 * root_norm**2 * (
            endpoint_energies[index] + endpoint_energies[index + 1]
        )
        maximum_detector_violation = max(
            maximum_detector_violation,
            detector_energy - root_reduction_bound,
            detector_energy - transfer_bound,
        )
        weighted_detector_energy += detector_energy / (prime - 1.0)
        weighted_detector_bound += transfer_bound / (prime - 1.0)

    endpoint_response = np.trace(
        detector @ (quotient_projections[-1] - quotient_projections[0])
    )
    telescope_error = relative_error(response_sum, endpoint_response)
    harmonic_violation = weighted_detector_energy - weighted_detector_bound

    return {
        "maximum endpoint bound violation": max(0.0, maximum_endpoint_violation),
        "maximum midpoint exact error": maximum_midpoint_error,
        "maximum detector bound violation": max(0.0, maximum_detector_violation),
        "harmonic row violation": max(0.0, harmonic_violation),
        "endpoint telescope error": telescope_error,
        "maximum endpoint energy": max(endpoint_energies),
        "endpoint universal bound": endpoint_bound,
        "weighted detector energy": weighted_detector_energy,
        "weighted detector bound": weighted_detector_bound,
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--ambient-size", type=int, default=144)
    parser.add_argument("--offset", type=int, default=38)
    parser.add_argument("--model-dimension", type=int, default=10)
    parser.add_argument("--seed", type=int, default=378)
    parser.add_argument("--tolerance", type=float, default=3e-9)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    checks = certificate(
        args.ambient_size,
        args.offset,
        args.model_dimension,
        args.seed,
    )
    print("Proof 378 nearly-invariant detector-row certificate")
    for label, value in checks.items():
        print(f"{label.replace(' ', '_')}={value:.12e}")

    exact_labels = [
        "maximum endpoint bound violation",
        "maximum midpoint exact error",
        "maximum detector bound violation",
        "harmonic row violation",
        "endpoint telescope error",
    ]
    maximum_error = max(checks[label] for label in exact_labels)
    if maximum_error > args.tolerance:
        raise RuntimeError(f"near detector-row assembly failed: {maximum_error:.3e}")

    print(f"maximum_error_or_violation={maximum_error:.12e}")
    print("endpoint_MR6=PASS")
    print("midpoint_detector_row=PASS")
    print("near_detector_row=MATHEMATICALLY_CLOSED")
    print("root_split_same_object_factorization=OPEN")
    print("far_gate_3u=PROOF_336")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
