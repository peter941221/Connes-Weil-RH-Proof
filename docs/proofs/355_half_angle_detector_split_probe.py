"""Finite certificate for Proof 355's half-angle detector split.

The script checks exact matrix identities and condition-number-free Schatten
bounds.  It does not prove the continuous old-crossing row, Gate 3U, or RH.
"""

from __future__ import annotations

import argparse
import math

import numpy as np


def random_isometry(
    ambient_size: int, rank: int, rng: np.random.Generator
) -> np.ndarray:
    matrix = rng.normal(size=(ambient_size, rank)) + 1j * rng.normal(
        size=(ambient_size, rank)
    )
    isometry, _ = np.linalg.qr(matrix)
    return isometry[:, :rank]


def orthogonal_complement(isometry: np.ndarray) -> np.ndarray:
    _, _, right_singular_vectors = np.linalg.svd(
        isometry.conj().T, full_matrices=True
    )
    return right_singular_vectors.conj().T[:, isometry.shape[1] :]


def positive_square_root(matrix: np.ndarray) -> np.ndarray:
    eigenvalues, eigenvectors = np.linalg.eigh(matrix)
    if float(np.min(eigenvalues)) < -1e-10:
        raise RuntimeError("matrix is not positive semidefinite")
    eigenvalues = np.maximum(eigenvalues, 0.0)
    return eigenvectors @ np.diag(np.sqrt(eigenvalues)) @ eigenvectors.conj().T


def inverse_positive_square_root(matrix: np.ndarray) -> np.ndarray:
    eigenvalues, eigenvectors = np.linalg.eigh(matrix)
    if float(np.min(eigenvalues)) <= 0.0:
        raise RuntimeError("matrix is not positive definite")
    return eigenvectors @ np.diag(eigenvalues ** -0.5) @ eigenvectors.conj().T


def projection_from_frame(frame: np.ndarray) -> np.ndarray:
    gram = frame.conj().T @ frame
    return frame @ np.linalg.inv(gram) @ frame.conj().T


def relative_error(actual: np.ndarray | complex, expected: np.ndarray | complex) -> float:
    actual_array = np.asarray(actual)
    expected_array = np.asarray(expected)
    return float(
        np.linalg.norm(actual_array - expected_array)
        / max(1.0, float(np.linalg.norm(expected_array)))
    )


def certificate(
    ambient_size: int,
    rank: int,
    primes: list[int],
    seed: int,
) -> dict[str, float]:
    rng = np.random.default_rng(seed)
    frequencies = rng.uniform(-3.0, 3.0, size=ambient_size)
    detector_values = (
        0.7
        + 0.25 * np.cos(1.3 * frequencies)
        + 0.15 * np.sin(0.8 * frequencies)
    )
    detector = np.diag(detector_values.astype(complex))
    current_isometry = random_isometry(ambient_size, rank, rng)
    identity = np.eye(ambient_size, dtype=complex)

    checks = {
        "Euler commutator error": 0.0,
        "direct rotation error": 0.0,
        "half rotation square error": 0.0,
        "midpoint projection error": 0.0,
        "detector split error": 0.0,
        "range singular-value error": 0.0,
        "off-diagonal bound violation": 0.0,
        "diagonal bound violation": 0.0,
        "total bound violation": 0.0,
    }

    for prime in primes:
        coefficient = prime ** -0.5
        translation = np.diag(
            np.exp(1j * math.log(prime) * frequencies)
        )
        checks["Euler commutator error"] = max(
            checks["Euler commutator error"],
            relative_error(detector @ translation, translation @ detector),
        )

        complement = orthogonal_complement(current_isometry)
        current_projection = current_isometry @ current_isometry.conj().T
        u10 = complement.conj().T @ translation @ current_isometry
        u11 = complement.conj().T @ translation @ complement
        graph = coefficient * np.linalg.solve(
            np.eye(u11.shape[0], dtype=complex) - coefficient * u11,
            u10,
        )
        cosine = inverse_positive_square_root(
            np.eye(rank, dtype=complex) + graph.conj().T @ graph
        )
        sine = graph @ cosine
        complement_cosine = positive_square_root(
            np.eye(ambient_size - rank, dtype=complex) - sine @ sine.conj().T
        )
        direct_rotation = np.block(
            [[cosine, -sine.conj().T], [sine, complement_cosine]]
        )

        half_cosine = positive_square_root(
            0.5 * (np.eye(rank, dtype=complex) + cosine)
        )
        half_sine = sine @ inverse_positive_square_root(
            2.0 * (np.eye(rank, dtype=complex) + cosine)
        )
        half_complement_cosine = positive_square_root(
            0.5
            * (
                np.eye(ambient_size - rank, dtype=complex)
                + complement_cosine
            )
        )
        half_rotation = np.block(
            [
                [half_cosine, -half_sine.conj().T],
                [half_sine, half_complement_cosine],
            ]
        )
        checks["direct rotation error"] = max(
            checks["direct rotation error"],
            relative_error(
                direct_rotation.conj().T @ direct_rotation,
                np.eye(ambient_size, dtype=complex),
            ),
        )
        checks["half rotation square error"] = max(
            checks["half rotation square error"],
            relative_error(half_rotation @ half_rotation, direct_rotation),
        )

        next_isometry = current_isometry @ cosine + complement @ sine
        next_projection = next_isometry @ next_isometry.conj().T
        midpoint_isometry = (
            current_isometry @ half_cosine + complement @ half_sine
        )
        midpoint_projection = midpoint_isometry @ midpoint_isometry.conj().T
        difference = next_projection - current_projection
        bisector = next_projection + current_projection - identity
        midpoint_from_sign = bisector @ inverse_positive_square_root(
            bisector @ bisector
        )
        midpoint_from_sign = 0.5 * (identity + midpoint_from_sign)
        checks["midpoint projection error"] = max(
            checks["midpoint projection error"],
            relative_error(midpoint_projection, midpoint_from_sign),
        )

        w00 = current_isometry.conj().T @ detector @ current_isometry
        w01 = current_isometry.conj().T @ detector @ complement
        w10 = complement.conj().T @ detector @ current_isometry
        w11 = complement.conj().T @ detector @ complement
        detector_diagonal = (
            -half_sine @ w00 @ half_cosine
            + half_complement_cosine @ w11 @ half_sine
        )
        detector_off_diagonal = (
            -half_sine @ w01 @ half_sine
            + half_complement_cosine @ w10 @ half_cosine
        )
        midpoint_complement_isometry = (
            -current_isometry @ half_sine.conj().T
            + complement @ half_complement_cosine
        )
        direct_detector_corner = (
            midpoint_complement_isometry.conj().T
            @ detector
            @ midpoint_isometry
        )
        checks["detector split error"] = max(
            checks["detector split error"],
            relative_error(
                direct_detector_corner,
                detector_diagonal + detector_off_diagonal,
            ),
        )

        midpoint_range_corner = (
            midpoint_complement_isometry.conj().T
            @ difference
            @ midpoint_isometry
        )
        checks["range singular-value error"] = max(
            checks["range singular-value error"],
            relative_error(
                np.linalg.svd(midpoint_range_corner, compute_uv=False),
                np.linalg.svd(sine, compute_uv=False),
            ),
        )

        off_diagonal_bound = math.sqrt(2.0) * np.linalg.norm(w10, "fro")
        diagonal_bound = (
            2.0 * np.linalg.norm(detector, 2) * np.linalg.norm(half_sine, "fro")
        )
        total_bound_sq = (
            4.0 * np.linalg.norm(w10, "fro") ** 2
            + 4.0 * np.linalg.norm(detector, 2) ** 2
            * np.linalg.norm(sine, "fro") ** 2
        )
        checks["off-diagonal bound violation"] = max(
            checks["off-diagonal bound violation"],
            float(np.linalg.norm(detector_off_diagonal, "fro") - off_diagonal_bound),
        )
        checks["diagonal bound violation"] = max(
            checks["diagonal bound violation"],
            float(np.linalg.norm(detector_diagonal, "fro") - diagonal_bound),
        )
        checks["total bound violation"] = max(
            checks["total bound violation"],
            float(np.linalg.norm(direct_detector_corner, "fro") ** 2 - total_bound_sq),
        )
        current_isometry = next_isometry

    return {label: max(0.0, value) for label, value in checks.items()}


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--ambient-size", type=int, default=48)
    parser.add_argument("--rank", type=int, default=20)
    parser.add_argument("--primes", default="2,3,5,7,11,13,17,19,23")
    parser.add_argument("--seed", type=int, default=355)
    parser.add_argument("--tolerance", type=float, default=8e-10)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    primes = [int(value) for value in args.primes.split(",")]
    checks = certificate(args.ambient_size, args.rank, primes, args.seed)
    print("Proof 355 half-angle detector-split certificate")
    for label, value in checks.items():
        print(f"{label.replace(' ', '_')}={value:.12e}")
    maximum_error = max(checks.values())
    if maximum_error > args.tolerance:
        raise RuntimeError(f"half-angle certificate failed: {maximum_error:.3e}")
    print(f"maximum_exact_error_or_violation={maximum_error:.12e}")
    print("half_angle_midpoint=EXACT")
    print("detector_split=EXACT")
    print("uniform_old_crossing_row=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
