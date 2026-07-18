"""Finite certificate for Proof 354's canonical-midpoint innovation.

The script verifies exact two-projection identities and their compatibility
with the sequential Julia graph path.  It does not prove the continuous
weighted midpoint-row estimate, Gate 3U, or RH.
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


def midpoint_data(
    old_projection: np.ndarray, new_projection: np.ndarray
) -> tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray]:
    size = old_projection.shape[0]
    identity = np.eye(size, dtype=complex)
    difference = new_projection - old_projection
    bisector = new_projection + old_projection - identity
    bisector_square = bisector @ bisector
    midpoint_symmetry = bisector @ inverse_positive_square_root(bisector_square)
    midpoint_projection = 0.5 * (identity + midpoint_symmetry)

    eigenvalues, eigenvectors = np.linalg.eigh(midpoint_symmetry)
    positive_basis = eigenvectors[:, eigenvalues > 0.0]
    negative_basis = eigenvectors[:, eigenvalues < 0.0]
    return difference, bisector, midpoint_projection, np.concatenate(
        (positive_basis, negative_basis), axis=1
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
    source_isometry = current_isometry.copy()
    source_projection = source_isometry @ source_isometry.conj().T
    inverse_product = np.eye(ambient_size, dtype=complex)

    maximum_anticommutator_error = 0.0
    maximum_pythagorean_error = 0.0
    maximum_midpoint_projection_error = 0.0
    maximum_midpoint_diagonal_error = 0.0
    maximum_midpoint_pairing_error = 0.0
    maximum_singular_value_error = 0.0
    maximum_schatten_bound_violation = 0.0
    maximum_range_error = 0.0
    response_sum = 0.0
    weighted_midpoint_detector_energy = 0.0

    identity = np.eye(ambient_size, dtype=complex)
    for prime in primes:
        coefficient = prime ** -0.5
        displacement = math.log(prime)
        translation = np.diag(np.exp(1j * displacement * frequencies))
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
        next_isometry = current_isometry @ cosine + complement @ sine
        new_projection = next_isometry @ next_isometry.conj().T

        euler_factor = identity - coefficient * translation
        transported_frame = np.linalg.solve(euler_factor, current_isometry)
        maximum_range_error = max(
            maximum_range_error,
            relative_error(new_projection, projection_from_frame(transported_frame)),
        )

        difference, bisector, midpoint_projection, midpoint_coordinates = (
            midpoint_data(current_projection, new_projection)
        )
        midpoint_symmetry = 2.0 * midpoint_projection - identity
        midpoint_complement = identity - midpoint_projection

        maximum_anticommutator_error = max(
            maximum_anticommutator_error,
            relative_error(
                difference @ bisector + bisector @ difference,
                np.zeros_like(difference),
            ),
        )
        maximum_pythagorean_error = max(
            maximum_pythagorean_error,
            relative_error(difference @ difference + bisector @ bisector, identity),
        )
        maximum_midpoint_projection_error = max(
            maximum_midpoint_projection_error,
            relative_error(midpoint_projection @ midpoint_projection, midpoint_projection),
            relative_error(midpoint_symmetry @ midpoint_symmetry, identity),
        )
        maximum_midpoint_diagonal_error = max(
            maximum_midpoint_diagonal_error,
            relative_error(
                midpoint_projection @ difference @ midpoint_projection,
                np.zeros_like(difference),
            ),
            relative_error(
                midpoint_complement @ difference @ midpoint_complement,
                np.zeros_like(difference),
            ),
        )

        positive_basis = midpoint_coordinates[:, :rank]
        negative_basis = midpoint_coordinates[:, rank:]
        range_corner = negative_basis.conj().T @ difference @ positive_basis
        detector_corner = negative_basis.conj().T @ detector @ positive_basis
        direct_response = np.trace(detector @ difference)
        midpoint_response = 2.0 * np.trace(
            detector_corner.conj().T @ range_corner
        ).real
        maximum_midpoint_pairing_error = max(
            maximum_midpoint_pairing_error,
            relative_error(direct_response, midpoint_response),
        )

        graph_singular_values = np.linalg.svd(sine, compute_uv=False)
        midpoint_singular_values = np.linalg.svd(range_corner, compute_uv=False)
        maximum_singular_value_error = max(
            maximum_singular_value_error,
            relative_error(midpoint_singular_values, graph_singular_values),
        )
        if prime >= 3:
            midpoint_commutator = (
                detector @ midpoint_projection - midpoint_projection @ detector
            )
            old_commutator = detector @ current_projection - current_projection @ detector
            new_commutator = detector @ new_projection - new_projection @ detector
            schatten_bound = 0.5 * (math.sqrt(2.0) + 2.0) * (
                np.linalg.norm(old_commutator, "fro")
                + np.linalg.norm(new_commutator, "fro")
            )
            maximum_schatten_bound_violation = max(
                maximum_schatten_bound_violation,
                float(np.linalg.norm(midpoint_commutator, "fro") - schatten_bound),
            )
        weighted_midpoint_detector_energy += float(
            np.linalg.norm(detector_corner, "fro") ** 2 / (prime - 1.0)
        )
        response_sum += float(midpoint_response)

        inverse_product = np.linalg.solve(euler_factor, inverse_product)
        current_isometry = next_isometry

    endpoint_projection = projection_from_frame(inverse_product @ source_isometry)
    endpoint_response = np.trace(detector @ (endpoint_projection - source_projection))

    return {
        "graph range error": maximum_range_error,
        "anticommutator error": maximum_anticommutator_error,
        "Pythagorean error": maximum_pythagorean_error,
        "midpoint projection error": maximum_midpoint_projection_error,
        "midpoint diagonal error": maximum_midpoint_diagonal_error,
        "midpoint detector pairing error": maximum_midpoint_pairing_error,
        "range singular-value error": maximum_singular_value_error,
        "Schatten bound violation": max(0.0, maximum_schatten_bound_violation),
        "endpoint telescope error": relative_error(response_sum, endpoint_response),
        "endpoint response imaginary part": abs(float(endpoint_response.imag)),
        "weighted midpoint detector energy": weighted_midpoint_detector_energy,
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--ambient-size", type=int, default=48)
    parser.add_argument("--rank", type=int, default=20)
    parser.add_argument("--primes", default="2,3,5,7,11,13,17,19,23")
    parser.add_argument("--seed", type=int, default=354)
    parser.add_argument("--tolerance", type=float, default=8e-10)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    primes = [int(value) for value in args.primes.split(",")]
    checks = certificate(args.ambient_size, args.rank, primes, args.seed)
    print("Proof 354 canonical-midpoint innovation certificate")
    for label, value in checks.items():
        print(f"{label.replace(' ', '_')}={value:.12e}")
    exact_checks = {
        label: value
        for label, value in checks.items()
        if label != "weighted midpoint detector energy"
    }
    maximum_error = max(exact_checks.values())
    if maximum_error > args.tolerance:
        raise RuntimeError(
            f"canonical-midpoint certificate failed: {maximum_error:.3e}"
        )
    print(f"maximum_exact_error={maximum_error:.12e}")
    print("midpoint_off_diagonalization=EXACT")
    print("midpoint_detector_pairing=EXACT")
    print("uniform_weighted_midpoint_row=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
