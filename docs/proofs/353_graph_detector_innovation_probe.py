"""Finite certificate for Proof 353's graph detector innovation identity.

The probe checks exact matrix identities for commuting Euler translations and
a self-adjoint detector.  It does not prove infinite-dimensional trace
legality, a weighted detector-row estimate, Gate 3U, or RH.
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
    q, _ = np.linalg.qr(matrix)
    return q[:, :rank]


def orthogonal_complement(isometry: np.ndarray) -> np.ndarray:
    _, _, vh = np.linalg.svd(isometry.conj().T, full_matrices=True)
    return vh.conj().T[:, isometry.shape[1] :]


def inverse_positive_square_root(matrix: np.ndarray) -> np.ndarray:
    eigenvalues, eigenvectors = np.linalg.eigh(matrix)
    if float(np.min(eigenvalues)) <= 0.0:
        raise RuntimeError("matrix is not positive definite")
    return eigenvectors @ np.diag(eigenvalues ** -0.5) @ eigenvectors.conj().T


def projection_from_frame(frame: np.ndarray) -> np.ndarray:
    gram = frame.conj().T @ frame
    return frame @ np.linalg.inv(gram) @ frame.conj().T


def relative_error(actual: np.ndarray | complex, expected: np.ndarray | complex) -> float:
    return float(
        np.linalg.norm(np.asarray(actual) - np.asarray(expected))
        / max(1.0, float(np.linalg.norm(np.asarray(expected))))
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

    source_isometry = random_isometry(ambient_size, rank, rng)
    current_isometry = source_isometry.copy()
    source_projection = source_isometry @ source_isometry.conj().T
    inverse_product = np.eye(ambient_size, dtype=complex)

    maximum_commutator_error = 0.0
    maximum_range_error = 0.0
    maximum_block_error = 0.0
    maximum_innovation_error = 0.0
    response_sum = 0.0

    for prime in primes:
        coefficient = prime ** -0.5
        displacement = math.log(prime)
        translation = np.diag(np.exp(1j * displacement * frequencies))
        maximum_commutator_error = max(
            maximum_commutator_error,
            relative_error(detector @ translation, translation @ detector),
        )

        complement = orthogonal_complement(current_isometry)
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
        next_projection = next_isometry @ next_isometry.conj().T

        euler_factor = np.eye(ambient_size, dtype=complex) - coefficient * translation
        transported_frame = np.linalg.solve(euler_factor, current_isometry)
        direct_projection = projection_from_frame(transported_frame)
        maximum_range_error = max(
            maximum_range_error,
            relative_error(next_projection, direct_projection),
        )

        block_difference = np.block(
            [
                [-sine.conj().T @ sine, cosine @ sine.conj().T],
                [sine @ cosine, sine @ sine.conj().T],
            ]
        )
        coordinates = np.concatenate((current_isometry, complement), axis=1)
        reconstructed_difference = coordinates @ block_difference @ coordinates.conj().T
        current_projection = current_isometry @ current_isometry.conj().T
        maximum_block_error = max(
            maximum_block_error,
            relative_error(next_projection - current_projection, reconstructed_difference),
        )

        w00 = current_isometry.conj().T @ detector @ current_isometry
        w10 = complement.conj().T @ detector @ current_isometry
        w11 = complement.conj().T @ detector @ complement
        innovation = 2.0 * w10 @ cosine + w11 @ sine - sine @ w00
        direct_response = np.trace(detector @ (next_projection - current_projection))
        innovation_response = float(np.trace(sine.conj().T @ innovation).real)
        maximum_innovation_error = max(
            maximum_innovation_error,
            relative_error(direct_response, innovation_response),
        )
        response_sum += innovation_response

        inverse_product = np.linalg.solve(euler_factor, inverse_product)
        current_isometry = next_isometry

    endpoint_projection = projection_from_frame(inverse_product @ source_isometry)
    sequential_projection = current_isometry @ current_isometry.conj().T
    endpoint_response = np.trace(detector @ (endpoint_projection - source_projection))

    return {
        "commutator error": maximum_commutator_error,
        "graph range error": maximum_range_error,
        "projection block error": maximum_block_error,
        "detector innovation error": maximum_innovation_error,
        "sequential projection error": relative_error(
            sequential_projection, endpoint_projection
        ),
        "endpoint telescope error": relative_error(response_sum, endpoint_response),
        "endpoint response imaginary part": abs(float(endpoint_response.imag)),
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--ambient-size", type=int, default=48)
    parser.add_argument("--rank", type=int, default=20)
    parser.add_argument("--primes", default="2,3,5,7,11,13,17,19,23")
    parser.add_argument("--seed", type=int, default=353)
    parser.add_argument("--tolerance", type=float, default=5e-10)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    primes = [int(value) for value in args.primes.split(",")]
    checks = certificate(args.ambient_size, args.rank, primes, args.seed)
    print("Proof 353 graph detector innovation certificate")
    for label, value in checks.items():
        print(f"{label.replace(' ', '_')}={value:.12e}")
    maximum_error = max(checks.values())
    if maximum_error > args.tolerance:
        raise RuntimeError(
            f"graph detector innovation certificate failed: {maximum_error:.3e}"
        )
    print(f"maximum_exact_error={maximum_error:.12e}")
    print("finite_graph_detector_identity=EXACT")
    print("infinite_trace_legality=OPEN")
    print("weighted_detector_row=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
