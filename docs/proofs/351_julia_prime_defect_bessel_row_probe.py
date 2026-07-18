"""Certificate for Proof 351's Julia prime-defect Bessel row.

The matrices verify the defect telescope and its vector/HS amplifications.
They do not identify the route's completed detector with the dual row and do
not prove Gate 3U.
"""

from __future__ import annotations

import argparse
import math

import numpy as np


def random_unitary(size: int, rng: np.random.Generator) -> np.ndarray:
    matrix = rng.normal(size=(size, size)) + 1j * rng.normal(size=(size, size))
    q, r = np.linalg.qr(matrix)
    phases = np.diag(r)
    phases = phases / np.maximum(np.abs(phases), 1e-15)
    return q @ np.diag(np.conj(phases))


def positive_square_root(matrix: np.ndarray) -> np.ndarray:
    eigenvalues, eigenvectors = np.linalg.eigh(matrix)
    eigenvalues = np.maximum(eigenvalues, 0.0)
    return eigenvectors @ np.diag(np.sqrt(eigenvalues)) @ eigenvectors.conj().T


def inverse_positive_square_root(matrix: np.ndarray) -> np.ndarray:
    eigenvalues, eigenvectors = np.linalg.eigh(matrix)
    if float(np.min(eigenvalues)) <= 0.0:
        raise RuntimeError("matrix is not positive definite")
    return eigenvectors @ np.diag(eigenvalues ** -0.5) @ eigenvectors.conj().T


def relative_error(actual: np.ndarray | complex, expected: np.ndarray | complex) -> float:
    return float(
        np.linalg.norm(np.asarray(actual) - np.asarray(expected))
        / max(1.0, float(np.linalg.norm(np.asarray(expected))))
    )


def colligation_data(
    size: int, rank: int, prime: int, rng: np.random.Generator
) -> dict[str, np.ndarray | float]:
    unitary = random_unitary(size, rng)
    coefficient = prime ** -0.5
    complement_rank = size - rank
    u00 = unitary[:rank, :rank]
    u01 = unitary[:rank, rank:]
    u10 = unitary[rank:, :rank]
    u11 = unitary[rank:, rank:]
    resolvent = np.linalg.inv(
        np.eye(complement_rank, dtype=complex) - coefficient * u11
    )
    graph = coefficient * resolvent @ u10
    transfer = u00 + coefficient * u01 @ resolvent @ u10
    defect_square = np.eye(rank, dtype=complex) - transfer.conj().T @ transfer
    defect = positive_square_root(defect_square)
    sine = graph @ inverse_positive_square_root(
        np.eye(rank, dtype=complex) + graph.conj().T @ graph
    )
    julia_coefficient = coefficient / math.sqrt(1.0 - coefficient * coefficient)
    predicted_sine_square = (
        julia_coefficient
        * julia_coefficient
        * defect_square
        @ np.linalg.inv(
            np.eye(rank, dtype=complex)
            + julia_coefficient * julia_coefficient * defect_square
        )
    )
    return {
        "transfer": transfer,
        "defect": defect,
        "defect_square": defect_square,
        "sine": sine,
        "coefficient": julia_coefficient,
        "sine_square_error": relative_error(
            sine.conj().T @ sine, predicted_sine_square
        ),
    }


def certificate(
    size: int,
    rank: int,
    auxiliary_rank: int,
    primes: list[int],
    seed: int,
) -> dict[str, float]:
    rng = np.random.default_rng(seed)
    data = [colligation_data(size, rank, prime, rng) for prime in primes]

    source_vector = rng.normal(size=rank) + 1j * rng.normal(size=rank)
    source_matrix = rng.normal(size=(rank, auxiliary_rank)) + 1j * rng.normal(
        size=(rank, auxiliary_rank)
    )
    prefix = np.eye(rank, dtype=complex)
    defect_vector_energy = 0.0
    sine_vector_energy = 0.0
    defect_hs_energy = 0.0
    sine_hs_energy = 0.0
    response = 0.0 + 0.0j
    detector_energy = 0.0
    sine_square_error = 0.0

    for prime, step in zip(primes, data):
        transfer = np.asarray(step["transfer"])
        defect = np.asarray(step["defect"])
        sine = np.asarray(step["sine"])
        coefficient = float(step["coefficient"])
        sine_square_error = max(
            sine_square_error, float(step["sine_square_error"])
        )

        defect_vector = defect @ prefix @ source_vector
        sine_vector = sine @ prefix @ source_vector
        defect_matrix = defect @ prefix @ source_matrix
        sine_matrix = sine @ prefix @ source_matrix

        defect_vector_energy += float(np.vdot(defect_vector, defect_vector).real)
        sine_vector_energy += float(
            np.vdot(sine_vector, sine_vector).real
            / (coefficient * coefficient)
        )
        defect_hs_energy += float(np.linalg.norm(defect_matrix, "fro") ** 2)
        sine_hs_energy += float(
            np.linalg.norm(sine_matrix, "fro") ** 2
            / (coefficient * coefficient)
        )

        detector = rng.normal(size=sine_matrix.shape) + 1j * rng.normal(
            size=sine_matrix.shape
        )
        response += np.vdot(detector, sine_matrix)
        detector_energy += float(
            coefficient * coefficient * np.linalg.norm(detector, "fro") ** 2
        )
        prefix = transfer @ prefix

    survivor_vector = prefix @ source_vector
    survivor_matrix = prefix @ source_matrix
    vector_source_energy = float(np.vdot(source_vector, source_vector).real)
    matrix_source_energy = float(np.linalg.norm(source_matrix, "fro") ** 2)
    vector_telescope = defect_vector_energy + float(
        np.vdot(survivor_vector, survivor_vector).real
    )
    matrix_telescope = defect_hs_energy + float(
        np.linalg.norm(survivor_matrix, "fro") ** 2
    )
    cauchy_bound = math.sqrt(detector_energy * sine_hs_energy)

    return {
        "maximum sine square identity error": sine_square_error,
        "vector defect telescope error": relative_error(
            vector_telescope, vector_source_energy
        ),
        "HS defect telescope error": relative_error(
            matrix_telescope, matrix_source_energy
        ),
        "vector Bessel violation": max(
            0.0, sine_vector_energy - vector_source_energy
        ),
        "HS Bessel violation": max(0.0, sine_hs_energy - matrix_source_energy),
        "direct-sum Cauchy violation": max(0.0, abs(response) - cauchy_bound),
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--size", type=int, default=28)
    parser.add_argument("--rank", type=int, default=12)
    parser.add_argument("--auxiliary-rank", type=int, default=7)
    parser.add_argument("--primes", default="2,3,5,7,11,13,17,19,23")
    parser.add_argument("--seed", type=int, default=351)
    parser.add_argument("--tolerance", type=float, default=3e-10)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    primes = [int(value) for value in args.primes.split(",")]
    checks = certificate(
        args.size,
        args.rank,
        args.auxiliary_rank,
        primes,
        args.seed,
    )
    print("Proof 351 Julia prime-defect Bessel-row certificate")
    for label, value in checks.items():
        print(f"{label.replace(' ', '_')}={value:.12e}")
    maximum_error = max(checks.values())
    if maximum_error > args.tolerance:
        raise RuntimeError(f"Julia Bessel-row certificate failed: {maximum_error:.3e}")
    print(f"maximum_exact_error={maximum_error:.12e}")
    print("julia_defect_row_isometry=EXACT")
    print("weighted_range_sine_bessel_bound=EXACT")
    print("complete_detector_dual_row=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
