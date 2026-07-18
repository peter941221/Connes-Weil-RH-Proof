"""Finite Douglas certificate for Proof 382's Julia range-root column."""

from __future__ import annotations

import argparse
import math

import numpy as np


def positive_square_root(matrix: np.ndarray) -> np.ndarray:
    eigenvalues, eigenvectors = np.linalg.eigh(matrix)
    eigenvalues = np.maximum(eigenvalues, 0.0)
    return eigenvectors @ np.diag(np.sqrt(eigenvalues)) @ eigenvectors.conj().T


def inverse_positive_square_root(matrix: np.ndarray) -> np.ndarray:
    eigenvalues, eigenvectors = np.linalg.eigh(matrix)
    if float(np.min(eigenvalues)) <= 1e-12:
        raise ValueError("positive inverse square root lost strict positivity")
    return eigenvectors @ np.diag(eigenvalues ** -0.5) @ eigenvectors.conj().T


def random_contraction(size: int, rng: np.random.Generator) -> np.ndarray:
    matrix = rng.normal(size=(size, size)) + 1j * rng.normal(size=(size, size))
    norm = float(np.linalg.norm(matrix, 2))
    return 0.72 * matrix / norm


def random_unitary(size: int, rng: np.random.Generator) -> np.ndarray:
    matrix = rng.normal(size=(size, size)) + 1j * rng.normal(size=(size, size))
    orthonormal, triangular = np.linalg.qr(matrix)
    phases = np.diag(triangular)
    phases = phases / np.maximum(np.abs(phases), 1e-15)
    return orthonormal @ np.diag(np.conj(phases))


def relative_error(actual: complex | np.ndarray, expected: complex | np.ndarray) -> float:
    return float(
        np.linalg.norm(np.asarray(actual) - np.asarray(expected))
        / max(1.0, float(np.linalg.norm(np.asarray(expected))))
    )


def certificate(
    source_size: int,
    auxiliary_size: int,
    primes: list[int],
    seed: int,
) -> dict[str, float]:
    if auxiliary_size <= source_size:
        raise ValueError("auxiliary size must expose a nontrivial common kernel")

    rng = np.random.default_rng(seed)
    identity = np.eye(source_size, dtype=complex)
    prefix = identity
    range_blocks = []
    maximum_defect_error = 0.0

    for prime in primes:
        transfer = random_contraction(source_size, rng)
        defect_square = identity - transfer.conj().T @ transfer
        defect = positive_square_root(defect_square)
        coefficient = 1.0 / math.sqrt(prime - 1.0)
        regularizer = inverse_positive_square_root(
            identity + coefficient * coefficient * defect_square
        )
        polar = random_unitary(source_size, rng)
        range_sine = coefficient * polar @ defect @ regularizer
        block = math.sqrt(prime - 1.0) * range_sine @ prefix
        range_blocks.append(block)

        predicted = (
            coefficient
            * coefficient
            * defect_square
            @ np.linalg.inv(identity + coefficient * coefficient * defect_square)
        )
        maximum_defect_error = max(
            maximum_defect_error,
            relative_error(range_sine.conj().T @ range_sine, predicted),
        )
        prefix = transfer @ prefix

    range_column = np.vstack(range_blocks)
    range_contraction_violation = max(
        0.0,
        float(
            np.max(
                np.linalg.eigvalsh(
                    range_column.conj().T @ range_column - identity
                )
            )
        ),
    )

    common_input = (
        rng.normal(size=(source_size, auxiliary_size))
        + 1j * rng.normal(size=(source_size, auxiliary_size))
    ) / np.sqrt(2.0 * auxiliary_size)
    julia_common_column = range_column @ common_input

    readouts = []
    physical_blocks = []
    detector_blocks = []
    offset = 0
    for prime in primes:
        readout = random_contraction(source_size, rng)
        block = julia_common_column[offset : offset + source_size]
        readouts.append(readout)
        physical_blocks.append(readout @ block)
        detector_blocks.append(
            (
                rng.normal(size=block.shape)
                + 1j * rng.normal(size=block.shape)
            )
            / np.sqrt(2.0 * auxiliary_size)
        )
        offset += source_size

    physical_column = np.vstack(physical_blocks)
    block_readout = np.zeros(
        (len(primes) * source_size, len(primes) * source_size),
        dtype=complex,
    )
    for index, readout in enumerate(readouts):
        start = index * source_size
        block_readout[start : start + source_size, start : start + source_size] = (
            readout
        )

    factorization_error = relative_error(
        physical_column,
        block_readout @ julia_common_column,
    )
    douglas_violation = max(
        0.0,
        float(
            np.max(
                np.linalg.eigvalsh(
                    physical_column.conj().T @ physical_column
                    - julia_common_column.conj().T @ julia_common_column
                )
            )
        ),
    )
    range_energy_violation = max(
        0.0,
        float(np.linalg.norm(julia_common_column, "fro") ** 2)
        - float(np.linalg.norm(common_input, "fro") ** 2),
    )

    response = sum(
        np.vdot(detector / math.sqrt(prime - 1.0), physical)
        for prime, detector, physical in zip(
            primes,
            detector_blocks,
            physical_blocks,
            strict=True,
        )
    )
    detector_energy = 0.0
    range_energy = 0.0
    for prime, detector, physical in zip(
        primes,
        detector_blocks,
        physical_blocks,
        strict=True,
    ):
        detector_energy += float(np.linalg.norm(detector, "fro") ** 2) / (
            prime - 1.0
        )
        range_energy += float(np.linalg.norm(physical, "fro") ** 2)
    cauchy_violation = max(
        0.0,
        abs(response) - math.sqrt(detector_energy * range_energy),
    )

    _, singular_values, right_vectors = np.linalg.svd(
        julia_common_column,
        full_matrices=True,
    )
    kernel_vector = right_vectors[-1].conj()
    kernel_residual = float(np.linalg.norm(julia_common_column @ kernel_vector))
    leakage_size = 1e-6
    leakage_output = np.zeros(
        (physical_column.shape[0], 1), dtype=complex
    )
    leakage_output[0, 0] = leakage_size
    leakage = leakage_output @ kernel_vector.conj()[None, :]
    leaked_column = physical_column + leakage
    leakage_response = float(np.linalg.norm(leaked_column @ kernel_vector))

    pseudoinverse_factor = leaked_column @ np.linalg.pinv(julia_common_column)
    reconstruction_residual = float(
        np.linalg.norm(
            leaked_column - pseudoinverse_factor @ julia_common_column
        )
    )

    return {
        "maximum Julia defect error": maximum_defect_error,
        "Julia column contraction violation": range_contraction_violation,
        "common column factorization error": factorization_error,
        "Douglas domination violation": douglas_violation,
        "common input range energy violation": range_energy_violation,
        "weighted Cauchy Schwarz violation": cauchy_violation,
        "common column kernel residual": kernel_residual,
        "leakage Hilbert Schmidt norm": float(np.linalg.norm(leakage, "fro")),
        "leakage kernel response": leakage_response,
        "leakage reconstruction residual": reconstruction_residual,
        "smallest common column singular value": float(
            singular_values[-1] if len(singular_values) == auxiliary_size else 0.0
        ),
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source-size", type=int, default=8)
    parser.add_argument("--auxiliary-size", type=int, default=11)
    parser.add_argument("--primes", default="2,3,5,7,11,13")
    parser.add_argument("--seed", type=int, default=382)
    parser.add_argument("--tolerance", type=float, default=3e-10)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    primes = [int(value) for value in args.primes.split(",")]
    checks = certificate(
        args.source_size,
        args.auxiliary_size,
        primes,
        args.seed,
    )
    print("Proof 382 Julia range-root Douglas criterion certificate")
    for label, value in checks.items():
        print(f"{label.replace(' ', '_')}={value:.12e}")

    exact_labels = [
        "maximum Julia defect error",
        "Julia column contraction violation",
        "common column factorization error",
        "Douglas domination violation",
        "common input range energy violation",
        "weighted Cauchy Schwarz violation",
        "common column kernel residual",
    ]
    maximum_error = max(checks[label] for label in exact_labels)
    if maximum_error > args.tolerance:
        raise RuntimeError(f"Julia Douglas certificate failed: {maximum_error:.3e}")
    if checks["leakage reconstruction residual"] <= 0.25e-6:
        raise RuntimeError("kernel leakage was not detected")

    print(f"maximum_exact_error={maximum_error:.12e}")
    print("julia_common_column=CONTRACTIVE")
    print("aligned_range_root_column=DOUGLAS_FACTORED")
    print("small_unaligned_kernel_leak=REJECTED")
    print("ccm24_range_root_domination=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
