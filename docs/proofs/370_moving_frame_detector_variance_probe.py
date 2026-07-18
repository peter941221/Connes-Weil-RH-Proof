"""Finite certificate for Proof 370's moving-frame detector variance.

The script checks the UCP multiplicative defect and coordinate invariance.
It does not prove the uniform root-local trace estimate, Gate 3U, or RH.
"""

from __future__ import annotations

import argparse

import numpy as np


def inverse_positive_square_root(matrix: np.ndarray) -> np.ndarray:
    hermitian = 0.5 * (matrix + matrix.conj().T)
    eigenvalues, eigenvectors = np.linalg.eigh(hermitian)
    if float(np.min(eigenvalues)) <= 0.0:
        raise ValueError("matrix must be positive definite")
    return (
        eigenvectors
        @ np.diag(eigenvalues**-0.5)
        @ eigenvectors.conj().T
    )


def relative_error(actual: np.ndarray, expected: np.ndarray) -> float:
    return float(
        np.linalg.norm(actual - expected)
        / max(1.0, float(np.linalg.norm(expected)))
    )


def random_matrix(
    rows: int,
    columns: int,
    rng: np.random.Generator,
) -> np.ndarray:
    return rng.normal(size=(rows, columns)) + 1j * rng.normal(
        size=(rows, columns)
    )


def normalized_frame(frame: np.ndarray) -> np.ndarray:
    gram = frame.conj().T @ frame
    return frame @ inverse_positive_square_root(gram)


def certificate(ambient_size: int, source_size: int, seed: int) -> dict[str, float]:
    if not 1 < source_size < ambient_size:
        raise ValueError("require 1 < source size < ambient size")
    rng = np.random.default_rng(seed)
    raw_frame = random_matrix(ambient_size, source_size, rng)
    frame = normalized_frame(raw_frame)
    projection = frame @ frame.conj().T
    identity = np.eye(ambient_size, dtype=complex)

    detector_seed = random_matrix(ambient_size, ambient_size, rng)
    detector = 0.5 * (detector_seed + detector_seed.conj().T)
    detector /= max(1.0, float(np.linalg.norm(detector, 2)))

    defect = (identity - projection) @ detector @ frame
    defect_covariance = defect.conj().T @ defect
    compressed_detector = frame.conj().T @ detector @ frame
    variance = (
        frame.conj().T @ detector.conj().T @ detector @ frame
        - compressed_detector.conj().T @ compressed_detector
    )

    coordinate = random_matrix(source_size, source_size, rng)
    coordinate += 2.0 * np.eye(source_size)
    reframed = normalized_frame(raw_frame @ coordinate)
    reframed_projection = reframed @ reframed.conj().T
    reframed_defect = (identity - reframed_projection) @ detector @ reframed
    source_unitary = frame.conj().T @ reframed

    minimum_variance_eigenvalue = float(
        np.min(np.linalg.eigvalsh(0.5 * (variance + variance.conj().T)))
    )

    return {
        "isometry error": relative_error(
            frame.conj().T @ frame, np.eye(source_size)
        ),
        "projection error": relative_error(projection @ projection, projection),
        "variance identity error": relative_error(defect_covariance, variance),
        "positivity violation": max(0.0, -minimum_variance_eigenvalue),
        "coordinate projection error": relative_error(
            reframed_projection, projection
        ),
        "coordinate variance error": relative_error(
            reframed_defect.conj().T @ reframed_defect,
            source_unitary.conj().T @ defect_covariance @ source_unitary,
        ),
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--ambient-size", type=int, default=20)
    parser.add_argument("--source-size", type=int, default=9)
    parser.add_argument("--seed", type=int, default=370)
    parser.add_argument("--tolerance", type=float, default=2e-10)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    checks = certificate(args.ambient_size, args.source_size, args.seed)
    print("Proof 370 moving-frame detector variance certificate")
    for label, value in checks.items():
        print(f"{label.replace(' ', '_')}={value:.12e}")
    maximum_error = max(checks.values())
    if maximum_error > args.tolerance:
        raise RuntimeError(f"detector variance failed: {maximum_error:.3e}")

    print(f"maximum_error_or_violation={maximum_error:.12e}")
    print("ucp_variance=EXACT")
    print("variance_positive=PASS")
    print("explicit_gram_inverse=ELIMINATED")
    print("weighted_variance_bound=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
