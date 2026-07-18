"""Finite certificate for Proof 366's corrected quotient transport.

The model verifies the mandatory compressed-commutator term and scale
invariance.  It does not prove the uniform Gate 3U estimate or RH.
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


def random_unitary(size: int, rng: np.random.Generator) -> np.ndarray:
    matrix = rng.normal(size=(size, size)) + 1j * rng.normal(size=(size, size))
    unitary, triangular = np.linalg.qr(matrix)
    diagonal = np.diag(triangular)
    phases = diagonal / np.where(
        np.abs(diagonal) == 0.0, 1.0, np.abs(diagonal)
    )
    return unitary @ np.diag(phases.conj())


def quotient_data(
    ambient_size: int,
    quotient_size: int,
    rng: np.random.Generator,
) -> tuple[np.ndarray, np.ndarray]:
    spectral_basis = random_unitary(ambient_size, rng)
    transport = (
        spectral_basis
        @ np.diag(np.linspace(0.3, 0.95, ambient_size))
        @ spectral_basis.conj().T
    )
    detector = (
        spectral_basis
        @ np.diag(np.sin(np.linspace(0.1, 2.2, ambient_size)))
        @ spectral_basis.conj().T
    )
    inclusion = random_unitary(ambient_size, rng)[:, :quotient_size]
    return (
        inclusion.conj().T @ transport @ inclusion,
        inclusion.conj().T @ detector @ inclusion,
    )


def crossing_data(
    quotient_transport: np.ndarray,
    quotient_detector: np.ndarray,
    source_frame: np.ndarray,
) -> tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray]:
    quotient_size = quotient_transport.shape[0]
    identity = np.eye(quotient_size, dtype=complex)
    source_projection = source_frame @ source_frame.conj().T
    gram = (
        source_frame.conj().T
        @ quotient_transport.conj().T
        @ quotient_transport
        @ source_frame
    )
    inverse_gram_root = inverse_positive_square_root(gram)
    normalized_frame = quotient_transport @ source_frame @ inverse_gram_root
    moving_projection = normalized_frame @ normalized_frame.conj().T
    old_crossing = (
        (identity - source_projection) @ quotient_detector @ source_frame
    )
    transported_old = (
        (identity - moving_projection)
        @ quotient_transport
        @ (identity - source_projection)
        @ old_crossing
        @ inverse_gram_root
    )
    quotient_commutator = (
        quotient_detector @ quotient_transport
        - quotient_transport @ quotient_detector
    )
    correction = (
        (identity - moving_projection)
        @ quotient_commutator
        @ source_frame
        @ inverse_gram_root
    )
    direct = (
        (identity - moving_projection)
        @ quotient_detector
        @ normalized_frame
    )
    return direct, transported_old, correction, normalized_frame


def certificate(
    ambient_size: int,
    quotient_size: int,
    source_size: int,
    seed: int,
) -> dict[str, float]:
    if not 1 < source_size < quotient_size < ambient_size:
        raise ValueError("require 1 < source < quotient < ambient")
    rng = np.random.default_rng(seed)
    quotient_transport, quotient_detector = quotient_data(
        ambient_size, quotient_size, rng
    )
    source_frame = random_unitary(quotient_size, rng)[:, :source_size]
    direct, transported_old, correction, normalized_frame = crossing_data(
        quotient_transport, quotient_detector, source_frame
    )

    scale = 0.173
    scaled = crossing_data(
        scale * quotient_transport, quotient_detector, source_frame
    )

    return {
        "normalized isometry error": relative_error(
            normalized_frame.conj().T @ normalized_frame,
            np.eye(source_size),
        ),
        "corrected transport error": relative_error(
            direct, transported_old + correction
        ),
        "old-only omission norm": float(np.linalg.norm(direct - transported_old)),
        "scaled direct error": relative_error(scaled[0], direct),
        "scaled transported error": relative_error(scaled[1], transported_old),
        "scaled correction error": relative_error(scaled[2], correction),
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--ambient-size", type=int, default=20)
    parser.add_argument("--quotient-size", type=int, default=13)
    parser.add_argument("--source-size", type=int, default=7)
    parser.add_argument("--seed", type=int, default=366)
    parser.add_argument("--tolerance", type=float, default=8e-11)
    parser.add_argument("--minimum-omission", type=float, default=1e-4)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    checks = certificate(
        args.ambient_size,
        args.quotient_size,
        args.source_size,
        args.seed,
    )
    print("Proof 366 boundary-corrected quotient certificate")
    for label, value in checks.items():
        print(f"{label.replace(' ', '_')}={value:.12e}")

    exact_errors = [
        checks["normalized isometry error"],
        checks["corrected transport error"],
        checks["scaled direct error"],
        checks["scaled transported error"],
        checks["scaled correction error"],
    ]
    maximum_error = max(exact_errors)
    if maximum_error > args.tolerance:
        raise RuntimeError(f"corrected transport failed: {maximum_error:.3e}")
    if checks["old-only omission norm"] < args.minimum_omission:
        raise RuntimeError("old-only omission was not detected")

    print(f"maximum_exact_error={maximum_error:.12e}")
    print("corrected_transport=EXACT")
    print("old_only_transport=FALSE")
    print("scale_invariance=PASS")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
