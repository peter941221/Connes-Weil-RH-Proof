"""Finite certificate for Proof 369's corrected covariance bottom.

The matrices verify the shorted metric and every corrected covariance term.
They do not prove the real-line uniform domination, Gate 3U, or RH.
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


def certificate(
    ambient_size: int,
    quotient_size: int,
    source_size: int,
    seed: int,
) -> dict[str, float]:
    if not 1 < source_size < quotient_size < ambient_size:
        raise ValueError("require 1 < source < quotient < ambient")
    rng = np.random.default_rng(seed)
    ambient_basis = random_unitary(ambient_size, rng)
    ambient_transport = (
        ambient_basis
        @ np.diag(np.linspace(0.2, 0.96, ambient_size))
        @ ambient_basis.conj().T
    )
    ambient_detector = (
        ambient_basis
        @ np.diag(np.cos(np.linspace(0.1, 2.6, ambient_size)))
        @ ambient_basis.conj().T
    )
    quotient_inclusion = random_unitary(ambient_size, rng)[:, :quotient_size]
    transport = (
        quotient_inclusion.conj().T
        @ ambient_transport
        @ quotient_inclusion
    )
    detector = (
        quotient_inclusion.conj().T
        @ ambient_detector
        @ quotient_inclusion
    )

    quotient_basis = random_unitary(quotient_size, rng)
    source = quotient_basis[:, :source_size]
    remainder = quotient_basis[:, source_size:]
    source_projection = source @ source.conj().T
    remainder_projection = remainder @ remainder.conj().T
    identity = np.eye(quotient_size, dtype=complex)

    metric = transport.conj().T @ transport
    gram = source.conj().T @ metric @ source
    gram_inverse = np.linalg.inv(gram)
    inverse_gram_root = inverse_positive_square_root(gram)
    normalized_frame = transport @ source @ inverse_gram_root
    moving_projection = normalized_frame @ normalized_frame.conj().T

    shorted = (
        remainder_projection
        @ (
            metric
            - metric @ source @ gram_inverse @ source.conj().T @ metric
        )
        @ remainder_projection
    )
    crossing_metric = (
        remainder_projection
        @ transport.conj().T
        @ (identity - moving_projection)
        @ transport
        @ remainder_projection
    )
    inverse_compression = np.linalg.inv(
        remainder.conj().T @ np.linalg.inv(metric) @ remainder
    )
    shorted_on_remainder = remainder.conj().T @ shorted @ remainder

    fixed_commutator = (
        detector @ remainder_projection
        - remainder_projection @ detector
    )
    quotient_commutator = detector @ transport - transport @ detector
    fixed_crossing = -fixed_commutator @ source
    correction = quotient_commutator @ source
    corrected_owner = -transport @ fixed_commutator + quotient_commutator
    direct = (
        (identity - moving_projection)
        @ detector
        @ normalized_frame
    )
    corrected = (
        (identity - moving_projection)
        @ corrected_owner
        @ source
        @ inverse_gram_root
    )

    covariance = corrected.conj().T @ corrected
    unsplit_covariance = (
        inverse_gram_root
        @ source.conj().T
        @ corrected_owner.conj().T
        @ (identity - moving_projection)
        @ corrected_owner
        @ source
        @ inverse_gram_root
    )
    old_covariance = (
        inverse_gram_root
        @ fixed_crossing.conj().T
        @ transport.conj().T
        @ (identity - moving_projection)
        @ transport
        @ fixed_crossing
        @ inverse_gram_root
    )
    correction_covariance = (
        inverse_gram_root
        @ correction.conj().T
        @ (identity - moving_projection)
        @ correction
        @ inverse_gram_root
    )
    mixed_covariance = (
        inverse_gram_root
        @ (
            fixed_crossing.conj().T
            @ transport.conj().T
            @ (identity - moving_projection)
            @ correction
            + correction.conj().T
            @ (identity - moving_projection)
            @ transport
            @ fixed_crossing
        )
        @ inverse_gram_root
    )

    return {
        "shorted metric error": relative_error(shorted, crossing_metric),
        "inverse compression error": relative_error(
            shorted_on_remainder, inverse_compression
        ),
        "corrected crossing error": relative_error(corrected, direct),
        "unsplit covariance error": relative_error(unsplit_covariance, covariance),
        "four-term covariance error": relative_error(
            old_covariance + correction_covariance + mixed_covariance,
            covariance,
        ),
        "mixed covariance norm": float(np.linalg.norm(mixed_covariance, 2)),
        "diagonal-only error": relative_error(
            old_covariance + correction_covariance, covariance
        ),
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--ambient-size", type=int, default=24)
    parser.add_argument("--quotient-size", type=int, default=15)
    parser.add_argument("--source-size", type=int, default=8)
    parser.add_argument("--seed", type=int, default=369)
    parser.add_argument("--tolerance", type=float, default=2e-10)
    parser.add_argument("--minimum-mixed", type=float, default=1e-5)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    checks = certificate(
        args.ambient_size,
        args.quotient_size,
        args.source_size,
        args.seed,
    )
    print("Proof 369 corrected normalized-covariance certificate")
    for label, value in checks.items():
        print(f"{label.replace(' ', '_')}={value:.12e}")

    exact_errors = [
        checks["shorted metric error"],
        checks["inverse compression error"],
        checks["corrected crossing error"],
        checks["unsplit covariance error"],
        checks["four-term covariance error"],
    ]
    maximum_error = max(exact_errors)
    if maximum_error > args.tolerance:
        raise RuntimeError(f"corrected covariance failed: {maximum_error:.3e}")
    if checks["mixed covariance norm"] < args.minimum_mixed:
        raise RuntimeError("mixed covariance was not detected")
    if checks["diagonal-only error"] < args.minimum_mixed:
        raise RuntimeError("diagonal-only omission was not detected")

    print(f"maximum_exact_error={maximum_error:.12e}")
    print("shorted_metric=EXACT")
    print("corrected_covariance=EXACT")
    print("mixed_terms=MANDATORY")
    print("uniform_douglas_domination=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
