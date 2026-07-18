"""Finite certificate for Proof 368's corrected physical ledger.

The script verifies the nested-projection, commutator, and moving-crossing
identities.  It does not prove the continuous Gate 3U estimate or RH.
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
    sonin_size: int,
    seed: int,
) -> dict[str, float]:
    if not 0 < sonin_size < quotient_size < ambient_size:
        raise ValueError("require 0 < sonin < quotient < ambient")
    rng = np.random.default_rng(seed)
    ambient_basis = random_unitary(ambient_size, rng)
    transport = (
        ambient_basis
        @ np.diag(np.linspace(0.2, 0.97, ambient_size))
        @ ambient_basis.conj().T
    )
    detector = (
        ambient_basis
        @ np.diag(np.sin(np.linspace(0.0, 2.5, ambient_size)))
        @ ambient_basis.conj().T
    )

    quotient_inclusion = random_unitary(ambient_size, rng)[:, :quotient_size]
    quotient_projection = quotient_inclusion @ quotient_inclusion.conj().T
    quotient_transport = quotient_inclusion.conj().T @ transport @ quotient_inclusion
    quotient_detector = quotient_inclusion.conj().T @ detector @ quotient_inclusion

    quotient_basis = random_unitary(quotient_size, rng)
    sonin_inclusion = quotient_basis[:, :sonin_size]
    source_inclusion = quotient_basis[:, sonin_size:]
    sonin_projection = sonin_inclusion @ sonin_inclusion.conj().T
    source_projection = source_inclusion @ source_inclusion.conj().T
    quotient_identity = np.eye(quotient_size, dtype=complex)

    second_basis = random_unitary(ambient_size, rng)
    second_projection = (
        second_basis[:, :quotient_size]
        @ second_basis[:, :quotient_size].conj().T
    )
    sonin_ambient = (
        quotient_inclusion @ sonin_projection @ quotient_inclusion.conj().T
    )
    prolate = (
        quotient_projection @ second_projection @ quotient_projection
        - sonin_ambient
    )

    boundary = detector @ quotient_projection - quotient_projection @ detector
    second_commutator = detector @ second_projection - second_projection @ detector
    prolate_commutator = detector @ prolate - prolate @ detector
    physical_ambient = (
        quotient_projection @ boundary @ second_projection @ quotient_projection
        + quotient_projection @ second_commutator @ quotient_projection
        + quotient_projection @ second_projection @ boundary @ quotient_projection
        - quotient_projection @ prolate_commutator @ quotient_projection
    )
    physical_readback = (
        quotient_inclusion.conj().T
        @ physical_ambient
        @ quotient_inclusion
    )
    sonin_commutator = (
        quotient_detector @ sonin_projection
        - sonin_projection @ quotient_detector
    )

    old_crossing = sonin_projection @ quotient_detector @ source_inclusion
    old_from_commutator = -sonin_commutator @ source_inclusion

    quotient_commutator = (
        quotient_detector @ quotient_transport
        - quotient_transport @ quotient_detector
    )
    corrected_ledger = -quotient_transport @ sonin_commutator + quotient_commutator

    gram = (
        source_inclusion.conj().T
        @ quotient_transport.conj().T
        @ quotient_transport
        @ source_inclusion
    )
    inverse_gram_root = inverse_positive_square_root(gram)
    normalized_frame = quotient_transport @ source_inclusion @ inverse_gram_root
    moving_projection = normalized_frame @ normalized_frame.conj().T
    direct = (
        (quotient_identity - moving_projection)
        @ quotient_detector
        @ normalized_frame
    )
    ledger_crossing = (
        (quotient_identity - moving_projection)
        @ corrected_ledger
        @ source_inclusion
        @ inverse_gram_root
    )

    return {
        "nested decomposition error": relative_error(
            sonin_projection + source_projection, quotient_identity
        ),
        "old crossing error": relative_error(old_crossing, old_from_commutator),
        "physical ledger error": relative_error(
            sonin_commutator, physical_readback
        ),
        "quotient correction norm": float(np.linalg.norm(quotient_commutator, 2)),
        "moving ledger error": relative_error(direct, ledger_crossing),
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--ambient-size", type=int, default=24)
    parser.add_argument("--quotient-size", type=int, default=15)
    parser.add_argument("--sonin-size", type=int, default=6)
    parser.add_argument("--seed", type=int, default=368)
    parser.add_argument("--tolerance", type=float, default=1e-10)
    parser.add_argument("--minimum-correction", type=float, default=1e-4)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    checks = certificate(
        args.ambient_size,
        args.quotient_size,
        args.sonin_size,
        args.seed,
    )
    print("Proof 368 boundary-corrected physical ledger certificate")
    for label, value in checks.items():
        print(f"{label.replace(' ', '_')}={value:.12e}")

    exact_errors = [
        checks["nested decomposition error"],
        checks["old crossing error"],
        checks["physical ledger error"],
        checks["moving ledger error"],
    ]
    maximum_error = max(exact_errors)
    if maximum_error > args.tolerance:
        raise RuntimeError(f"physical ledger failed: {maximum_error:.3e}")
    if checks["quotient correction norm"] < args.minimum_correction:
        raise RuntimeError("quotient correction was not detected")

    print(f"maximum_exact_error={maximum_error:.12e}")
    print("fixed_sonin_ledger=EXACT")
    print("quotient_boundary_correction=NONZERO")
    print("corrected_moving_crossing=EXACT")
    print("normalized_covariance=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
