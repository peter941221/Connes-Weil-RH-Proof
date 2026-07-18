"""Finite certificate for Proof 365's quotient commutation audit.

The script compresses commuting normal matrices to a nonreducing subspace and
checks the exact two-boundary commutator.  It does not prove Gate 3U or RH.
"""

from __future__ import annotations

import argparse

import numpy as np


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
    seed: int,
) -> dict[str, float]:
    if not 1 < quotient_size < ambient_size:
        raise ValueError("quotient size must be strictly between 1 and ambient")

    rng = np.random.default_rng(seed)
    spectral_basis = random_unitary(ambient_size, rng)
    transport_spectrum = np.linspace(0.25, 0.95, ambient_size)
    detector_spectrum = np.cos(np.linspace(0.2, 2.4, ambient_size))
    transport = (
        spectral_basis
        @ np.diag(transport_spectrum)
        @ spectral_basis.conj().T
    )
    detector = (
        spectral_basis
        @ np.diag(detector_spectrum)
        @ spectral_basis.conj().T
    )

    quotient_inclusion = random_unitary(ambient_size, rng)[:, :quotient_size]
    quotient_projection = quotient_inclusion @ quotient_inclusion.conj().T
    quotient_transport = (
        quotient_inclusion.conj().T @ transport @ quotient_inclusion
    )
    quotient_detector = (
        quotient_inclusion.conj().T @ detector @ quotient_inclusion
    )

    ambient_boundary_commutator = (
        detector @ quotient_projection
        - quotient_projection @ detector
    )
    quotient_commutator = (
        quotient_detector @ quotient_transport
        - quotient_transport @ quotient_detector
    )
    boundary_readback = (
        quotient_inclusion.conj().T
        @ (
            ambient_boundary_commutator @ transport @ quotient_projection
            + quotient_projection @ transport @ ambient_boundary_commutator
        )
        @ quotient_inclusion
    )

    return {
        "ambient commutator error": relative_error(
            detector @ transport, transport @ detector
        ),
        "boundary readback error": relative_error(
            quotient_commutator, boundary_readback
        ),
        "quotient commutator norm": float(
            np.linalg.norm(quotient_commutator, 2)
        ),
        "quotient contraction violation": max(
            0.0, float(np.linalg.norm(quotient_transport, 2) - 1.0)
        ),
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--ambient-size", type=int, default=18)
    parser.add_argument("--quotient-size", type=int, default=11)
    parser.add_argument("--seed", type=int, default=365)
    parser.add_argument("--tolerance", type=float, default=5e-11)
    parser.add_argument("--minimum-commutator", type=float, default=1e-4)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    checks = certificate(args.ambient_size, args.quotient_size, args.seed)
    print("Proof 365 quotient-compression commutation certificate")
    for label, value in checks.items():
        print(f"{label.replace(' ', '_')}={value:.12e}")

    exact_errors = [
        checks["ambient commutator error"],
        checks["boundary readback error"],
        checks["quotient contraction violation"],
    ]
    maximum_error = max(exact_errors)
    if maximum_error > args.tolerance:
        raise RuntimeError(f"quotient audit failed: {maximum_error:.3e}")
    if checks["quotient commutator norm"] < args.minimum_commutator:
        raise RuntimeError("compressed commutator was not detected")

    print(f"maximum_exact_error={maximum_error:.12e}")
    print("ambient_commutation=PASS")
    print("quotient_commutation=FALSE")
    print("two_boundary_correction=EXACT")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
