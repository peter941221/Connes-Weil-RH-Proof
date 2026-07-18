"""Finite certificate for Proof 367's compressed boundary ideal bound.

Frobenius and nuclear norms model the Schatten-2 and Schatten-1 estimates.
The script does not estimate the route's compressed Gram inverse or prove RH.
"""

from __future__ import annotations

import argparse

import numpy as np


def relative_error(actual: np.ndarray, expected: np.ndarray) -> float:
    return float(
        np.linalg.norm(actual - expected)
        / max(1.0, float(np.linalg.norm(expected)))
    )


def nuclear_norm(matrix: np.ndarray) -> float:
    return float(np.sum(np.linalg.svd(matrix, compute_uv=False)))


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
    transport = (
        spectral_basis
        @ np.diag(np.linspace(0.15, 0.98, ambient_size))
        @ spectral_basis.conj().T
    )
    detector = (
        spectral_basis
        @ np.diag(np.cos(np.linspace(0.0, 2.7, ambient_size)))
        @ spectral_basis.conj().T
    )
    inclusion = random_unitary(ambient_size, rng)[:, :quotient_size]
    projection = inclusion @ inclusion.conj().T
    quotient_transport = inclusion.conj().T @ transport @ inclusion
    quotient_detector = inclusion.conj().T @ detector @ inclusion

    boundary = detector @ projection - projection @ detector
    quotient_commutator = (
        quotient_detector @ quotient_transport
        - quotient_transport @ quotient_detector
    )
    readback = (
        inclusion.conj().T
        @ (boundary @ transport @ projection + projection @ transport @ boundary)
        @ inclusion
    )

    transport_norm = float(np.linalg.norm(transport, 2))
    frobenius_bound = 2.0 * transport_norm * float(np.linalg.norm(boundary, "fro"))
    nuclear_bound = 2.0 * transport_norm * nuclear_norm(boundary)

    return {
        "boundary identity error": relative_error(quotient_commutator, readback),
        "S2 bound violation": max(
            0.0, float(np.linalg.norm(quotient_commutator, "fro")) - frobenius_bound
        ),
        "S1 bound violation": max(
            0.0, nuclear_norm(quotient_commutator) - nuclear_bound
        ),
        "ambient contraction violation": max(0.0, transport_norm - 1.0),
        "quotient commutator norm": float(np.linalg.norm(quotient_commutator, 2)),
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--ambient-size", type=int, default=22)
    parser.add_argument("--quotient-size", type=int, default=14)
    parser.add_argument("--seed", type=int, default=367)
    parser.add_argument("--tolerance", type=float, default=8e-11)
    parser.add_argument("--minimum-commutator", type=float, default=1e-4)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    checks = certificate(args.ambient_size, args.quotient_size, args.seed)
    print("Proof 367 compressed-detector boundary ideal certificate")
    for label, value in checks.items():
        print(f"{label.replace(' ', '_')}={value:.12e}")

    exact_errors = [
        checks["boundary identity error"],
        checks["S2 bound violation"],
        checks["S1 bound violation"],
        checks["ambient contraction violation"],
    ]
    maximum_error = max(exact_errors)
    if maximum_error > args.tolerance:
        raise RuntimeError(f"boundary ideal certificate failed: {maximum_error:.3e}")
    if checks["quotient commutator norm"] < args.minimum_commutator:
        raise RuntimeError("quotient correction was not detected")

    print(f"maximum_error_or_violation={maximum_error:.12e}")
    print("two_boundary_owner=EXACT")
    print("uniform_pre_gram_S2_bound=PASS")
    print("uniform_pre_gram_S1_bound=PASS")
    print("post_gram_domination=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
