"""Finite certificate for Proof 403's nested-band first variation."""

from __future__ import annotations

import argparse

import numpy as np


def relative_error(actual: np.ndarray | complex, expected: np.ndarray | complex) -> float:
    return float(
        np.linalg.norm(np.asarray(actual) - np.asarray(expected))
        / max(1.0, float(np.linalg.norm(np.asarray(expected))))
    )


def random_unitary(size: int, rng: np.random.Generator) -> np.ndarray:
    raw = rng.normal(size=(size, size)) + 1j * rng.normal(size=(size, size))
    unitary, triangular = np.linalg.qr(raw)
    diagonal = np.diag(triangular)
    phases = diagonal / np.maximum(np.abs(diagonal), 1e-15)
    return unitary @ np.diag(np.conj(phases))


def moved_projection(
    projection: np.ndarray,
    unitary: np.ndarray,
    coefficient: float,
) -> np.ndarray:
    eigenvalues, eigenvectors = np.linalg.eigh(projection)
    basis = eigenvectors[:, eigenvalues > 0.5]
    moved = np.linalg.solve(
        np.eye(unitary.shape[0], dtype=complex) - coefficient * unitary,
        basis,
    )
    orthonormal, _ = np.linalg.qr(moved)
    return orthonormal @ orthonormal.conj().T


def variation(projection: np.ndarray, unitary: np.ndarray) -> np.ndarray:
    identity = np.eye(unitary.shape[0], dtype=complex)
    complement = identity - projection
    return (
        complement @ unitary @ projection
        + projection @ unitary.conj().T @ complement
    )


def certificate(size: int, inner_rank: int, band_rank: int, seed: int) -> dict[str, float]:
    if inner_rank + band_rank >= size:
        raise ValueError("nested ranks must leave a nonzero outer complement")
    rng = np.random.default_rng(seed)
    identity = np.eye(size, dtype=complex)
    inner = np.diag([1.0] * inner_rank + [0.0] * (size - inner_rank))
    outer = np.diag(
        [1.0] * (inner_rank + band_rank)
        + [0.0] * (size - inner_rank - band_rank)
    )
    band = outer - inner
    complement = identity - outer

    spectral_basis = random_unitary(size, rng)
    phases = np.exp(1j * np.linspace(-2.2, 2.5, size))
    unitary = spectral_basis @ np.diag(phases) @ spectral_basis.conj().T
    detector_values = 0.35 + np.linspace(0.0, 1.0, size) ** 2
    detector = (
        spectral_basis
        @ np.diag(detector_values)
        @ spectral_basis.conj().T
    )

    direct_variation = variation(outer, unitary) - variation(inner, unitary)
    boundary_variation = (
        complement @ unitary @ band
        + band @ unitary.conj().T @ complement
        - band @ unitary @ inner
        - inner @ unitary.conj().T @ band
    )
    analytic_response = np.trace(detector @ direct_variation)

    step = 1e-5
    response_plus = np.trace(
        detector
        @ (
            moved_projection(outer, unitary, step)
            - moved_projection(inner, unitary, step)
        )
    )
    response_minus = np.trace(
        detector
        @ (
            moved_projection(outer, unitary, -step)
            - moved_projection(inner, unitary, -step)
        )
    )
    finite_difference = (response_plus - response_minus) / (2.0 * step)

    return {
        "unitary violation": relative_error(unitary.conj().T @ unitary, identity),
        "detector commutator error": relative_error(
            detector @ unitary, unitary @ detector
        ),
        "detector positivity violation": max(
            0.0, -float(np.linalg.eigvalsh(detector).min())
        ),
        "nesting error": max(
            relative_error(outer @ inner, inner),
            relative_error(inner @ outer, inner),
        ),
        "two boundary identity error": relative_error(
            direct_variation, boundary_variation
        ),
        "finite difference error": relative_error(
            finite_difference, analytic_response
        ),
        "surviving derivative magnitude": float(abs(analytic_response)),
        "outer boundary norm": float(
            np.linalg.norm(
                complement @ unitary @ band
                + band @ unitary.conj().T @ complement,
                2,
            )
        ),
        "inner boundary norm": float(
            np.linalg.norm(
                band @ unitary @ inner
                + inner @ unitary.conj().T @ band,
                2,
            )
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--size", type=int, default=12)
    parser.add_argument("--inner-rank", type=int, default=3)
    parser.add_argument("--band-rank", type=int, default=4)
    parser.add_argument("--seed", type=int, default=403)
    parser.add_argument("--tolerance", type=float, default=2e-8)
    args = parser.parse_args()

    checks = certificate(args.size, args.inner_rank, args.band_rank, args.seed)
    print("Proof 403 nested-band first variation certificate")
    for label, value in checks.items():
        print(f"{label.replace(' ', '_')}={value:.12e}")

    exact_labels = [
        "unitary violation",
        "detector commutator error",
        "detector positivity violation",
        "nesting error",
        "two boundary identity error",
        "finite difference error",
    ]
    maximum_error = max(checks[label] for label in exact_labels)
    if maximum_error > args.tolerance:
        raise RuntimeError(f"nested first variation failed: {maximum_error:.3e}")
    if checks["surviving derivative magnitude"] <= 1e-4:
        raise RuntimeError("generic nested first variation is accidentally zero")
    if min(checks["outer boundary norm"], checks["inner boundary norm"]) <= 1e-4:
        raise RuntimeError("a physical boundary branch is accidentally trivial")

    print(f"maximum_exact_error={maximum_error:.12e}")
    print("nested_two_boundary_derivative=EXACT")
    print("abstract_first_variation_vanishing=REJECTED")
    print("cc20_first_variation_cancellation=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
