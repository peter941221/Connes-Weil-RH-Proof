"""Finite certificate for Proof 405's fixed-quotient first jet."""

from __future__ import annotations

import argparse

import numpy as np


def commutator(left: np.ndarray, right: np.ndarray) -> np.ndarray:
    return left @ right - right @ left


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


def projection(columns: np.ndarray) -> np.ndarray:
    return columns @ columns.conj().T


def geometry(
    size: int,
    intersection_rank: int,
    band_rank: int,
) -> tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray, np.ndarray]:
    if intersection_rank + 2 * band_rank > size:
        raise ValueError("ambient carrier is too small")
    identity = np.eye(size, dtype=complex)
    inner_columns = identity[:, :intersection_rank]
    band_columns = identity[
        :, intersection_rank : intersection_rank + band_rank
    ]
    outer = projection(np.hstack([inner_columns, band_columns]))
    inner = projection(inner_columns)
    band = projection(band_columns)

    second_columns = [inner_columns[:, index] for index in range(intersection_rank)]
    for offset, angle in enumerate(np.linspace(0.31, 0.88, band_rank)):
        inside = intersection_rank + offset
        outside = intersection_rank + band_rank + offset
        second_columns.append(
            np.cos(angle) * identity[:, inside]
            + np.sin(angle) * identity[:, outside]
        )
    second = projection(np.column_stack(second_columns))
    prolate = outer @ second @ outer - inner
    return outer, second, inner, band, prolate


def moved_quotient_projection(
    outer: np.ndarray,
    band_columns: np.ndarray,
    unitary: np.ndarray,
    coefficient: float,
) -> np.ndarray:
    identity = np.eye(unitary.shape[0], dtype=complex)
    inverse = np.linalg.inv(identity - coefficient * unitary)
    moved = outer @ inverse @ outer @ band_columns
    frame, _ = np.linalg.qr(moved)
    return projection(frame[:, : band_columns.shape[1]])


def certificate(size: int, intersection_rank: int, band_rank: int, seed: int) -> dict[str, float]:
    rng = np.random.default_rng(seed)
    identity = np.eye(size, dtype=complex)
    outer, second, inner, band, prolate = geometry(
        size, intersection_rank, band_rank
    )
    band_columns = identity[
        :, intersection_rank : intersection_rank + band_rank
    ]

    spectral_basis = random_unitary(size, rng)
    phases = np.exp(1j * np.linspace(-2.1, 2.4, size))
    unitary = spectral_basis @ np.diag(phases) @ spectral_basis.conj().T
    detector = (
        spectral_basis
        @ np.diag(0.35 + np.linspace(0.0, 1.0, size) ** 2)
        @ spectral_basis.conj().T
    )
    compressed_detector = outer @ detector @ outer
    generator = outer @ unitary @ outer
    predicted_derivative = (
        inner @ generator @ band
        + band @ generator.conj().T @ inner
    )

    step = 1e-5
    plus = moved_quotient_projection(
        outer, band_columns, unitary, step
    )
    minus = moved_quotient_projection(
        outer, band_columns, unitary, -step
    )
    finite_derivative = (plus - minus) / (2.0 * step)
    response_derivative = np.trace(compressed_detector @ predicted_derivative)

    scalar_corner = 2.0 * np.real(
        np.trace(band @ compressed_detector @ inner @ generator @ band)
    )
    commutator_corner = 2.0 * np.real(
        np.trace(
            band
            @ commutator(compressed_detector, inner)
            @ inner
            @ generator
            @ band
        )
    )
    semicommutator = (
        band @ compressed_detector @ generator @ band
        - (band @ compressed_detector @ band)
        @ (band @ generator @ band)
    )

    physical_ledger = (
        outer @ commutator(detector, outer) @ second @ outer
        + outer @ commutator(detector, second) @ outer
        + outer @ second @ commutator(detector, outer) @ outer
        - outer @ commutator(detector, prolate) @ outer
    )
    two_branch = (
        band @ second @ compressed_detector @ inner
        + band
        @ (identity - second)
        @ commutator(compressed_detector, second)
        @ inner
    )

    return {
        "ambient detector transport commutator error": relative_error(
            detector @ unitary, unitary @ detector
        ),
        "quotient Gram derivative error": relative_error(
            finite_derivative, predicted_derivative
        ),
        "scalar corner error": relative_error(
            response_derivative, scalar_corner
        ),
        "commutator corner error": relative_error(
            scalar_corner, commutator_corner
        ),
        "Toeplitz semicommutator error": relative_error(
            scalar_corner, 2.0 * np.real(np.trace(semicommutator))
        ),
        "physical ledger error": relative_error(
            commutator(compressed_detector, inner), physical_ledger
        ),
        "two branch collapse error": relative_error(
            band @ compressed_detector @ inner, two_branch
        ),
        "prolate Gram error": relative_error(
            (band @ second) @ (second @ band), prolate
        ),
        "quotient first jet magnitude": float(abs(response_derivative)),
        "quotient compression commutator norm": float(
            np.linalg.norm(commutator(compressed_detector, generator), 2)
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--size", type=int, default=18)
    parser.add_argument("--intersection-rank", type=int, default=3)
    parser.add_argument("--band-rank", type=int, default=5)
    parser.add_argument("--seed", type=int, default=405)
    parser.add_argument("--tolerance", type=float, default=3e-8)
    args = parser.parse_args()

    checks = certificate(
        args.size, args.intersection_rank, args.band_rank, args.seed
    )
    print("Proof 405 fixed-quotient first-jet certificate")
    for label, value in checks.items():
        print(f"{label.replace(' ', '_')}={value:.12e}")

    exact_labels = [
        "ambient detector transport commutator error",
        "quotient Gram derivative error",
        "scalar corner error",
        "commutator corner error",
        "Toeplitz semicommutator error",
        "physical ledger error",
        "two branch collapse error",
        "prolate Gram error",
    ]
    maximum_error = max(checks[label] for label in exact_labels)
    if maximum_error > args.tolerance:
        raise RuntimeError(f"fixed-quotient first jet failed: {maximum_error:.3e}")
    if checks["quotient first jet magnitude"] <= 1e-5:
        raise RuntimeError("quotient first jet is accidentally trivial")
    if checks["quotient compression commutator norm"] <= 1e-5:
        raise RuntimeError("quotient correction is accidentally trivial")

    print(f"maximum_exact_error={maximum_error:.12e}")
    print("fixed_quotient_first_jet=EXACT")
    print("physical_ledger_scalar_collapse=TWO_BRANCHES")
    print("uniform_near_two_branch_bound=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
