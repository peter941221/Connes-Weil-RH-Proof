"""Finite certificate for Proof 372's two-support prolate renewal.

The matrices have a prescribed intersection and nonzero principal angles.
The script does not prove the uniform moving boundary-Gram estimate or RH.
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


def certificate(
    intersection_size: int,
    quotient_size: int,
    outside_size: int,
    seed: int,
) -> dict[str, float]:
    if not 0 < quotient_size <= outside_size:
        raise ValueError("require 0 < quotient size <= outside size")
    if intersection_size < 1:
        raise ValueError("intersection size must be positive")
    rng = np.random.default_rng(seed)
    ambient_size = intersection_size + quotient_size + outside_size
    identity = np.eye(ambient_size, dtype=complex)

    intersection = np.zeros((ambient_size, intersection_size), dtype=complex)
    intersection[:intersection_size, :] = np.eye(intersection_size)
    quotient = np.zeros((ambient_size, quotient_size), dtype=complex)
    quotient[
        intersection_size : intersection_size + quotient_size, :
    ] = np.eye(quotient_size)
    outside = np.zeros((ambient_size, outside_size), dtype=complex)
    outside[intersection_size + quotient_size :, :] = np.eye(outside_size)

    angles = np.linspace(0.25, 1.05, quotient_size)
    tilted = quotient * np.cos(angles) + outside[:, :quotient_size] * np.sin(
        angles
    )
    second_basis = np.hstack((intersection, tilted))

    intersection_projection = intersection @ intersection.conj().T
    quotient_projection = quotient @ quotient.conj().T
    support_projection = intersection_projection + quotient_projection
    second_projection = second_basis @ second_basis.conj().T
    prolate = quotient_projection @ second_projection @ quotient_projection

    root = rng.normal(size=(ambient_size, ambient_size)) + 1j * rng.normal(
        size=(ambient_size, ambient_size)
    )
    root /= max(1.0, float(np.linalg.norm(root, 2)))
    root_crossing = intersection_projection @ root @ quotient_projection
    commutator = root @ second_projection - second_projection @ root
    boundary_numerator = (
        intersection_projection
        @ root
        @ (identity - support_projection)
        @ second_projection
        @ quotient_projection
        - intersection_projection @ commutator @ quotient_projection
    )

    boundary_frame = (identity - second_projection) @ quotient
    boundary_gram = boundary_frame.conj().T @ boundary_frame
    prolate_on_quotient = quotient.conj().T @ prolate @ quotient
    normalized_boundary = (
        boundary_frame @ inverse_positive_square_root(boundary_gram)
    )

    return {
        "compression identity error": relative_error(
            support_projection @ second_projection @ support_projection,
            intersection_projection + prolate,
        ),
        "renewal error": relative_error(
            root_crossing @ (identity - prolate), boundary_numerator
        ),
        "boundary Gram error": relative_error(
            boundary_gram,
            np.eye(quotient_size) - prolate_on_quotient,
        ),
        "polar isometry error": relative_error(
            normalized_boundary.conj().T @ normalized_boundary,
            np.eye(quotient_size),
        ),
        "strict angle margin": float(
            np.min(np.linalg.eigvalsh(boundary_gram))
        ),
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--intersection-size", type=int, default=5)
    parser.add_argument("--quotient-size", type=int, default=9)
    parser.add_argument("--outside-size", type=int, default=11)
    parser.add_argument("--seed", type=int, default=372)
    parser.add_argument("--tolerance", type=float, default=2e-10)
    parser.add_argument("--minimum-margin", type=float, default=1e-4)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    checks = certificate(
        args.intersection_size,
        args.quotient_size,
        args.outside_size,
        args.seed,
    )
    print("Proof 372 two-support prolate renewal certificate")
    for label, value in checks.items():
        print(f"{label.replace(' ', '_')}={value:.12e}")

    exact_errors = [
        checks["compression identity error"],
        checks["renewal error"],
        checks["boundary Gram error"],
        checks["polar isometry error"],
    ]
    maximum_error = max(exact_errors)
    if maximum_error > args.tolerance:
        raise RuntimeError(f"prolate renewal failed: {maximum_error:.3e}")
    if checks["strict angle margin"] < args.minimum_margin:
        raise RuntimeError("strict principal-angle margin was not detected")

    print(f"maximum_exact_error={maximum_error:.12e}")
    print("prolate_renewal=EXACT")
    print("explicit_prolate_commutator=ELIMINATED")
    print("boundary_polar_frame=ISOMETRIC")
    print("uniform_boundary_row=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
