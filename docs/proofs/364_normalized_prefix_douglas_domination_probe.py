"""Finite certificate for Proof 364's normalized-prefix reduction.

The script verifies the expanded covariance identity and a commuting
two-dimensional condition-number guard.  It does not prove the route's
source-specific domination, Gate 3U, or RH.
"""

from __future__ import annotations

import argparse

import numpy as np


def inverse_positive_square_root(matrix: np.ndarray) -> np.ndarray:
    eigenvalues, eigenvectors = np.linalg.eigh(0.5 * (matrix + matrix.conj().T))
    if float(np.min(eigenvalues)) <= 0.0:
        raise ValueError("matrix must be positive definite")
    return (
        eigenvectors
        @ np.diag(eigenvalues**-0.5)
        @ eigenvectors.conj().T
    )


def relative_error(actual: np.ndarray | float, expected: np.ndarray | float) -> float:
    actual_array = np.asarray(actual)
    expected_array = np.asarray(expected)
    return float(
        np.linalg.norm(actual_array - expected_array)
        / max(1.0, float(np.linalg.norm(expected_array)))
    )


def random_unitary(size: int, rng: np.random.Generator) -> np.ndarray:
    matrix = rng.normal(size=(size, size)) + 1j * rng.normal(size=(size, size))
    unitary, triangular = np.linalg.qr(matrix)
    diagonal = np.diag(triangular)
    phases = diagonal / np.where(
        np.abs(diagonal) == 0.0, 1.0, np.abs(diagonal)
    )
    return unitary @ np.diag(phases.conj())


def normalized_prefix_certificate(
    ambient_size: int,
    source_size: int,
    seed: int,
) -> dict[str, float]:
    rng = np.random.default_rng(seed)
    spectral_basis = random_unitary(ambient_size, rng)
    prefix_eigenvalues = np.exp(np.linspace(-1.1, 0.9, ambient_size))
    detector_eigenvalues = rng.normal(size=ambient_size)
    prefix = (
        spectral_basis
        @ np.diag(prefix_eigenvalues)
        @ spectral_basis.conj().T
    )
    detector = (
        spectral_basis
        @ np.diag(detector_eigenvalues)
        @ spectral_basis.conj().T
    )

    source_frame = random_unitary(ambient_size, rng)[:, :source_size]
    identity = np.eye(ambient_size, dtype=complex)
    source_projection = source_frame @ source_frame.conj().T
    gram = source_frame.conj().T @ prefix.conj().T @ prefix @ source_frame
    inverse_gram_root = inverse_positive_square_root(gram)
    normalized_frame = prefix @ source_frame @ inverse_gram_root
    moving_projection = normalized_frame @ normalized_frame.conj().T

    fixed_bracket = (
        (identity - source_projection) @ detector @ source_projection
    )
    left_singular, singular_values, right_singular = np.linalg.svd(
        fixed_bracket, full_matrices=False
    )
    singular_root = np.diag(np.sqrt(singular_values))
    fixed_left = left_singular @ singular_root
    fixed_common = singular_root @ right_singular

    transported = (
        (identity - moving_projection)
        @ prefix
        @ (identity - source_projection)
        @ fixed_left
        @ fixed_common
        @ source_frame
        @ inverse_gram_root
    )
    direct = (identity - moving_projection) @ detector @ normalized_frame

    covariance = transported.conj().T @ transported
    expanded_covariance = (
        inverse_gram_root
        @ source_frame.conj().T
        @ fixed_common.conj().T
        @ fixed_left.conj().T
        @ (identity - source_projection)
        @ prefix.conj().T
        @ (identity - moving_projection)
        @ prefix
        @ (identity - source_projection)
        @ fixed_left
        @ fixed_common
        @ source_frame
        @ inverse_gram_root
    )

    return {
        "prefix detector commutator error": relative_error(
            prefix @ detector, detector @ prefix
        ),
        "normalized isometry error": relative_error(
            normalized_frame.conj().T @ normalized_frame,
            np.eye(source_size),
        ),
        "moving projection error": relative_error(
            moving_projection @ moving_projection, moving_projection
        ),
        "fixed bracket factorization error": relative_error(
            fixed_left @ fixed_common, fixed_bracket
        ),
        "transported crossing error": relative_error(transported, direct),
        "expanded covariance error": relative_error(
            expanded_covariance, covariance
        ),
    }


def condition_guard(kappa: float, theta: float) -> dict[str, float]:
    prefix = np.diag([1.0 / kappa, 1.0]).astype(complex)
    detector = np.diag([0.0, 1.0]).astype(complex)
    source = np.array([[np.cos(theta)], [np.sin(theta)]], dtype=complex)
    identity = np.eye(2, dtype=complex)
    source_projection = source @ source.conj().T
    gram = source.conj().T @ prefix.conj().T @ prefix @ source
    inverse_gram_root = np.array([[float(gram[0, 0].real) ** -0.5]])
    normalized_frame = prefix @ source @ inverse_gram_root
    moving_projection = normalized_frame @ normalized_frame.conj().T

    fixed_crossing = (identity - source_projection) @ detector @ source
    transported = (
        (identity - moving_projection)
        @ prefix
        @ (identity - source_projection)
        @ fixed_crossing
        @ inverse_gram_root
    )
    direct = (identity - moving_projection) @ detector @ normalized_frame

    fixed_norm = float(np.linalg.norm(fixed_crossing, 2))
    transported_norm = float(np.linalg.norm(transported, 2))
    amplification = transported_norm / fixed_norm
    tangent = float(np.tan(theta))
    exact_amplification = (
        kappa
        * (1.0 + tangent**2)
        / (1.0 + (kappa * tangent) ** 2)
    )

    return {
        "commutator error": relative_error(
            prefix @ detector, detector @ prefix
        ),
        "guard isometry error": relative_error(
            normalized_frame.conj().T @ normalized_frame, np.ones((1, 1))
        ),
        "guard transport error": relative_error(transported, direct),
        "amplification formula error": abs(amplification - exact_amplification),
        "amplification": amplification,
        "condition number": kappa,
        "condition fraction": amplification / kappa,
        "unit covariance violation": max(
            0.0, transported_norm**2 - fixed_norm**2
        ),
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--ambient-size", type=int, default=18)
    parser.add_argument("--source-size", type=int, default=7)
    parser.add_argument("--seed", type=int, default=364)
    parser.add_argument("--kappa", type=float, default=5.82842712474619)
    parser.add_argument("--theta", type=float, default=1e-4)
    parser.add_argument("--tolerance", type=float, default=5e-10)
    parser.add_argument("--minimum-condition-fraction", type=float, default=0.99999)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    prefix_checks = normalized_prefix_certificate(
        args.ambient_size,
        args.source_size,
        args.seed,
    )
    guard_checks = condition_guard(args.kappa, args.theta)

    print("Proof 364 normalized-prefix Douglas certificate")
    for label, value in prefix_checks.items():
        print(f"{label.replace(' ', '_')}={value:.12e}")
    for label, value in guard_checks.items():
        print(f"guard_{label.replace(' ', '_')}={value:.12e}")

    exact_errors = list(prefix_checks.values()) + [
        guard_checks["commutator error"],
        guard_checks["guard isometry error"],
        guard_checks["guard transport error"],
        guard_checks["amplification formula error"],
    ]
    maximum_error = max(exact_errors)
    if maximum_error > args.tolerance:
        raise RuntimeError(
            f"normalized-prefix certificate failed: {maximum_error:.3e}"
        )
    if guard_checks["condition fraction"] < args.minimum_condition_fraction:
        raise RuntimeError("guard did not approach the prefix condition number")
    if guard_checks["unit covariance violation"] <= 0.0:
        raise RuntimeError("guard did not violate unit Douglas domination")

    print(f"maximum_exact_error={maximum_error:.12e}")
    print("normalized_prefix_covariance=EXACT")
    print("isometry_only_uniform_bound=FALSE")
    print("causal_source_domination=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
