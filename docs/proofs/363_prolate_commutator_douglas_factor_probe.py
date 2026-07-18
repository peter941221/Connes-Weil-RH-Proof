"""Finite certificate for Proof 363's prolate commutator factor.

The matrices verify the exact two-copy factorization, Schatten budgets, and a
signed finite bundle.  They do not prove uniform prefix control, Gate 3U, or
RH.
"""

from __future__ import annotations

import argparse
import math

import numpy as np


def positive_square_root(matrix: np.ndarray) -> np.ndarray:
    eigenvalues, eigenvectors = np.linalg.eigh(matrix)
    eigenvalues = np.maximum(eigenvalues, 0.0)
    return eigenvectors @ np.diag(np.sqrt(eigenvalues)) @ eigenvectors.conj().T


def relative_error(actual: np.ndarray | float, expected: np.ndarray | float) -> float:
    actual_array = np.asarray(actual)
    expected_array = np.asarray(expected)
    return float(
        np.linalg.norm(actual_array - expected_array)
        / max(1.0, float(np.linalg.norm(expected_array)))
    )


def positive_maximum_eigenvalue(matrix: np.ndarray) -> float:
    hermitian = 0.5 * (matrix + matrix.conj().T)
    return max(0.0, float(np.max(np.linalg.eigvalsh(hermitian))))


def certificate(size: int, auxiliary_size: int, seed: int) -> dict[str, float]:
    rng = np.random.default_rng(seed)
    frame = rng.normal(size=(size, size)) + 1j * rng.normal(size=(size, size))
    eigenvalues = np.exp(-0.3 * np.arange(size))
    unitary, _ = np.linalg.qr(frame)
    prolate = unitary @ np.diag(eigenvalues) @ unitary.conj().T
    square_root = positive_square_root(prolate)

    detector_frame = rng.normal(size=(size, size)) + 1j * rng.normal(
        size=(size, size)
    )
    detector = 0.5 * (detector_frame + detector_frame.conj().T)
    detector /= max(1.0, np.linalg.norm(detector, 2))

    common = np.vstack((square_root, square_root @ detector))
    left_factor = np.hstack((detector @ square_root, -square_root))
    commutator = detector @ prolate - prolate @ detector
    factored = left_factor @ common

    hs_budget = float(
        np.trace(prolate).real * (1.0 + np.linalg.norm(detector, 2) ** 2)
    )
    left_bound = float(
        math.sqrt(np.linalg.norm(prolate, 2))
        * math.sqrt(1.0 + np.linalg.norm(detector, 2) ** 2)
    )
    left_norm_sq = float(np.linalg.norm(left_factor, 2) ** 2)
    covariance_violation = positive_maximum_eigenvalue(
        commutator.conj().T @ commutator
        - left_norm_sq * (common.conj().T @ common)
    )

    boundary_common = rng.normal(size=(auxiliary_size, size)) + 1j * rng.normal(
        size=(auxiliary_size, size)
    )
    boundary_left = rng.normal(size=(size, auxiliary_size)) + 1j * rng.normal(
        size=(size, auxiliary_size)
    )
    signed_direct = boundary_left @ boundary_common - commutator
    bundled_common = np.vstack((boundary_common, common))
    bundled_left = np.hstack((boundary_left, -left_factor))

    return {
        "commutator factorization error": relative_error(commutator, factored),
        "HS budget violation": max(
            0.0, float(np.linalg.norm(common, "fro") ** 2 - hs_budget)
        ),
        "left norm violation": max(
            0.0, float(np.linalg.norm(left_factor, 2) - left_bound)
        ),
        "Douglas covariance violation": covariance_violation,
        "signed bundle error": relative_error(
            signed_direct, bundled_left @ bundled_common
        ),
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--size", type=int, default=28)
    parser.add_argument("--auxiliary-size", type=int, default=17)
    parser.add_argument("--seed", type=int, default=363)
    parser.add_argument("--tolerance", type=float, default=4e-10)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    checks = certificate(args.size, args.auxiliary_size, args.seed)
    print("Proof 363 prolate commutator Douglas certificate")
    for label, value in checks.items():
        print(f"{label.replace(' ', '_')}={value:.12e}")
    maximum_error = max(checks.values())
    if maximum_error > args.tolerance:
        raise RuntimeError(
            f"prolate commutator certificate failed: {maximum_error:.3e}"
        )
    print(f"maximum_error_or_violation={maximum_error:.12e}")
    print("prolate_two_copy_factor=EXACT")
    print("fixed_source_bundle=EXACT")
    print("uniform_prefix_dressing=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
