"""Discrete certificate for Proof 361's outer half-line Douglas factor.

The zero-fill convolution matrix checks exact intermediate-window localization
and positive covariance domination.  It does not prove the remaining quotient
branches, Gate 3U, or RH.
"""

from __future__ import annotations

import argparse

import numpy as np


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


def certificate(size: int, root_radius: int) -> dict[str, float]:
    if size % 2 == 0:
        raise ValueError("size must be odd")
    center = size // 2
    coordinates = np.arange(size) - center
    root_offsets = np.arange(-root_radius, root_radius + 1)
    root_values = (root_radius + 1 - np.abs(root_offsets)).astype(float)
    root_values /= np.linalg.norm(root_values)

    convolution = np.zeros((size, size), dtype=complex)
    for row in range(size):
        for offset, value in zip(root_offsets, root_values):
            column = row - int(offset)
            if 0 <= column < size:
                convolution[row, column] = value

    positive = np.diag((coordinates >= 0).astype(float)).astype(complex)
    negative = np.eye(size, dtype=complex) - positive
    window = np.diag((np.abs(coordinates) <= root_radius).astype(float)).astype(
        complex
    )
    detector = convolution.conj().T @ convolution
    direct = negative @ detector @ positive
    common = window @ convolution @ positive
    left_factor = negative @ convolution.conj().T @ window
    factored = left_factor @ common

    left_norm_sq = float(np.linalg.norm(left_factor, 2) ** 2)
    covariance_violation = positive_maximum_eigenvalue(
        direct.conj().T @ direct
        - left_norm_sq * (common.conj().T @ common)
    )
    root_norm_sq = float(np.linalg.norm(root_values) ** 2)
    hs_budget = float((2 * root_radius + 1) * root_norm_sq)

    return {
        "window localization error": relative_error(direct, factored),
        "Douglas covariance violation": covariance_violation,
        "left factor norm violation": max(
            0.0,
            float(np.linalg.norm(left_factor, 2) - np.linalg.norm(convolution, 2)),
        ),
        "HS budget violation": max(
            0.0, float(np.linalg.norm(common, "fro") ** 2 - hs_budget)
        ),
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--size", type=int, default=121)
    parser.add_argument("--root-radius", type=int, default=9)
    parser.add_argument("--tolerance", type=float, default=2e-10)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    checks = certificate(args.size, args.root_radius)
    print("Proof 361 outer half-line Douglas certificate")
    for label, value in checks.items():
        print(f"{label.replace(' ', '_')}={value:.12e}")
    maximum_error = max(checks.values())
    if maximum_error > args.tolerance:
        raise RuntimeError(f"outer half-line certificate failed: {maximum_error:.3e}")
    print(f"maximum_error_or_violation={maximum_error:.12e}")
    print("outer_window_factorization=EXACT")
    print("outer_douglas_domination=PASS")
    print("remaining_quotient_branches=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
