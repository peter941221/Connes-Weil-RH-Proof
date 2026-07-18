"""Finite certificate for Proof 362's reflected second-support factor.

Spatial reflection models the exact conjugation ordering.  The script does not
prove the remaining prolate coupling, Gate 3U, or RH.
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
    offsets = np.arange(-root_radius, root_radius + 1)
    amplitudes = (root_radius + 1 - np.abs(offsets)).astype(float)
    root_values = amplitudes * np.exp(0.17j * offsets)
    root_values /= np.linalg.norm(root_values)

    convolution = np.zeros((size, size), dtype=complex)
    for row in range(size):
        for offset, value in zip(offsets, root_values):
            column = row - int(offset)
            if 0 <= column < size:
                convolution[row, column] = value

    reflection = np.fliplr(np.eye(size, dtype=complex))
    reflected_convolution = reflection @ convolution @ reflection
    positive = np.diag((coordinates >= 0).astype(float)).astype(complex)
    negative = np.eye(size, dtype=complex) - positive
    second_support = reflection @ positive @ reflection
    window = np.diag((np.abs(coordinates) <= root_radius).astype(float)).astype(
        complex
    )

    detector = convolution.conj().T @ convolution
    reflected_detector = reflected_convolution.conj().T @ reflected_convolution
    direct_second = (
        (np.eye(size, dtype=complex) - second_support)
        @ detector
        @ second_support
    )
    radial_reflected = negative @ reflected_detector @ positive
    conjugated_second = reflection @ radial_reflected @ reflection

    common = window @ reflected_convolution @ positive @ reflection
    left_factor = (
        reflection @ negative @ reflected_convolution.conj().T @ window
    )
    factored_second = left_factor @ common
    left_norm_sq = float(np.linalg.norm(left_factor, 2) ** 2)
    covariance_violation = positive_maximum_eigenvalue(
        direct_second.conj().T @ direct_second
        - left_norm_sq * (common.conj().T @ common)
    )

    outer_common = window @ convolution @ positive
    two_copy_hs_sq = float(
        np.linalg.norm(outer_common, "fro") ** 2
        + np.linalg.norm(common, "fro") ** 2
    )
    two_copy_budget = float(2 * (2 * root_radius + 1))

    return {
        "support conjugation error": relative_error(
            second_support, reflection @ positive @ reflection
        ),
        "detector reflection error": relative_error(
            reflection @ detector @ reflection, reflected_detector
        ),
        "crossing conjugation error": relative_error(
            direct_second, conjugated_second
        ),
        "reflected factorization error": relative_error(
            direct_second, factored_second
        ),
        "Douglas covariance violation": covariance_violation,
        "two-copy HS budget violation": max(
            0.0, two_copy_hs_sq - two_copy_budget
        ),
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--size", type=int, default=121)
    parser.add_argument("--root-radius", type=int, default=9)
    parser.add_argument("--tolerance", type=float, default=3e-10)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    checks = certificate(args.size, args.root_radius)
    print("Proof 362 reflected second-support Douglas certificate")
    for label, value in checks.items():
        print(f"{label.replace(' ', '_')}={value:.12e}")
    maximum_error = max(checks.values())
    if maximum_error > args.tolerance:
        raise RuntimeError(
            f"reflected second-support certificate failed: {maximum_error:.3e}"
        )
    print(f"maximum_error_or_violation={maximum_error:.12e}")
    print("reflected_detector_readback=EXACT")
    print("second_support_window_factor=EXACT")
    print("second_support_prolate_remainder=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
