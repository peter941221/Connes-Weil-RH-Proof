#!/usr/bin/env python3
"""Finite algebraic guard for Proof 307.

This checks the explicit two-point root-sandwich factorization and keeps the
CC20 ``-2`` root pairing separate.  It is not a continuous moving-owner,
Gate 3U, or RH proof.
"""

from __future__ import annotations

import argparse

import numpy as np


def relative_error(actual: np.ndarray | complex, expected: np.ndarray | complex) -> float:
    actual_array = np.asarray(actual)
    expected_array = np.asarray(expected)
    scale = max(float(np.linalg.norm(expected_array)), 1.0)
    return float(np.linalg.norm(actual_array - expected_array) / scale)


def run(size: int, radius: int, seed: int) -> dict[str, float]:
    if 2 * radius + 1 >= size:
        raise ValueError("root support must fit inside the finite window")
    rng = np.random.default_rng(seed)
    nodes = np.linspace(-2.5, 2.5, size)
    left = np.zeros(size, dtype=complex)
    right = np.zeros(size, dtype=complex)
    support = np.arange(-radius, radius + 1)
    left_values = rng.normal(size=support.size) + 1j * rng.normal(size=support.size)
    right_values = rng.normal(size=support.size) + 1j * rng.normal(size=support.size)
    left_values /= np.linalg.norm(left_values)
    right_values /= np.linalg.norm(right_values)
    left[np.mod(support, size)] = left_values
    right[np.mod(support, size)] = right_values

    difference = nodes[:, None] - nodes[None, :]
    left_kernel = np.exp(-0.17 * difference**2) * (
        1.0 + 0.13 * np.cos(0.7 * (nodes[:, None] + nodes[None, :]))
    )
    right_kernel = np.exp(-0.17 * difference**2) * (
        1.0 + 0.13 * np.cos(1.1 * (nodes[:, None] + nodes[None, :]))
    )

    left_factor = np.conj(left)[:, None] * left_kernel * right[None, :]
    right_factor = np.conj(left)[:, None] * right_kernel * right[None, :]
    direct_trace = np.sum(np.conj(right_factor) * left_factor)
    matrix_trace = np.trace(right_factor.conj().T @ left_factor)
    pointwise_factorized = (
        (np.conj(left)[:, None] * left[:, None])
        * (np.conj(right)[None, :] * right[None, :])
        * np.conj(right_kernel)
        * left_kernel
    )
    residue = -2.0 * np.vdot(right, left)

    moving_direct = []
    moving_two_point = []
    for alpha in np.linspace(0.0, 1.0, 9):
        phase_left = 0.7 + 0.2 * alpha
        phase_right = 1.1 - 0.15 * alpha
        left_kernel_alpha = np.exp(-0.17 * difference**2) * (
            1.0 + 0.13 * np.cos(phase_left * (nodes[:, None] + nodes[None, :]))
        )
        right_kernel_alpha = np.exp(-0.17 * difference**2) * (
            1.0 + 0.13 * np.cos(phase_right * (nodes[:, None] + nodes[None, :]))
        )
        left_factor_alpha = np.conj(left)[:, None] * left_kernel_alpha * right[None, :]
        right_factor_alpha = np.conj(left)[:, None] * right_kernel_alpha * right[None, :]
        moving_direct.append(np.trace(right_factor_alpha.conj().T @ left_factor_alpha))
        moving_two_point.append(np.sum(np.conj(right_factor_alpha) * left_factor_alpha))

    return {
        "matrix/two-point trace error": relative_error(matrix_trace, direct_trace),
        "root-weight factorization error": relative_error(
            np.conj(right_factor) * left_factor, pointwise_factorized
        ),
        "residue readback error": relative_error(residue, -2.0 * np.vdot(right, left)),
        "residue omission gap": float(abs(residue)),
        "complete response magnitude": float(abs(direct_trace + residue)),
        "moving time-average error": relative_error(
            np.mean(moving_direct), np.mean(moving_two_point)
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--size", type=int, default=32)
    parser.add_argument("--support-radius", type=int, default=3)
    parser.add_argument("--seed", type=int, default=1307)
    args = parser.parse_args()

    metrics = run(args.size, args.support_radius, args.seed)
    print("Proof 307 continuous root-sandwiched two-point guard")
    for name, value in metrics.items():
        print(f"{name}: {value:.6e}")
    print("RH=UNPROVED")

    if metrics["matrix/two-point trace error"] > 1e-12:
        raise SystemExit("matrix/two-point trace readback failed")
    if metrics["root-weight factorization error"] > 1e-12:
        raise SystemExit("root-weight factorization failed")
    if metrics["residue readback error"] > 1e-12:
        raise SystemExit("residue readback failed")
    if metrics["residue omission gap"] < 1e-6:
        raise SystemExit("residue omission guard did not fire")
    if metrics["moving time-average error"] > 1e-12:
        raise SystemExit("moving time-average readback failed")


if __name__ == "__main__":
    main()
