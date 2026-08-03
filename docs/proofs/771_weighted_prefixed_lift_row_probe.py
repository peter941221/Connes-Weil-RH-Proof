#!/usr/bin/env python3
"""Finite checks for Proof 771's weighted prefixed lift row."""

from __future__ import annotations

import numpy as np


def random_complex(rng: np.random.Generator, rows: int, cols: int) -> np.ndarray:
    return rng.standard_normal((rows, cols)) + 1j * rng.standard_normal((rows, cols))


def hs_inner(left: np.ndarray, right: np.ndarray) -> complex:
    return np.trace(left.conj().T @ right)


def hs_norm_sq(operator: np.ndarray) -> float:
    return float(np.linalg.norm(operator, ord="fro") ** 2)


def contraction(rng: np.random.Generator, rows: int, cols: int) -> np.ndarray:
    matrix = random_complex(rng, rows, cols)
    spectral_norm = np.linalg.norm(matrix, ord=2)
    return matrix / max(1.0, spectral_norm)


def check_weighted_prefixed_lift_row() -> dict[str, float]:
    rng = np.random.default_rng(771)
    source_dim = 4
    output_dims = [3, 2, 5]
    weights = np.array([1.0, 2.0, 4.0])
    prefix_scales = np.array([0.91, 0.67, 0.43])
    range_shares = np.array([0.18, 0.31, 0.41])

    lifts = [random_complex(rng, source_dim, dimension) for dimension in output_dims]
    prefixes = [scale * np.eye(source_dim) for scale in prefix_scales]
    corners = [prefix @ lift for prefix, lift in zip(prefixes, lifts)]

    weighted_row = np.concatenate(
        [lift / np.sqrt(weight) for lift, weight in zip(lifts, weights)], axis=1
    )
    left, singular_values, right_adjoint = np.linalg.svd(
        weighted_row, full_matrices=False
    )
    square_root = np.sqrt(singular_values)
    common_input = left * square_root
    detector_row_adjoint = square_root[:, None] * right_adjoint
    trace_norm = float(np.sum(singular_values))

    detector_adjoint_blocks: list[np.ndarray] = []
    start = 0
    for dimension, weight in zip(output_dims, weights):
        stop = start + dimension
        detector_adjoint_blocks.append(
            np.sqrt(weight) * detector_row_adjoint[:, start:stop]
        )
        start = stop

    factorization_error = np.linalg.norm(
        weighted_row - common_input @ detector_row_adjoint
    )
    lift_recovery_error = max(
        np.linalg.norm(
            lift - common_input @ detector_adjoint
        )
        for lift, detector_adjoint in zip(lifts, detector_adjoint_blocks)
    )
    corner_factorization_error = max(
        np.linalg.norm(corner - prefix @ common_input @ detector_adjoint)
        for corner, prefix, detector_adjoint in zip(
            corners, prefixes, detector_adjoint_blocks
        )
    )

    detector_budget = sum(
        hs_norm_sq(detector_adjoint) / weight
        for detector_adjoint, weight in zip(detector_adjoint_blocks, weights)
    )
    input_budget = hs_norm_sq(common_input)

    base_ranges = [
        contraction(rng, dimension, source_dim) for dimension in output_dims
    ]
    ranges = [
        np.sqrt(share / weight) * base
        for share, weight, base in zip(range_shares, weights, base_ranges)
    ]
    range_images = [
        range_map @ prefix @ common_input
        for range_map, prefix in zip(ranges, prefixes)
    ]
    range_budget = sum(
        weight * hs_norm_sq(image) for weight, image in zip(weights, range_images)
    )
    response = 2.0 * abs(
        sum(
            hs_inner(detector_adjoint.conj().T, image)
            for detector_adjoint, image in zip(detector_adjoint_blocks, range_images)
        )
    )
    weighted_cauchy_bound = 2.0 * np.sqrt(detector_budget * range_budget)
    trace_norm_bound = 2.0 * trace_norm

    return {
        "polar_factorization_error": factorization_error,
        "lift_recovery_error": lift_recovery_error,
        "corner_factorization_error": corner_factorization_error,
        "detector_budget_error": abs(detector_budget - trace_norm),
        "input_budget_error": abs(input_budget - trace_norm),
        "range_bessel_overrun": max(0.0, range_budget - input_budget),
        "weighted_cauchy_overrun": max(0.0, response - weighted_cauchy_bound),
        "trace_norm_overrun": max(0.0, response - trace_norm_bound),
    }


def check_rank_deficient_visibility_obstruction() -> dict[str, float]:
    prefix = np.array([[1.0, 0.0], [0.0, 0.0]], dtype=np.complex128)
    bad_corner = np.array([[0.0, 0.0], [1.0, 0.0]], dtype=np.complex128)
    invisible_vector = np.array([0.0, 1.0], dtype=np.complex128)

    return {
        "prefix_adjoint_on_invisible": np.linalg.norm(
            prefix.conj().T @ invisible_vector
        ),
        "corner_adjoint_on_invisible": np.linalg.norm(
            bad_corner.conj().T @ invisible_vector
        ),
    }


def main() -> None:
    row = check_weighted_prefixed_lift_row()
    visibility = check_rank_deficient_visibility_obstruction()
    tolerance = 3e-11

    for name, value in row.items():
        print(f"{name:36s} {value:.12e}")
    for name, value in visibility.items():
        print(f"{name:36s} {value:.12e}")

    if max(row.values()) > tolerance:
        raise SystemExit("weighted prefixed lift-row check failed")
    if visibility["prefix_adjoint_on_invisible"] > tolerance:
        raise SystemExit("chosen vector is visible to the prefix")
    if visibility["corner_adjoint_on_invisible"] <= 0.5:
        raise SystemExit("rank-deficient prefix obstruction was not detected")


if __name__ == "__main__":
    main()
