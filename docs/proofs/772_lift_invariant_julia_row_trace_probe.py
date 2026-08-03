#!/usr/bin/env python3
"""Finite checks for Proof 772's lift-invariant Julia row trace."""

from __future__ import annotations

import numpy as np


def random_complex(rng: np.random.Generator, rows: int, cols: int) -> np.ndarray:
    return rng.standard_normal((rows, cols)) + 1j * rng.standard_normal((rows, cols))


def contraction(rng: np.random.Generator, rows: int, cols: int) -> np.ndarray:
    matrix = random_complex(rng, rows, cols)
    return matrix / max(1.0, np.linalg.norm(matrix, ord=2))


def trace_norm(operator: np.ndarray) -> float:
    return float(np.sum(np.linalg.svd(operator, compute_uv=False)))


def check_lift_invariant_julia_row_trace() -> dict[str, float]:
    rng = np.random.default_rng(772)
    source_dim = 4
    output_dims = [3, 2, 5]
    weights = np.array([1.0, 2.0, 4.0])
    range_shares = np.array([0.17, 0.29, 0.43])
    prefixes = [
        np.diag([0.91, 0.62, 0.0, 0.0]),
        np.diag([0.83, 0.54, 0.0, 0.0]),
        np.diag([0.74, 0.47, 0.0, 0.0]),
    ]

    lifts = [random_complex(rng, source_dim, dimension) for dimension in output_dims]
    null_lifts = []
    for dimension in output_dims:
        null_lift = np.zeros((source_dim, dimension), dtype=np.complex128)
        null_lift[2:, :] = random_complex(rng, 2, dimension)
        null_lifts.append(null_lift)

    base_ranges = [
        contraction(rng, dimension, source_dim) for dimension in output_dims
    ]
    ranges = [
        np.sqrt(share / weight) * base
        for share, weight, base in zip(range_shares, weights, base_ranges)
    ]
    corners = [prefix @ lift for prefix, lift in zip(prefixes, lifts)]

    julia_row = np.vstack(
        [
            np.sqrt(weight) * range_map @ prefix
            for weight, range_map, prefix in zip(weights, ranges, prefixes)
        ]
    )
    lift_row = np.hstack(
        [lift / np.sqrt(weight) for lift, weight in zip(lifts, weights)]
    )
    row_product = julia_row @ lift_row
    row_trace = np.trace(row_product)
    physical_trace = sum(
        np.trace(range_map @ corner)
        for range_map, corner in zip(ranges, corners)
    )

    kappa = 25.0
    perturbed_lifts = [
        lift + kappa * null_lift for lift, null_lift in zip(lifts, null_lifts)
    ]
    perturbed_corners = [
        prefix @ lift for prefix, lift in zip(prefixes, perturbed_lifts)
    ]
    perturbed_lift_row = np.hstack(
        [lift / np.sqrt(weight) for lift, weight in zip(perturbed_lifts, weights)]
    )
    perturbed_trace = np.trace(julia_row @ perturbed_lift_row)
    base_trace_norm = trace_norm(lift_row)
    perturbed_trace_norm = trace_norm(perturbed_lift_row)

    return {
        "julia_row_contraction_overrun": max(
            0.0, np.linalg.norm(julia_row, ord=2) - 1.0
        ),
        "diagonal_trace_error": abs(row_trace - physical_trace),
        "null_lift_prefix_error": max(
            np.linalg.norm(prefix @ null_lift)
            for prefix, null_lift in zip(prefixes, null_lifts)
        ),
        "null_lift_corner_error": max(
            np.linalg.norm(original - perturbed)
            for original, perturbed in zip(corners, perturbed_corners)
        ),
        "lift_invariance_error": abs(row_trace - perturbed_trace),
        "trace_norm_growth": perturbed_trace_norm - base_trace_norm,
    }


def main() -> None:
    checks = check_lift_invariant_julia_row_trace()
    tolerance = 3e-11

    for name, value in checks.items():
        print(f"{name:34s} {value:.12e}")

    for name, value in checks.items():
        if name != "trace_norm_growth" and value > tolerance:
            raise SystemExit("lift-invariant Julia row-trace check failed")
    if checks["trace_norm_growth"] <= 1.0:
        raise SystemExit("null lifts did not expose trace-norm noninvariance")


if __name__ == "__main__":
    main()
