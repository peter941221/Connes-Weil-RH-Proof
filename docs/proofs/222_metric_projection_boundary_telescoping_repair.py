#!/usr/bin/env python3
"""Check the metric-projection boundary telescoping from Proof 222.

For the bilateral shift S e_n=e_(n-1), let P project onto n>=0 and let P_a be
the orthogonal projection onto (I-aS) Ran(P).  The exact infinite-fiber result
is

    q_0 = 0,
    q_k = -a**abs(k)  (k != 0),

where q_k is the sum of P_a-P along translation diagonal k.  This script
constructs finite projections from their range matrices and checks convergence
to those coefficients and to the resulting convolution trace.
"""

from __future__ import annotations

import argparse
import math

import numpy as np


def parse_radii(raw: str) -> list[int]:
    return [int(item.strip()) for item in raw.split(",") if item.strip()]


def finite_metric_projection(
    parameter: float, radius: int
) -> tuple[np.ndarray, np.ndarray]:
    indices = np.arange(-1, radius + 1)
    size = len(indices)
    transfer = np.zeros((size, radius + 1), dtype=float)

    for column, index in enumerate(range(radius + 1)):
        transfer[index + 1, column] = 1.0
        transfer[index, column] = -parameter

    gram = transfer.T @ transfer
    projection = transfer @ np.linalg.solve(gram, transfer.T)
    base_projection = np.diag((indices >= 0).astype(float))
    return indices, projection - base_projection


def diagonal_sum(
    indices: np.ndarray, difference: np.ndarray, degree: int
) -> complex:
    total = 0.0j
    for row, row_index in enumerate(indices):
        for column, column_index in enumerate(indices):
            if column_index - row_index == degree:
                total += difference[row, column]
    return total


def test_kernel(value: float) -> complex:
    return np.exp(-0.35 * value * value + 0.7j * value)


def expected_trace(parameter: float, cell_length: float) -> complex:
    total = 0.0j
    for exponent in range(1, 10000):
        term = parameter**exponent * (
            test_kernel(exponent * cell_length)
            + test_kernel(-exponent * cell_length)
        )
        total -= cell_length * term
        if abs(term) < 1e-16:
            break
    return total


def sampled_trace(
    indices: np.ndarray, difference: np.ndarray, cell_length: float
) -> complex:
    convolution = np.empty(difference.shape, dtype=complex)
    for row, row_index in enumerate(indices):
        for column, column_index in enumerate(indices):
            convolution[row, column] = test_kernel(
                (row_index - column_index) * cell_length
            )
    return cell_length * np.trace(convolution @ difference)


def boundary_counts() -> tuple[int, int, int]:
    indices = np.arange(-4, 5)
    size = len(indices)
    shift = np.zeros((size, size))
    index_to_row = {int(index): row for row, index in enumerate(indices)}
    for index in indices:
        target = int(index - 1)
        if target in index_to_row:
            shift[index_to_row[target], index_to_row[int(index)]] = 1.0

    positive = np.diag((indices >= 0).astype(float))
    negative = np.eye(size) - positive
    full = negative @ shift @ shift @ positive
    interrupted = negative @ shift @ negative @ shift @ positive
    telescoped = full - interrupted
    tolerance = 1e-12
    return (
        int(np.count_nonzero(np.abs(full) > tolerance)),
        int(np.count_nonzero(np.abs(interrupted) > tolerance)),
        int(np.count_nonzero(np.abs(telescoped) > tolerance)),
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--prime", type=int, default=2)
    parser.add_argument("--radii", default="8,16,32,64")
    parser.add_argument("--max-degree", type=int, default=8)
    parser.add_argument("--max-error", type=float, default=1e-10)
    args = parser.parse_args()

    if args.prime < 2:
        raise ValueError("prime must be at least 2")
    radii = parse_radii(args.radii)
    if not radii or min(radii) < args.max_degree:
        raise ValueError("every radius must be at least max-degree")

    parameter = 1.0 / math.sqrt(args.prime)
    cell_length = math.log(args.prime)
    target_trace = expected_trace(parameter, cell_length)
    full_count, interrupted_count, telescoped_count = boundary_counts()

    print("identity=metric-projection boundary telescoping")
    print(f"prime={args.prime}")
    print(f"a={parameter:.15g}")
    print(f"L={cell_length:.15g}")
    print(
        "p2_boundary_counts="
        f"full:{full_count} interrupted:{interrupted_count} "
        f"telescoped:{telescoped_count}"
    )
    print(
        "expected_trace="
        f"{target_trace.real:+.12g}{target_trace.imag:+.3e}j"
    )

    finest_coefficient_error = math.inf
    finest_trace_error = math.inf
    for radius in radii:
        indices, difference = finite_metric_projection(parameter, radius)
        projection = difference + np.diag((indices >= 0).astype(float))
        self_adjoint_error = float(
            np.linalg.norm(projection - projection.T, ord=2)
        )
        idempotence_error = float(
            np.linalg.norm(projection @ projection - projection, ord=2)
        )

        coefficient_errors = []
        for degree in range(-args.max_degree, args.max_degree + 1):
            expected = 0.0 if degree == 0 else -(parameter ** abs(degree))
            coefficient_errors.append(
                abs(diagonal_sum(indices, difference, degree) - expected)
            )
        coefficient_error = float(max(coefficient_errors))

        actual_trace = sampled_trace(indices, difference, cell_length)
        trace_error = float(abs(actual_trace - target_trace))
        p2_ratio = (
            diagonal_sum(indices, difference, 2) / (-(parameter**2))
        ).real

        print(
            f"radius={radius} "
            f"self_adjoint_error={self_adjoint_error:.3e} "
            f"idempotence_error={idempotence_error:.3e} "
            f"max_coefficient_error={coefficient_error:.3e} "
            f"p2_ratio={p2_ratio:.12f} "
            f"trace={actual_trace.real:+.12g}{actual_trace.imag:+.3e}j "
            f"trace_error={trace_error:.3e}"
        )

        finest_coefficient_error = coefficient_error
        finest_trace_error = trace_error

    if (full_count, interrupted_count, telescoped_count) != (2, 1, 1):
        raise RuntimeError("the p^2 boundary count is not 2-1=1")
    if finest_coefficient_error > args.max_error:
        raise RuntimeError("Laurent coefficients did not converge sufficiently")
    if finest_trace_error > args.max_error:
        raise RuntimeError("convolution trace did not converge sufficiently")
    print("certificate=PASS")


if __name__ == "__main__":
    main()
