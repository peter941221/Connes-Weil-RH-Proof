#!/usr/bin/env python3
"""Check the second-order expansion of the Euler-log graph projection.

This is a finite-matrix algebra check.  It verifies that the graph projection
differs from its off-diagonal Euler-log read-off only at order a^3: the two
order-a^2 diagonal trace terms cancel for a translation-invariant same-square
test matrix.  It is not evidence for an infinite-dimensional trace identity.
"""

import numpy as np


def left_shift(size: int, step: int) -> np.ndarray:
    shift = np.zeros((size, size))
    for column in range(step, size):
        shift[column - step, column] = 1.0
    return shift


def euler_log_crossing(
    shift: np.ndarray,
    negative: np.ndarray,
    positive: np.ndarray,
    parameter: float,
    terms: int,
) -> np.ndarray:
    power = np.eye(shift.shape[0])
    logarithm = np.zeros_like(shift)
    for exponent in range(1, terms + 1):
        power = power @ shift
        logarithm += parameter**exponent / exponent * power
    return logarithm[np.ix_(negative, positive)]


def graph_projection(crossing: np.ndarray) -> np.ndarray:
    negative_size, positive_size = crossing.shape
    graph_basis = np.vstack((crossing, np.eye(positive_size)))
    gram = graph_basis.T @ graph_basis
    return graph_basis @ np.linalg.solve(gram, graph_basis.T)


def run_probe() -> None:
    size = 320
    half = size // 2
    negative = np.arange(half)
    positive = np.arange(half, size)
    shift = left_shift(size, step=7)

    indices = np.arange(size)
    distance = indices[:, None] - indices[None, :]
    same_square = np.exp(-np.square(distance) / (2.0 * 11.0**2))

    base_projection = np.zeros((size, size))
    base_projection[half:, half:] = np.eye(half)

    print("a graph_trace linear_trace residual residual_over_a3")
    for parameter in (0.08, 0.06, 0.04, 0.03, 0.02, 0.015, 0.01):
        crossing = euler_log_crossing(
            shift, negative, positive, parameter, terms=8
        )
        graph_delta = graph_projection(crossing) - base_projection

        linear_delta = np.zeros((size, size))
        linear_delta[:half, half:] = crossing
        linear_delta[half:, :half] = crossing.T

        graph_trace = float(np.trace(same_square @ graph_delta))
        linear_trace = float(np.trace(same_square @ linear_delta))
        residual = graph_trace - linear_trace
        print(
            f"{parameter:.3f} {graph_trace:.12e} {linear_trace:.12e} "
            f"{residual:.12e} {residual / parameter**3:.12e}"
        )


if __name__ == "__main__":
    run_probe()
