#!/usr/bin/env python3
"""Finite-section check for the single-crossing leak proved in record 206.

The proof is the second-order operator expansion. This script only checks the
(-1, 0) translation-fiber matrix entry of the exact compressed inverse.
"""

import numpy as np


def crossing_entry(parameter: float, radius: int = 48) -> tuple[float, float, float]:
    indices = np.arange(-radius, radius + 1)
    positive = indices >= 0
    negative = ~positive
    size = len(indices)

    euler_log = np.zeros((size, size))
    for exponent in range(1, radius + 1):
        coefficient = -(parameter**exponent) / exponent
        euler_log += coefficient * (
            np.eye(size, k=exponent) + np.eye(size, k=-exponent)
        )

    scalar_bound = 2.0 * np.log1p(parameter)
    inverse_metric = (1.0 + scalar_bound) * np.eye(size) - euler_log
    positive_columns = np.linalg.solve(
        inverse_metric, np.eye(size)[:, positive]
    )
    compressed_metric = positive_columns[positive, :]
    actual = np.linalg.solve(
        compressed_metric.T, positive_columns[negative, :].T
    ).T
    selected = euler_log[np.ix_(negative, positive)]

    row = np.flatnonzero(indices[negative] == -1)[0]
    column = np.flatnonzero(indices[positive] == 0)[0]
    error = actual[row, column] - selected[row, column]
    return selected[row, column], actual[row, column], error / parameter**2


def main() -> None:
    print("a selected[-1,0] actual[-1,0] error_over_a2")
    for parameter in (0.03, 0.05, 0.08, 1 / np.sqrt(101), 1 / np.sqrt(2)):
        selected, actual, ratio = crossing_entry(parameter)
        print(
            f"{parameter:.12f} {selected:.12e} "
            f"{actual:.12e} {ratio:.9f}"
        )


if __name__ == "__main__":
    main()
