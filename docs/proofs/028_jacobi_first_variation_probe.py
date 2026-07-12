"""First Euler variation of archimedean Jacobi recurrence coefficients."""

import numpy as np


def scaling_matrix(size: int):
    indices = np.arange(size - 1, dtype=float)
    coefficients = 0.5 * np.sqrt((2 * indices + 1) * (2 * indices + 2))
    return np.diag(coefficients, 1) + np.diag(coefficients, -1)


def first_variation(size: int, log_prime: float):
    scaling = scaling_matrix(size)
    values, vectors = np.linalg.eigh(scaling)
    cosine = vectors @ np.diag(np.cos(log_prime * values)) @ vectors.T
    row, column = np.indices((size, size))
    generator = np.sign(row - column) * cosine
    variation = generator @ scaling - scaling @ generator
    return np.diag(variation, 1)


sample_indices = (16, 24, 32, 48, 64, 80, 96, 128)
for section in (256, 384, 512):
    variation = first_variation(section, np.log(2.0))
    print(f"section={section}")
    for index in sample_indices:
        print(f"  n={index:3d}  da_n/da={variation[index]: .10f}")
