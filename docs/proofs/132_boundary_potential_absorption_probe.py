#!/usr/bin/env python3
"""Finite-difference screen for a one-prime boundary-potential bound."""

import math

import numpy as np


def run(size: int, primes: tuple[int, ...]) -> None:
    length = 20.0
    step = length / (size + 1)
    coordinate = np.arange(1, size + 1) * step
    potential = np.zeros_like(coordinate)
    for prime in primes:
        a = prime**-0.5
        shift = math.log(float(prime))
        first_interval = np.maximum(1, np.ceil(coordinate / shift).astype(int))
        potential += np.array(
            [sum(a**k / k for k in range(int(index), 800)) for index in first_interval]
        )

    stiffness = np.diag(np.full(size, 2.0 / step + 0.25 * step))
    stiffness += np.diag(np.full(size - 1, -1.0 / step), 1)
    stiffness += np.diag(np.full(size - 1, -1.0 / step), -1)
    mass_potential = np.diag(step * potential)

    eigenvalues, eigenvectors = np.linalg.eigh(stiffness)
    inverse_sqrt = eigenvectors @ np.diag(1.0 / np.sqrt(eigenvalues)) @ eigenvectors.T
    normalized = inverse_sqrt @ mass_potential @ inverse_sqrt
    largest = np.linalg.eigvalsh(normalized)[-1]
    print(
        f"primes={','.join(map(str, primes)):8s} size={size:4d} "
        f"absorption_constant={largest:.12e}"
    )


if __name__ == "__main__":
    for primes in ((2,), (2, 3), (2, 3, 5), (2, 3, 5, 7, 11)):
        run(400, primes)
