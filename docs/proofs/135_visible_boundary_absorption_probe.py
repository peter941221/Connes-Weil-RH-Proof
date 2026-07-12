#!/usr/bin/env python3
"""Scan support-aware visible-prime boundary-potential absorption."""

import math

import numpy as np


def primes_up_to(limit: int) -> list[int]:
    result: list[int] = []
    for candidate in range(2, limit + 1):
        if all(candidate % divisor for divisor in range(2, int(candidate**0.5) + 1)):
            result.append(candidate)
    return result


def absorption_constant(window: float, size: int = 400) -> float:
    step = window / (size + 1)
    coordinate = np.arange(1, size + 1) * step
    potential = np.zeros_like(coordinate)
    for prime in primes_up_to(max(2, int(math.exp(window)))):
        shift = math.log(float(prime))
        if shift > window:
            continue
        a = prime**-0.5
        first_interval = np.maximum(1, np.ceil(coordinate / shift).astype(int))
        maximum_power = int(window / shift)
        potential += np.array(
            [
                sum(a**power / power for power in range(int(index), maximum_power + 1))
                for index in first_interval
            ]
        )

    stiffness = np.diag(np.full(size, 2.0 / step + 0.25 * step))
    stiffness += np.diag(np.full(size - 1, -1.0 / step), 1)
    stiffness += np.diag(np.full(size - 1, -1.0 / step), -1)
    mass_potential = np.diag(step * potential)
    eigenvalues, eigenvectors = np.linalg.eigh(stiffness)
    inverse_sqrt = eigenvectors @ np.diag(1.0 / np.sqrt(eigenvalues)) @ eigenvectors.T
    normalized = inverse_sqrt @ mass_potential @ inverse_sqrt
    return float(np.linalg.eigvalsh(normalized)[-1])


if __name__ == "__main__":
    print("window visible_primes absorption_constant")
    for window in (0.25, 0.5, 0.7, 1.0, 1.4, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0):
        count = len([p for p in primes_up_to(max(2, int(math.exp(window)))) if math.log(p) <= window])
        print(f"{window:6.2f} {count:14d} {absorption_constant(window):.12e}")
