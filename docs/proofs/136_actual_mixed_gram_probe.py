#!/usr/bin/env python3
"""Compute the same-square mixed crossing Gram for compact tests."""

import math

import numpy as np


def primes_up_to(limit: int) -> list[int]:
    result: list[int] = []
    for candidate in range(2, limit + 1):
        if all(candidate % divisor for divisor in range(2, int(candidate**0.5) + 1)):
            result.append(candidate)
    return result


def bump(coordinate: np.ndarray, width: float) -> np.ndarray:
    scaled = 2.0 * coordinate / width - 1.0
    values = np.zeros_like(coordinate)
    inside = np.abs(scaled) < 1.0
    values[inside] = np.exp(-1.0 / (1.0 - scaled[inside] ** 2))
    return values


def autocorrelation(
    coordinate: np.ndarray, test: np.ndarray, shift: float
) -> complex:
    shifted_real = np.interp(
        coordinate + shift, coordinate, test.real, left=0.0, right=0.0
    )
    shifted_imag = np.interp(
        coordinate + shift, coordinate, test.imag, left=0.0, right=0.0
    )
    shifted = shifted_real + 1j * shifted_imag
    return np.trapz(np.conjugate(test) * shifted, coordinate)


def gram_cost(width: float, frequency: float) -> tuple[int, float]:
    grid = np.linspace(0.0, width, 12001)
    test = bump(grid, width) * np.cos(frequency * grid)
    norm = math.sqrt(float(np.trapz(np.abs(test) ** 2, grid)))
    test /= norm

    primes = [
        prime
        for prime in primes_up_to(max(2, int(math.exp(width))))
        if math.log(prime) <= width
    ]
    coordinates = np.array([math.log(prime) for prime in primes])
    gram = np.empty((len(primes), len(primes)), dtype=complex)
    for row, left in enumerate(coordinates):
        for column, right in enumerate(coordinates):
            overlap = min(left, right)
            difference = right - left
            gram[row, column] = overlap * autocorrelation(
                grid, test, difference
            )

    weights = np.exp(-coordinates / 2.0)
    eigenvalues = np.linalg.eigvalsh(gram)
    if eigenvalues[0] < -1e-8:
        raise RuntimeError(f"Gram lost positivity: {eigenvalues[0]}")
    regularized = gram + 1e-10 * np.eye(len(primes))
    cost = float(np.real(weights @ np.linalg.solve(regularized, weights)))
    return len(primes), cost


if __name__ == "__main__":
    print("width frequency visible_primes mixed_gram_cost")
    for width in (1.4, 2.0, 3.0, 4.0):
        for frequency in (0.0, 5.0, 10.0, 20.0):
            count, value = gram_cost(width, frequency)
            print(f"{width:5.1f} {frequency:9.1f} {count:14d} {value:.12e}")
