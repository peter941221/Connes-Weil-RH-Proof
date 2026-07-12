#!/usr/bin/env python3
"""Probe the shared half-line Brownian Gram Schur cost."""

import math

import numpy as np


def first_primes(count: int) -> list[int]:
    result: list[int] = []
    candidate = 2
    while len(result) < count:
        if all(candidate % divisor for divisor in range(2, int(candidate**0.5) + 1)):
            result.append(candidate)
        candidate += 1
    return result


def cost(count: int) -> float:
    primes = first_primes(count)
    coordinates = np.array([math.log(prime) for prime in primes])
    gram = np.minimum.outer(coordinates, coordinates)
    weights = np.exp(-coordinates / 2.0)
    return float(weights @ np.linalg.solve(gram, weights))


def telescoping_cost(count: int) -> float:
    primes = first_primes(count)
    coordinates = np.array([math.log(prime) for prime in primes])
    weights = np.exp(-coordinates / 2.0)
    result = weights[0] ** 2 / coordinates[0]
    result += float(
        np.sum(
            np.square(np.diff(weights)) / np.diff(coordinates)
        )
    )
    return float(result)


if __name__ == "__main__":
    print("count direct_cost telescoping_cost")
    for count in (1, 2, 3, 5, 10, 20, 40, 80, 120):
        print(f"{count:5d} {cost(count):.12e} {telescoping_cost(count):.12e}")
    uniform_bound = 1.0 / (2.0 * math.log(2.0)) + 1.0 / 8.0
    print(f"uniform_bound {uniform_bound:.12e}")
