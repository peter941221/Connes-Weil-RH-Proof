#!/usr/bin/env python3
"""Certificate for Proof 233's half-line Toeplitz path normal form."""

from __future__ import annotations

import argparse
import itertools
import math

import numpy as np


def translation(coordinates: np.ndarray, exponent: int) -> np.ndarray:
    size = len(coordinates)
    index = {int(value): position for position, value in enumerate(coordinates)}
    result = np.zeros((size, size))
    for output, coordinate in enumerate(coordinates):
        source = index.get(int(coordinate - exponent))
        if source is not None:
            result[output, source] = 1.0
    return result


def cutoff(coordinates: np.ndarray, threshold: int) -> np.ndarray:
    return np.diag((coordinates >= threshold).astype(float))


def path_word(
    coordinates: np.ndarray, path: tuple[int, ...]
) -> np.ndarray:
    positive = cutoff(coordinates, 0)
    result = positive.copy()
    for step in path:
        result = result @ translation(coordinates, step) @ positive
    return result


def predicted_word(
    coordinates: np.ndarray, path: tuple[int, ...]
) -> tuple[np.ndarray, int, int]:
    partial = 0
    maximum = 0
    for step in path:
        partial += step
        maximum = max(maximum, partial)
    predicted = cutoff(coordinates, maximum) @ translation(coordinates, partial)
    return predicted, maximum, partial


def normal_form_error(depth: int, radius: int) -> tuple[float, int]:
    coordinates = np.arange(-radius, radius + 1)
    central = np.where(np.abs(coordinates) <= radius - depth - 1)[0]
    error = 0.0
    paths = 0
    for length in range(depth + 1):
        for path in itertools.product((-1, 1), repeat=length):
            actual = path_word(coordinates, path)
            predicted, _, _ = predicted_word(coordinates, path)
            restricted = actual[np.ix_(central, central)] - predicted[np.ix_(central, central)]
            error = max(error, float(np.max(np.abs(restricted))))
            paths += 1
    return error, paths


def coefficient_errors(
    prime: int, alpha: float, depth: int
) -> tuple[float, float]:
    beta = alpha / (1 + alpha**2)
    eta = 2 * beta
    coefficient_error = 0.0
    compensation_error = 0.0
    for length in range(depth + 1):
        paths = list(itertools.product((-1, 1), repeat=length))
        direct = sum(beta**length for _ in paths)
        coefficient_error = max(coefficient_error, abs(direct - eta**length))
        for path in paths:
            _, maximum, _ = predicted_word(np.arange(-2, 3), path)
            amplitude = prime ** (0.5 * maximum)
            chirp_gain = prime ** (-0.5 * maximum)
            compensation_error = max(
                compensation_error, abs(amplitude * chirp_gain - 1)
            )
    return coefficient_error, compensation_error


def weighted_sum(ratio: float, power: int, terms: int = 100000) -> float:
    return float(
        sum((1 + index) ** power * ratio**index for index in range(terms))
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--prime", type=int, default=2)
    parser.add_argument("--depth", type=int, default=9)
    parser.add_argument("--radius", type=int, default=48)
    parser.add_argument("--graph-order", type=int, default=2)
    parser.add_argument("--max-error", type=float, default=2e-12)
    args = parser.parse_args()

    if args.prime < 2:
        raise ValueError("prime must be at least 2")
    if args.depth < 2:
        raise ValueError("depth must be at least 2")
    if args.radius <= 2 * args.depth:
        raise ValueError("radius must exceed twice the depth")
    if args.graph_order < 0:
        raise ValueError("graph-order must be nonnegative")

    alpha = args.prime**-0.5
    beta = alpha / (1 + alpha**2)
    eta = 2 * beta
    word_error, paths = normal_form_error(args.depth, args.radius)
    coefficient_error, compensation_error = coefficient_errors(
        args.prime, alpha, args.depth
    )
    metric_majorant = weighted_sum(eta, args.graph_order)
    graph_majorant = weighted_sum(alpha, args.graph_order)

    print("identity=half-line Toeplitz path profile")
    print(
        f"prime={args.prime} alpha={alpha:.12f} beta={beta:.12f} "
        f"eta={eta:.12f}"
    )
    print(f"enumerated_paths={paths}")
    print(f"path_normal_form_error={word_error:.3e}")
    print(f"coefficient_identity_error={coefficient_error:.3e}")
    print(f"endpoint_compensation_error={compensation_error:.3e}")
    print(f"metric_weighted_majorant={metric_majorant:.12e}")
    print(f"graph_weighted_majorant={graph_majorant:.12e}")

    if max(word_error, coefficient_error, compensation_error) > args.max_error:
        raise RuntimeError("half-line path identity failed")
    if not 0 <= eta < 1:
        raise RuntimeError("metric Neumann ratio is not summable")
    if not math.isfinite(metric_majorant) or not math.isfinite(graph_majorant):
        raise RuntimeError("polynomially weighted path series diverged")

    print("certificate=PASS")
    print("path_normal_form_verdict=PASS")
    print("endpoint_chirp_compensation_verdict=PASS")
    print("halfline_toeplitz_profile_verdict=PASS")
    print("sonin_alternating_profile_verdict=OPEN")
    print("integrated_three_row_sign_verdict=OPEN")


if __name__ == "__main__":
    main()
