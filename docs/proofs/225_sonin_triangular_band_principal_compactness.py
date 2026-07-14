#!/usr/bin/env python3
"""Certificate for Proof 225's triangular-band principal channel.

The script checks three independent parts of the calculation:

1. the closed Mellin transform of the archimedean scattering kernel;
2. the two-integration-by-parts asymptotic of the triangular low-pass term;
3. local L2 convergence of a representative twice-differentiated convolution
   term.

The last check is a quadrature-stability test for one analytic ingredient of
the finite-window Hilbert--Schmidt proof.  It concerns one fixed triangular
width in the normalized principal channel; it does not approximate the
remaining de Branges amplitude correction or prove uniform Euler-mode bounds.
"""

from __future__ import annotations

import argparse
import math

import numpy as np


LANCZOS_COEFFICIENTS = np.array(
    [
        0.99999999999980993,
        676.5203681218851,
        -1259.1392167224028,
        771.32342877765313,
        -176.61502916214059,
        12.507343278686905,
        -0.13857109526572012,
        9.9843695780195716e-6,
        1.5056327351493116e-7,
    ]
)


def log_gamma_lanczos(values: np.ndarray) -> np.ndarray:
    shifted = values - 1
    series = np.full_like(values, LANCZOS_COEFFICIENTS[0], dtype=complex)
    for index, coefficient in enumerate(
        LANCZOS_COEFFICIENTS[1:], start=1
    ):
        series += coefficient / (shifted + index)
    tail = shifted + 7.5
    return (
        0.5 * np.log(2 * np.pi)
        + (shifted + 0.5) * np.log(tail)
        - tail
        + np.log(series)
    )


def archimedean_scattering(frequencies: np.ndarray) -> np.ndarray:
    arguments = 0.25 + 0.5j * frequencies
    log_gamma = log_gamma_lanczos(arguments)
    return np.exp(
        -1j * frequencies * math.log(math.pi)
        + log_gamma
        - np.conj(log_gamma)
    )


def closed_cosine_mellin(frequencies: np.ndarray) -> np.ndarray:
    powers = 0.5 - 1j * frequencies
    return 2 * np.exp(
        -powers * math.log(2 * math.pi)
        + log_gamma_lanczos(powers)
    ) * np.cos(math.pi * powers / 2)


def scattering_response(coordinates: np.ndarray) -> np.ndarray:
    exponential = np.exp(coordinates)
    return 2 * np.exp(coordinates / 2) * np.cos(2 * np.pi * exponential)


def scattering_response_second(coordinates: np.ndarray) -> np.ndarray:
    exponential = np.exp(coordinates)
    phase = 2 * np.pi * exponential
    return 2 * np.exp(coordinates / 2) * (
        (0.25 - phase**2) * np.cos(phase)
        - 2 * phase * np.sin(phase)
    )


def split_legendre_nodes(bound: float, order: int) -> tuple[np.ndarray, np.ndarray]:
    base_nodes, base_weights = np.polynomial.legendre.leggauss(order)
    half_bound = bound / 2
    left_nodes = half_bound * (base_nodes - 1)
    right_nodes = half_bound * (base_nodes + 1)
    weights = half_bound * base_weights
    return (
        np.concatenate((left_nodes, right_nodes)),
        np.concatenate((weights, weights)),
    )


def triangular_profile(coordinates: np.ndarray, bound: float) -> np.ndarray:
    return (
        math.pi
        * (bound - np.abs(coordinates))
        * scattering_response(coordinates)
    )


def triangular_transform(
    frequencies: np.ndarray, bound: float, order: int
) -> np.ndarray:
    coordinates, weights = split_legendre_nodes(bound, order)
    profile = triangular_profile(coordinates, bound)
    values = np.empty(len(frequencies), dtype=complex)
    for start in range(0, len(frequencies), 128):
        stop = min(start + 128, len(frequencies))
        phases = np.exp(1j * frequencies[start:stop, None] * coordinates)
        values[start:stop] = (phases @ (weights * profile)) / (2 * np.pi)
    return values


def triangular_asymptotic(frequencies: np.ndarray, bound: float) -> np.ndarray:
    response_zero = float(scattering_response(np.array([0.0]))[0])
    response_left = float(scattering_response(np.array([-bound]))[0])
    response_right = float(scattering_response(np.array([bound]))[0])
    return response_zero - 0.5 * (
        response_left * np.exp(-1j * bound * frequencies)
        + response_right * np.exp(1j * bound * frequencies)
    )


def differentiated_local_kernel(
    points: np.ndarray, bound: float, order: int
) -> np.ndarray:
    coordinates, weights = split_legendre_nodes(bound, order)
    profile = triangular_profile(coordinates, bound)
    values = np.empty(len(points), dtype=float)
    for start in range(0, len(points), 128):
        stop = min(start + 128, len(points))
        shifted = points[start:stop, None] - coordinates
        values[start:stop] = (
            scattering_response_second(shifted) @ (weights * profile)
        ) / (2 * np.pi)
    return values


def parse_integers(raw: str) -> list[int]:
    return [int(item.strip()) for item in raw.split(",") if item.strip()]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--prime", type=int, default=2)
    parser.add_argument("--orders", default="96,192,384")
    parser.add_argument("--max-mellin-error", type=float, default=2e-11)
    parser.add_argument("--max-asymptotic-error", type=float, default=2e-2)
    parser.add_argument("--max-kernel-delta", type=float, default=2e-5)
    args = parser.parse_args()

    if args.prime < 2:
        raise ValueError("prime must be at least 2")
    orders = parse_integers(args.orders)
    if len(orders) < 2 or min(orders) < 32:
        raise ValueError("orders must contain at least two values >= 32")

    bound = math.log(args.prime)
    mellin_frequencies = np.array([0.0, 0.5, 2.0, 7.0, 20.0])
    scattering = archimedean_scattering(mellin_frequencies)
    closed_mellin = closed_cosine_mellin(mellin_frequencies)
    mellin_error = float(np.max(np.abs(closed_mellin - np.conj(scattering))))

    frequency_scale = max(1.0, bound / math.log(2))
    asymptotic_frequencies = frequency_scale * np.array(
        [40.0, 80.0, 160.0, 320.0]
    )
    transform = triangular_transform(
        asymptotic_frequencies, bound, max(orders)
    )
    scaled_transform = asymptotic_frequencies**2 * transform
    asymptotic = triangular_asymptotic(asymptotic_frequencies, bound)
    asymptotic_errors = np.abs(scaled_transform - asymptotic)

    window = 2 * bound
    points = np.linspace(-window, window, 801)
    kernels = [
        differentiated_local_kernel(points, bound, order)
        for order in orders
    ]
    kernel_deltas = [
        float(
            np.sqrt(
                np.trapz(np.abs(right - left) ** 2, points)
            )
        )
        for left, right in zip(kernels, kernels[1:])
    ]
    local_l2_norm = float(
        np.sqrt(np.trapz(np.abs(kernels[-1]) ** 2, points))
    )

    print("identity=Sonin triangular-band principal channel")
    print(f"prime={args.prime} q={bound:.12f}")
    print(f"mellin_identity_error={mellin_error:.3e}")
    print(
        "scaled_asymptotic_errors="
        + ",".join(f"{value:.3e}" for value in asymptotic_errors)
    )
    print(
        "local_kernel_l2_deltas="
        + ",".join(f"{value:.3e}" for value in kernel_deltas)
    )
    print(f"local_kernel_l2_norm={local_l2_norm:.12f}")

    if mellin_error > args.max_mellin_error:
        raise RuntimeError("closed Mellin identity failed")
    if asymptotic_errors[-1] > args.max_asymptotic_error:
        raise RuntimeError("triangular asymptotic failed")
    if kernel_deltas[-1] > args.max_kernel_delta:
        raise RuntimeError("local differentiated kernel did not converge")

    print("certificate=PASS")
    print("principal_compactness_verdict=PASS")
    print("uniform_euler_mode_verdict=OPEN")
    print("full_metric_compactness_verdict=OPEN")
    print("sign_verdict=OPEN")


if __name__ == "__main__":
    main()
