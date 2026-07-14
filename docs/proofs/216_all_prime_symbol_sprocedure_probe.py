#!/usr/bin/env python3
"""Screen a scalar S-procedure for the all-prime principal form.

For roots supported in an interval of length ``T = log(c)``, the discrete
prime and continuous PNT-main quadratic forms have whole-line Fourier symbols

    k_c(t) = 2 sum_(q=p^m<c) Lambda(q) q^(-1/2) cos(t log q),
    k_0(t) = 2 integral_0^T exp(b/2) cos(t b) db.

If constants ``alpha <= 1/50`` and ``lambda >= 0`` made

    k_c(t) <= 2 + alpha (t^2 + 1/4) + lambda k_0(t)

hold for every real ``t``, the proved nonpositivity of ``K_0`` on the
cosh-neutral subspace would imply the desired Sobolev domination.  This
script searches for an immediate counterexample.  It is a reconnaissance
screen, not an interval certificate.
"""

from __future__ import annotations

import argparse
import math

import numpy as np
from scipy.optimize import minimize_scalar

from importlib import import_module


principal_probe = import_module("215_all_prime_principal_form_probe")


def prime_power_terms(cutoff: int) -> tuple[np.ndarray, np.ndarray]:
    shifts: list[float] = []
    weights: list[float] = []
    for prime in principal_probe.primes_up_to(cutoff):
        prime_power = prime
        while prime_power < cutoff:
            shifts.append(math.log(prime_power))
            weights.append(math.log(prime) / math.sqrt(prime_power))
            prime_power *= prime
    return np.asarray(shifts), np.asarray(weights)


def discrete_symbol(
    frequencies: np.ndarray, shifts: np.ndarray, weights: np.ndarray
) -> np.ndarray:
    values = np.zeros_like(frequencies)
    # Chunk by prime powers so the large-cutoff screen has bounded memory.
    for start in range(0, shifts.size, 512):
        stop = min(start + 512, shifts.size)
        values += 2 * np.sum(
            weights[start:stop, None]
            * np.cos(shifts[start:stop, None] * frequencies[None, :]),
            axis=0,
        )
    return values


def continuous_symbol(frequencies: np.ndarray, cutoff: int) -> np.ndarray:
    interval_length = math.log(cutoff)
    denominator = frequencies**2 + 0.25
    endpoint = interval_length * frequencies
    return 2 * (
        math.sqrt(cutoff)
        * (0.5 * np.cos(endpoint) + frequencies * np.sin(endpoint))
        - 0.5
    ) / denominator


def screen_lambda(
    frequencies: np.ndarray,
    discrete: np.ndarray,
    continuous: np.ndarray,
    multiplier: float,
    scalar_budget: float,
) -> tuple[float, float]:
    denominator = frequencies**2 + 0.25
    ratios = (
        discrete - multiplier * continuous - scalar_budget
    ) / denominator
    index = int(np.argmax(ratios))
    return float(ratios[index]), float(frequencies[index])


def feasible_multiplier_interval(
    frequencies: np.ndarray,
    discrete: np.ndarray,
    continuous: np.ndarray,
    scalar_budget: float,
    target_alpha: float,
) -> tuple[tuple[float, float], tuple[float, float]]:
    denominator = frequencies**2 + 0.25
    required = discrete - scalar_budget - target_alpha * denominator
    positive = continuous > 0
    negative = continuous < 0

    lower_candidates = np.where(positive, required / continuous, -np.inf)
    upper_candidates = np.where(negative, required / continuous, np.inf)
    lower_index = int(np.argmax(lower_candidates))
    upper_index = int(np.argmin(upper_candidates))
    return (
        (float(lower_candidates[lower_index]), float(frequencies[lower_index])),
        (float(upper_candidates[upper_index]), float(frequencies[upper_index])),
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--cutoff", type=int, default=10_000)
    parser.add_argument("--t-max", type=float, default=200.0)
    parser.add_argument("--step", type=float, default=0.005)
    parser.add_argument("--lambda-max", type=float, default=2.0)
    parser.add_argument("--scalar-budget", type=float, default=2.0)
    args = parser.parse_args()

    frequencies = np.arange(0.0, args.t_max + args.step / 2, args.step)
    shifts, weights = prime_power_terms(args.cutoff)
    discrete = discrete_symbol(frequencies, shifts, weights)
    continuous = continuous_symbol(frequencies, args.cutoff)

    objective = lambda multiplier: screen_lambda(
        frequencies,
        discrete,
        continuous,
        multiplier,
        args.scalar_budget,
    )[0]
    optimization = minimize_scalar(
        objective,
        bounds=(0.0, args.lambda_max),
        method="bounded",
        options={"xatol": 1e-12},
    )
    best_value, best_frequency = screen_lambda(
        frequencies,
        discrete,
        continuous,
        float(optimization.x),
        args.scalar_budget,
    )

    print(
        f"cutoff={args.cutoff} prime_power_terms={shifts.size} "
        f"frequency_count={frequencies.size}"
    )
    for multiplier in (0.0, 0.5, 0.8, 0.9, 1.0, 1.1, 1.2):
        value, frequency = screen_lambda(
            frequencies,
            discrete,
            continuous,
            multiplier,
            args.scalar_budget,
        )
        print(
            f"lambda={multiplier:.12f} max_ratio={value:.12f} "
            f"at_t={frequency:.12f}"
        )
    print(
        f"best_grid_lambda={optimization.x:.12f} "
        f"best_grid_max_ratio={best_value:.12f} "
        f"at_t={best_frequency:.12f}"
    )
    no_scalar_value, no_scalar_frequency = screen_lambda(
        frequencies,
        discrete,
        continuous,
        float(optimization.x),
        0.0,
    )
    print(
        f"same_lambda_no_scalar_max_ratio={no_scalar_value:.12f} "
        f"at_t={no_scalar_frequency:.12f}"
    )
    target_alpha = 1 / 50
    lower, upper = feasible_multiplier_interval(
        frequencies,
        discrete,
        continuous,
        args.scalar_budget,
        target_alpha,
    )
    print(
        f"lambda_lower_bound={lower[0]:.12f} at_t={lower[1]:.12f}"
    )
    print(
        f"lambda_upper_bound={upper[0]:.12f} at_t={upper[1]:.12f}"
    )
    print(f"target_alpha={target_alpha:.12f}")


if __name__ == "__main__":
    main()
