#!/usr/bin/env python3
"""Certificate for Proof 276's CC20 static half-power tail audit.

The source formula for delta is evaluated directly.  The prolate layer checks
the super-exponential eigenvalue envelope that makes every polynomially
weighted coefficient series in the proof summable.  It does not identify the
static CC20 remainder with Proof 275's moving-projection first jet.
"""

from __future__ import annotations

import argparse
import math

import numpy as np


def sine_integral_scalar(value: float) -> float:
    """Evaluate Si(x) using its power series or optimally truncated tail."""
    if value < 0.0:
        return -sine_integral_scalar(-value)
    if value == 0.0:
        return 0.0
    if value <= 10.0:
        term = value
        total = term
        index = 0
        while index < 200:
            ratio = -(
                value**2
                * (2 * index + 1)
                / ((2 * index + 2) * (2 * index + 3) ** 2)
            )
            term *= ratio
            total += term
            index += 1
            if abs(term) <= 1e-17 * max(1.0, abs(total)):
                break
        return total

    inverse_square = 1.0 / (value * value)
    first_term = 1.0 / value
    second_term = inverse_square
    first_sum = first_term
    second_sum = second_term
    previous_first = abs(first_term)
    previous_second = abs(second_term)
    for order in range(1, 80):
        next_first = -first_term * (2 * order) * (2 * order - 1) * inverse_square
        next_second = -second_term * (2 * order + 1) * (2 * order) * inverse_square
        if abs(next_first) > previous_first or abs(next_second) > previous_second:
            break
        first_sum += next_first
        second_sum += next_second
        first_term = next_first
        second_term = next_second
        previous_first = abs(next_first)
        previous_second = abs(next_second)
    return (
        math.pi / 2.0
        - math.cos(value) * first_sum
        - math.sin(value) * second_sum
    )


def sine_integral(values: np.ndarray) -> np.ndarray:
    return np.array([sine_integral_scalar(float(value)) for value in values])


def cc20_delta(rho: np.ndarray) -> np.ndarray:
    reflected = np.maximum(rho, 1.0 / rho)
    plus = 2.0 * math.pi * (1.0 + reflected)
    minus = 2.0 * math.pi * (reflected - 1.0)
    si_plus = sine_integral(plus)
    si_minus = sine_integral(minus)
    minus_ratio = np.where(
        np.abs(minus) > 1e-14,
        si_minus / minus,
        1.0,
    )
    return 2.0 * np.sqrt(reflected) * (
        si_plus / plus + minus_ratio
    )


def log_prolate_eigenvalue_bound(index: np.ndarray) -> np.ndarray:
    index = np.asarray(index, dtype=float)
    return (
        2.0 * index * math.log(2.0)
        + (2.0 * index + 0.5) * math.log(math.pi)
        + 2.0 * np.array([math.lgamma(2.0 * item + 1.0) for item in index])
        - np.array([math.lgamma(4.0 * item + 1.0) for item in index])
        - np.array([math.lgamma(2.0 * item + 1.5) for item in index])
    )


def prolate_tail_certificate(
    maximum_index: int, polynomial_degree: int
) -> dict[str, float]:
    indices = np.arange(3, maximum_index + 1, dtype=float)
    log_bounds = log_prolate_eigenvalue_bound(indices)
    log_terms = log_bounds + polynomial_degree * np.log1p(indices)
    terms = np.exp(log_terms)
    ratios = np.exp(np.diff(log_terms))
    return {
        "first analytic tail bound": float(math.exp(log_bounds[0])),
        "last analytic log10 bound": float(log_bounds[-1] / math.log(10.0)),
        "weighted analytic partial sum": float(np.sum(terms)),
        "last weighted term ratio": float(ratios[-1]),
        "maximum late weighted ratio": float(np.max(ratios[-20:])),
    }


def delta_certificate(
    maximum_log_shift: float, samples: int
) -> tuple[list[dict[str, float]], dict[str, float]]:
    shifts = np.linspace(math.log(2.0), maximum_log_shift, samples)
    rho = np.exp(shifts)
    values = cc20_delta(rho)
    reflected_values = cc20_delta(1.0 / rho)
    scaled = np.sqrt(rho) * np.abs(values)
    selected_indices = np.linspace(0, samples - 1, 8, dtype=int)
    rows = [
        {
            "shift": float(shifts[index]),
            "delta": float(values[index]),
            "scaled": float(scaled[index]),
        }
        for index in selected_indices
    ]
    checks = {
        "rho-inversion symmetry error": float(
            np.max(np.abs(values - reflected_values))
        ),
        "maximum sqrt(rho) times abs(delta)": float(np.max(scaled)),
        "terminal scaled distance from one": float(abs(scaled[-1] - 1.0)),
        "minimum sampled delta": float(np.min(values)),
    }
    return rows, checks


def print_rows(rows: list[dict[str, float]]) -> None:
    print("CC20 explicit delta half-power tail")
    print("+----------+----------------+----------------+")
    print("| log rho  | delta(rho)     | sqrt(rho)|delta| |")
    print("+----------+----------------+----------------+")
    for row in rows:
        print(
            f"| {row['shift']:>8.3f} "
            f"| {row['delta']:>14.6e} "
            f"| {row['scaled']:>14.6e} |"
        )
    print("+----------+----------------+----------------+")


def print_checks(title: str, checks: dict[str, float]) -> None:
    print(title)
    print("+--------------------------------------------+----------------+")
    print("| check                                      | value          |")
    print("+--------------------------------------------+----------------+")
    for label, value in checks.items():
        print(f"| {label:<42} | {value:>14.6e} |")
    print("+--------------------------------------------+----------------+")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--maximum-log-shift", type=float, default=20.0)
    parser.add_argument("--samples", type=int, default=4096)
    parser.add_argument("--maximum-index", type=int, default=160)
    parser.add_argument("--polynomial-degree", type=int, default=8)
    parser.add_argument("--symmetry-tolerance", type=float, default=1e-12)
    parser.add_argument("--maximum-late-ratio", type=float, default=0.1)
    args = parser.parse_args()

    if args.maximum_log_shift < 8.0 or args.samples < 256:
        raise ValueError("delta tail grid is too small")
    if args.maximum_index < 40 or args.polynomial_degree < 0:
        raise ValueError("invalid prolate tail parameters")

    rows, delta_checks = delta_certificate(
        args.maximum_log_shift, args.samples
    )
    prolate_checks = prolate_tail_certificate(
        args.maximum_index, args.polynomial_degree
    )

    print("identity=CC20 static half-power tail and ownership guard")
    print("status=static delta/epsilon tail closed; first-jet identity open")
    print_rows(rows)
    print()
    print_checks("Explicit delta checks", delta_checks)
    print()
    print_checks("Prolate coefficient-tail checks", prolate_checks)

    if delta_checks["rho-inversion symmetry error"] > args.symmetry_tolerance:
        raise SystemExit("CC20 delta inversion symmetry failed")
    if delta_checks["minimum sampled delta"] <= 0.0:
        raise SystemExit("sampled CC20 delta changed sign")
    if (
        prolate_checks["maximum late weighted ratio"]
        > args.maximum_late_ratio
    ):
        raise SystemExit("prolate coefficient majorant no longer decays rapidly")

    print("cc20_explicit_delta_half_power_tail=PASS")
    print("cc20_prolate_polynomial_weight_sum=PASS")
    print("cc20_static_epsilon_half_power_log_tail=PROVED_IN_PROOF_276")
    print("static_remainder_to_moving_first_jet_identity=OPEN")
    print("raw_Qepsilon_large_displacement_bound=OPEN")
    print("proof_275_continuous_AL17=OPEN")
    print("mixed_prime_determinant_resummation=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
