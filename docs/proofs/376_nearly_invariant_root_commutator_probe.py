"""Finite certificate for Proof 376's nearly-invariant commutator bound."""

from __future__ import annotations

import argparse
import math

import numpy as np


def transported_frame(
    ambient_size: int,
    offset: int,
    model_dimension: int,
) -> np.ndarray:
    multiplier = np.array([1.0 + 0.0j])
    for prime, delay in [(2, 1), (3, 2), (5, 3), (7, 5), (11, 7)]:
        factor = np.zeros(delay + 1, dtype=complex)
        factor[0] = 1.0
        factor[delay] = -(prime**-0.5)
        multiplier = np.convolve(multiplier, factor)

    frame = np.zeros((ambient_size, model_dimension), dtype=complex)
    for column in range(model_dimension):
        start = offset + column
        frame[start : start + len(multiplier), column] = multiplier
    return frame


def bilateral_shift(size: int) -> np.ndarray:
    shift = np.zeros((size, size), dtype=complex)
    for column in range(size - 1):
        shift[column + 1, column] = 1.0
    return shift


def matrix_power(shift: np.ndarray, exponent: int) -> np.ndarray:
    if exponent >= 0:
        return np.linalg.matrix_power(shift, exponent)
    return np.linalg.matrix_power(shift.conj().T, -exponent)


def numerical_rank(matrix: np.ndarray, tolerance: float) -> int:
    singular_values = np.linalg.svd(matrix, compute_uv=False)
    return int(np.sum(singular_values > tolerance))


def certificate(
    ambient_size: int,
    offset: int,
    model_dimension: int,
    maximum_power: int,
    seed: int,
) -> dict[str, float]:
    frame = transported_frame(ambient_size, offset, model_dimension)
    orthonormal, _ = np.linalg.qr(frame, mode="reduced")
    projection = orthonormal @ orthonormal.conj().T
    shift = bilateral_shift(ambient_size)

    maximum_rank_excess = 0
    maximum_power_norm_excess = 0.0
    for exponent in range(-maximum_power, maximum_power + 1):
        if exponent == 0:
            continue
        unitary_power = matrix_power(shift, exponent)
        commutator = unitary_power @ projection - projection @ unitary_power
        rank = numerical_rank(commutator, 2e-9)
        maximum_rank_excess = max(
            maximum_rank_excess,
            rank - 2 * abs(exponent),
        )
        maximum_power_norm_excess = max(
            maximum_power_norm_excess,
            float(np.linalg.norm(commutator, 2)) - 1.0,
        )

    rng = np.random.default_rng(seed)
    coefficients: dict[int, complex] = {}
    for exponent in range(-maximum_power, maximum_power + 1):
        if exponent != 0:
            scale = (1.0 + abs(exponent)) ** -2.5
            coefficients[exponent] = scale * (
                rng.normal() + 1j * rng.normal()
            )

    multiplier = np.zeros_like(shift)
    coefficient_budget = 0.0
    for exponent, coefficient in coefficients.items():
        multiplier += coefficient * matrix_power(shift, exponent)
        coefficient_budget += math.sqrt(abs(exponent)) * abs(coefficient)

    commutator = multiplier @ projection - projection @ multiplier
    commutator_hs = float(np.linalg.norm(commutator, "fro"))
    predicted_bound = math.sqrt(2.0) * coefficient_budget

    return {
        "maximum rank excess": float(maximum_rank_excess),
        "maximum power norm excess": max(0.0, maximum_power_norm_excess),
        "smooth commutator Hilbert Schmidt norm": commutator_hs,
        "coefficient bound": predicted_bound,
        "smooth bound violation": max(0.0, commutator_hs - predicted_bound),
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--ambient-size", type=int, default=180)
    parser.add_argument("--offset", type=int, default=45)
    parser.add_argument("--model-dimension", type=int, default=12)
    parser.add_argument("--maximum-power", type=int, default=8)
    parser.add_argument("--seed", type=int, default=376)
    parser.add_argument("--tolerance", type=float, default=3e-9)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    checks = certificate(
        args.ambient_size,
        args.offset,
        args.model_dimension,
        args.maximum_power,
        args.seed,
    )
    print("Proof 376 nearly-invariant root commutator certificate")
    for label, value in checks.items():
        print(f"{label.replace(' ', '_')}={value:.12e}")

    maximum_error = max(
        checks["maximum rank excess"],
        checks["maximum power norm excess"],
        checks["smooth bound violation"],
    )
    if maximum_error > args.tolerance:
        raise RuntimeError(f"nearly-invariant commutator failed: {maximum_error:.3e}")

    print(f"maximum_error_or_violation={maximum_error:.12e}")
    print("cayley_power_rank_bound=PASS")
    print("smooth_multiplier_s2_bound=PASS")
    print("euler_condition_number=ABSENT")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
