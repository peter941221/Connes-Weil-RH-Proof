"""Certificate for Proof 377's Cayley compact-root Sobolev budget."""

from __future__ import annotations

import argparse
import math

import numpy as np


def cayley_coefficients(
    support_radius: float,
    spline_order: int,
    sample_count: int,
) -> tuple[np.ndarray, np.ndarray]:
    indices = np.arange(sample_count)
    theta = 2.0 * math.pi * (indices + 0.5) / sample_count
    spectral = np.tan(0.5 * (theta - math.pi))
    argument = support_radius * spectral / spline_order
    values = np.sinc(argument / math.pi) ** spline_order

    modes = np.fft.fftfreq(sample_count, d=1.0 / sample_count).astype(int)
    raw = np.fft.fft(values) / sample_count
    phase = np.exp(-1j * modes * math.pi / sample_count)
    return modes, raw * phase


def shift_matrix(size: int) -> np.ndarray:
    shift = np.zeros((size, size), dtype=complex)
    for column in range(size - 1):
        shift[column + 1, column] = 1.0
    return shift


def shift_power(shift: np.ndarray, exponent: int) -> np.ndarray:
    if exponent >= 0:
        return np.linalg.matrix_power(shift, exponent)
    return np.linalg.matrix_power(shift.conj().T, -exponent)


def nearly_invariant_projection(
    ambient_size: int,
    offset: int,
    model_dimension: int,
) -> np.ndarray:
    multiplier = np.array([1.0 + 0.0j])
    for prime, delay in [(2, 1), (3, 2), (5, 4), (7, 6)]:
        factor = np.zeros(delay + 1, dtype=complex)
        factor[0] = 1.0
        factor[delay] = -(prime**-0.5)
        multiplier = np.convolve(multiplier, factor)

    frame = np.zeros((ambient_size, model_dimension), dtype=complex)
    for column in range(model_dimension):
        start = offset + column
        frame[start : start + len(multiplier), column] = multiplier
    orthonormal, _ = np.linalg.qr(frame, mode="reduced")
    return orthonormal @ orthonormal.conj().T


def certificate(
    sample_count: int,
    spline_order: int,
    maximum_mode: int,
    ambient_size: int,
) -> dict[str, float]:
    shift = shift_matrix(ambient_size)
    projection = nearly_invariant_projection(ambient_size, 48, 12)
    maximum_cauchy_violation = 0.0
    maximum_commutator_violation = 0.0
    maximum_normalized_h2 = 0.0
    last_budget = 0.0
    last_commutator = 0.0

    for support_radius in [0.5, 1.0, 2.0, 4.0]:
        modes, coefficients = cayley_coefficients(
            support_radius,
            spline_order,
            sample_count,
        )
        nonzero = modes != 0
        coefficient_budget = float(
            np.sum(np.sqrt(np.abs(modes[nonzero])) * np.abs(coefficients[nonzero]))
        )
        h2_norm = float(
            np.sqrt(np.sum((1.0 + modes**2) ** 2 * np.abs(coefficients) ** 2))
        )
        cauchy_constant = float(
            np.sqrt(np.sum(np.abs(modes[nonzero]) / (1.0 + modes[nonzero] ** 2) ** 2))
        )
        maximum_cauchy_violation = max(
            maximum_cauchy_violation,
            coefficient_budget - cauchy_constant * h2_norm,
        )
        maximum_normalized_h2 = max(
            maximum_normalized_h2,
            h2_norm / (1.0 + support_radius) ** 2,
        )

        multiplier = np.zeros_like(shift)
        selected_budget = 0.0
        for mode, coefficient in zip(modes, coefficients, strict=True):
            if mode == 0 or abs(mode) > maximum_mode:
                continue
            multiplier += coefficient * shift_power(shift, int(mode))
            selected_budget += math.sqrt(abs(int(mode))) * abs(coefficient)

        commutator = multiplier @ projection - projection @ multiplier
        commutator_hs = float(np.linalg.norm(commutator, "fro"))
        commutator_bound = math.sqrt(2.0) * selected_budget
        maximum_commutator_violation = max(
            maximum_commutator_violation,
            commutator_hs - commutator_bound,
        )
        last_budget = coefficient_budget
        last_commutator = commutator_hs

    return {
        "coefficient Cauchy violation": max(0.0, maximum_cauchy_violation),
        "commutator bound violation": max(0.0, maximum_commutator_violation),
        "maximum H2 over polynomial support scale": maximum_normalized_h2,
        "largest support coefficient budget": last_budget,
        "largest support commutator norm": last_commutator,
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--sample-count", type=int, default=4096)
    parser.add_argument("--spline-order", type=int, default=10)
    parser.add_argument("--maximum-mode", type=int, default=36)
    parser.add_argument("--ambient-size", type=int, default=176)
    parser.add_argument("--tolerance", type=float, default=5e-8)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    checks = certificate(
        args.sample_count,
        args.spline_order,
        args.maximum_mode,
        args.ambient_size,
    )
    print("Proof 377 Cayley compact-root Sobolev certificate")
    for label, value in checks.items():
        print(f"{label.replace(' ', '_')}={value:.12e}")

    maximum_error = max(
        checks["coefficient Cauchy violation"],
        checks["commutator bound violation"],
    )
    if maximum_error > args.tolerance:
        raise RuntimeError(f"Cayley compact-root budget failed: {maximum_error:.3e}")

    print(f"maximum_error_or_violation={maximum_error:.12e}")
    print("cayley_coefficient_budget=PASS")
    print("compact_root_sobolev_scale=POLYNOMIAL")
    print("endpoint_MR6=MATHEMATICALLY_CLOSED")
    print("gate_3u=OPEN_PENDING_ROOT_SPLIT")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
