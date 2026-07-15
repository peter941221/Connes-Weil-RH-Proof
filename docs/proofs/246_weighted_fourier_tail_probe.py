#!/usr/bin/env python3
"""Detector-specific weighted Fourier leakage screen for the CC20 remainder.

Exact vanishing is imposed only below a fixed vertical threshold.  Above that
threshold the pre-root Fourier coefficients are bounded by a cubic envelope,
as suggested by a quadratic Yoshida source tail divided by the Q-root factor
`1/2-s`.  The script bounds leakage into every numerically resolved positive
eigenspace of `K_infinity - 2 Id`.

This is a numerical decision screen for the ordinary CC20 kernel.  It does not
include the finite-S metric correction and does not certify the continuum
spectral truncation.
"""

from __future__ import annotations

import argparse
import importlib.util
import math
from pathlib import Path

import numpy as np


def load_proof_245():
    path = Path(__file__).with_name("245_quantitative_fourier_control_probe.py")
    spec = importlib.util.spec_from_file_location("proof_245", path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path.name}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


PROOF_245 = load_proof_245()


def parse_integers(raw: str) -> list[int]:
    return [int(value.strip()) for value in raw.split(",") if value.strip()]


def expm1_over(value: complex, length: float) -> complex:
    if abs(value) < 1e-12:
        return complex(length)
    return np.expm1(value * length) / value


def fourier_sine_coefficients(
    length: float, mode_count: int, frequency_indices: np.ndarray
) -> np.ndarray:
    """Return `<e_k, phi_n>` for the periodic Fourier and Dirichlet bases."""
    result = np.empty((frequency_indices.size, mode_count), dtype=complex)
    for row, frequency_index in enumerate(frequency_indices):
        spectral = -2j * math.pi * frequency_index / length
        phase = -1.0 if int(frequency_index) % 2 else 1.0
        for column in range(mode_count):
            mode = column + 1
            angular = mode * math.pi / length
            integral = (
                expm1_over(spectral + 1j * angular, length)
                - expm1_over(spectral - 1j * angular, length)
            ) / (2j)
            result[row, column] = phase * math.sqrt(2.0) * integral / length
    return result


def envelope_tail_l2_bound(
    length: float, maximum_frequency_index: int, power: float
) -> float:
    if power <= 0.5:
        raise ValueError("power must exceed one half")
    index = float(maximum_frequency_index)
    zeta_tail_bound = index ** (-2.0 * power) + (
        index ** (1.0 - 2.0 * power) / (2.0 * power - 1.0)
    )
    scale = (length / (2.0 * math.pi)) ** power
    return math.sqrt(2.0 * scale**2 * zeta_tail_bound)


def weighted_bad_space_leakage(
    compact: np.ndarray,
    length: float,
    vertical_threshold: float,
    envelope_power: float,
    maximum_frequency_index: int,
) -> dict[str, float | int]:
    eigenvalues, eigenvectors = np.linalg.eigh(compact)
    selected = eigenvalues > 2.0
    bad_values = eigenvalues[selected] - 2.0
    bad_vectors = eigenvectors[:, selected]
    if bad_values.size == 0:
        return {
            "bad_dimension": 0,
            "low_radius": 0,
            "leakage_constant": 0.0,
            "maximum_bad_bound": 0.0,
            "minimum_fourier_capture": 1.0,
            "tail_envelope_l2": 0.0,
        }

    low_radius = math.ceil(vertical_threshold * length / (2.0 * math.pi))
    if maximum_frequency_index <= low_radius:
        raise ValueError("maximum Fourier index must exceed the low radius")
    frequency_indices = np.arange(
        -maximum_frequency_index, maximum_frequency_index + 1, dtype=int
    )
    transform = fourier_sine_coefficients(
        length, compact.shape[0], frequency_indices
    )
    bad_fourier = transform @ bad_vectors
    fourier_energy = np.sum(np.abs(bad_fourier) ** 2, axis=0)
    missing_energy = np.sqrt(np.maximum(0.0, 1.0 - fourier_energy))

    angular_frequencies = (
        2.0 * math.pi * np.abs(frequency_indices.astype(float)) / length
    )
    envelope = np.zeros_like(angular_frequencies)
    high = np.abs(frequency_indices) > low_radius
    envelope[high] = angular_frequencies[high] ** (-envelope_power)
    finite_bounds = np.sum(np.abs(bad_fourier) * envelope[:, None], axis=0)
    tail_envelope = envelope_tail_l2_bound(
        length, maximum_frequency_index, envelope_power
    )
    complete_bounds = finite_bounds + missing_energy * tail_envelope
    leakage = float(np.sum(bad_values * complete_bounds**2))
    return {
        "bad_dimension": int(bad_values.size),
        "low_radius": low_radius,
        "leakage_constant": leakage,
        "maximum_bad_bound": float(np.max(complete_bounds)),
        "minimum_fourier_capture": float(np.min(fourier_energy)),
        "tail_envelope_l2": tail_envelope,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--master-indices", default="1,2,3,4,5,6")
    parser.add_argument("--modes", default="64,96,128")
    parser.add_argument("--cell-length", type=float, default=math.log(2.0))
    parser.add_argument("--quadrature-order", type=int, default=384)
    parser.add_argument("--vertical-threshold", type=float, default=30.0)
    parser.add_argument("--envelope-power", type=float, default=3.0)
    parser.add_argument("--maximum-frequency-index", type=int, default=512)
    parser.add_argument("--contraction", type=float, default=0.5)
    parser.add_argument("--target-real", type=float, default=0.4)
    parser.add_argument("--target-imag", type=float, default=14.134725141734695)
    parser.add_argument("--correction-extra-modes", type=int, default=16)
    parser.add_argument("--tail-end", type=float, default=120.0)
    parser.add_argument("--tail-samples", type=int, default=64)
    parser.add_argument("--skip-interpolation", action="store_true")
    args = parser.parse_args()

    master_indices = parse_integers(args.master_indices)
    mode_counts = parse_integers(args.modes)
    if not master_indices or min(master_indices) < 1:
        raise ValueError("master indices must be positive")
    if not mode_counts or min(mode_counts) < 4:
        raise ValueError("mode counts must be at least four")
    if args.quadrature_order <= max(mode_counts):
        raise ValueError("quadrature order must exceed the largest mode count")
    if not 0.0 < args.contraction < 1.0:
        raise ValueError("contraction must lie in (0,1)")

    print("probe=detector-specific weighted Fourier leakage")
    print("owner=ordinary continuous CC20 compact kernel")
    print("finite_S_correction=NOT_INCLUDED")
    print(
        f"tail_model=abs(xi_hat(t))<=epsilon*abs(t)^(-{args.envelope_power:g})"
    )
    print(f"exact_low_height={args.vertical_threshold:.9f}")
    print(f"contraction={args.contraction:.9f}")
    maximum_modes = max(mode_counts)
    weighted_leakages: list[tuple[int, float]] = []
    combined_leakages: list[tuple[int, float]] = []
    every_interpolation_valid = True
    target = complex(args.target_real, args.target_imag)

    for master_index in master_indices:
        length = master_index * args.cell_length
        compact, _points, _weights, _basis = PROOF_245.ordinary_cc20_galerkin(
            length, maximum_modes, args.quadrature_order
        )
        largest_result: dict[str, float | int] | None = None
        for mode_count in mode_counts:
            mode_compact = compact[:mode_count, :mode_count]
            result = weighted_bad_space_leakage(
                mode_compact,
                length,
                args.vertical_threshold,
                args.envelope_power,
                args.maximum_frequency_index,
            )
            base_only_weighted = (
                args.contraction ** (2 * (master_index + 1))
                * float(result["leakage_constant"])
            )
            print(
                " ".join(
                    [
                        f"N={master_index}",
                        f"length={length:.9f}",
                        f"modes={mode_count}",
                        f"bad_dim={result['bad_dimension']}",
                        f"low_radius={result['low_radius']}",
                        f"fourier_capture={result['minimum_fourier_capture']:.9f}",
                        f"tail_l2={result['tail_envelope_l2']:.3e}",
                        f"max_bad_bound={result['maximum_bad_bound']:.3e}",
                        f"leakage_constant={result['leakage_constant']:.3e}",
                        f"base_only_q2_leakage={base_only_weighted:.3e}",
                    ]
                )
            )
            if mode_count == maximum_modes:
                largest_result = result
                weighted_leakages.append((master_index, base_only_weighted))
        if largest_result is None:
            raise RuntimeError("largest leakage result is missing")
        if args.skip_interpolation:
            print(f"coupled_N={master_index} interpolation=SKIPPED")
            continue

        low_radius = int(largest_result["low_radius"])
        interpolation = PROOF_245.correction_interpolation_probe(
            length,
            master_index,
            PROOF_245.control_nodes(length, low_radius),
            target,
            args.quadrature_order,
            args.correction_extra_modes,
            args.vertical_threshold,
            args.tail_end,
            args.tail_samples,
            args.contraction,
        )
        interpolation_valid = bool(interpolation["full_row_rank"])
        every_interpolation_valid = (
            every_interpolation_valid and interpolation_valid
        )
        assembled_tail = (
            args.contraction ** (master_index + 1)
            * float(interpolation["tail_proxy"])
            if interpolation_valid
            else math.inf
        )
        combined_leakage = (
            assembled_tail**2 * float(largest_result["leakage_constant"])
        )
        combined_leakages.append((master_index, combined_leakage))
        print(
            " ".join(
                [
                    f"coupled_N={master_index}",
                    f"constraints={interpolation['constraint_count']}",
                    f"interpolation_rank={interpolation['interpolation_rank']}",
                    f"full_row_rank={str(interpolation_valid).lower()}",
                    f"correction_dim={interpolation['correction_dimension']}",
                    f"right_inverse={interpolation['right_inverse_norm']:.3e}",
                    f"solution_norm={interpolation['solution_norm']:.3e}",
                    f"correction_tail={interpolation['tail_proxy']:.3e}",
                    f"assembled_tail={assembled_tail:.3e}",
                    f"combined_leakage={combined_leakage:.3e}",
                ]
            )
        )

    if len(weighted_leakages) >= 3:
        tail = weighted_leakages[len(weighted_leakages) // 2 :]
        indices = np.asarray([item[0] for item in tail], dtype=float)
        values = np.asarray(
            [max(item[1], np.finfo(float).tiny) for item in tail], dtype=float
        )
        slope = float(np.polyfit(indices, np.log(values), 1)[0])
        print(f"weighted_leakage_log_slope={slope:+.9f}")
        print(
            "weighted_leakage_status="
            + ("FAVORABLE_DIAGNOSTIC" if slope < 0.0 else "UNFAVORABLE_DIAGNOSTIC")
        )
    if len(combined_leakages) >= 3:
        tail = combined_leakages[len(combined_leakages) // 2 :]
        indices = np.asarray([item[0] for item in tail], dtype=float)
        values = np.asarray(
            [max(item[1], np.finfo(float).tiny) for item in tail], dtype=float
        )
        slope = float(np.polyfit(indices, np.log(values), 1)[0])
        print(f"combined_leakage_log_slope={slope:+.9f}")
        if not every_interpolation_valid:
            combined_status = "RANK_DEFICIENT_INTERPOLATION_DIAGNOSTIC"
        elif slope < 0.0:
            combined_status = "FAVORABLE_DIAGNOSTIC"
        else:
            combined_status = "UNFAVORABLE_DIAGNOSTIC"
        print(f"combined_leakage_status={combined_status}")
    print("route_status=DIAGNOSTIC_ONLY")


if __name__ == "__main__":
    main()
