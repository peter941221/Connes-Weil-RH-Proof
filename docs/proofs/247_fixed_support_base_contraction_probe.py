#!/usr/bin/env python3
"""Fixed-support contraction optimization for a Yoshida base factor.

The base is represented in an orthonormal smooth bump-Fourier space on one
fixed log interval.  Its Laplace transform is constrained to equal one at a
synthetic off-critical-line source orbit, while a least-squares stop-band
problem minimizes the transform on the closed critical strip above a chosen
height.

The orbit is a geometry stress test, not an asserted zeta-zero orbit.  Finite
sampling does not prove a uniform strip bound; this script is rejection-first.
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


def spectral_grid(
    height_start: float,
    height_end: float,
    height_count: int,
    sigma_count: int,
    phase_shift: float = 0.0,
) -> np.ndarray:
    if height_count < 2 or sigma_count < 2:
        raise ValueError("spectral grid counts must be at least two")
    logarithms = np.linspace(
        math.log(height_start), math.log(height_end), height_count
    )
    step = logarithms[1] - logarithms[0]
    heights = np.exp(logarithms + phase_shift * step)
    heights = heights[(height_start <= heights) & (heights <= height_end)]
    signed_heights = np.concatenate([-heights[::-1], heights])
    sigmas = np.linspace(0.0, 1.0, sigma_count)
    return (
        sigmas[:, None] + 1j * signed_heights[None, :]
    ).reshape(-1)


def evaluation_matrix(
    spectral_nodes: np.ndarray,
    points: np.ndarray,
    weights: np.ndarray,
    basis: np.ndarray,
) -> np.ndarray:
    return (
        np.exp(np.outer(spectral_nodes, points)) * weights[None, :]
    ) @ basis


def constrained_stopband_solution(
    target_matrix: np.ndarray,
    target_values: np.ndarray,
    stopband_matrix: np.ndarray,
    regularization: float,
) -> tuple[np.ndarray, dict[str, float | int]]:
    left, singular_values, right_h = np.linalg.svd(
        target_matrix, full_matrices=True
    )
    scale = singular_values[0]
    rank = int(np.sum(singular_values > 1e-11 * scale))
    if rank != target_matrix.shape[0]:
        raise RuntimeError("target interpolation matrix is rank deficient")
    particular = np.linalg.lstsq(
        target_matrix, target_values, rcond=1e-12
    )[0]
    nullspace = right_h.conj().T[:, rank:]
    if nullspace.shape[1] == 0:
        coefficients = particular
    else:
        design = stopband_matrix @ nullspace
        right_side = -(stopband_matrix @ particular)
        if regularization > 0.0:
            design = np.vstack(
                [
                    design,
                    math.sqrt(regularization)
                    * np.eye(nullspace.shape[1], dtype=complex),
                ]
            )
            right_side = np.concatenate(
                [right_side, np.zeros(nullspace.shape[1], dtype=complex)]
            )
        correction = np.linalg.lstsq(design, right_side, rcond=1e-12)[0]
        coefficients = particular + nullspace @ correction
    target_residual = float(
        np.linalg.norm(target_matrix @ coefficients - target_values)
    )
    stop_values = stopband_matrix @ coefficients
    return coefficients, {
        "target_rank": rank,
        "target_sigma_min": float(singular_values[-1]),
        "target_residual": target_residual,
        "coefficient_norm": float(np.linalg.norm(coefficients)),
        "train_rms": float(np.linalg.norm(stop_values) / math.sqrt(stop_values.size)),
        "train_sup": float(np.max(np.abs(stop_values))),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--support-length", type=float, default=math.log(2.0))
    parser.add_argument("--frequency-radii", default="12,16,20,24,32,40")
    parser.add_argument("--quadrature-order", type=int, default=384)
    parser.add_argument("--target-real", type=float, default=0.4)
    parser.add_argument("--target-imag", type=float, default=14.134725141734695)
    parser.add_argument("--height-start", type=float, default=30.0)
    parser.add_argument("--height-end", type=float, default=180.0)
    parser.add_argument("--train-heights", type=int, default=96)
    parser.add_argument("--validation-heights", type=int, default=191)
    parser.add_argument("--sigma-count", type=int, default=7)
    parser.add_argument("--regularization", type=float, default=1e-12)
    parser.add_argument("--required-contraction", type=float, default=0.369)
    args = parser.parse_args()

    if args.support_length <= 0.0:
        raise ValueError("support length must be positive")
    radii = parse_integers(args.frequency_radii)
    if not radii or min(radii) < 2:
        raise ValueError("frequency radii must be at least two")
    target = complex(args.target_real, args.target_imag)
    source_orbit = np.asarray(
        [
            target,
            1.0 - target.conjugate(),
            target.conjugate(),
            1.0 - target,
        ],
        dtype=complex,
    )
    target_values = np.ones(source_orbit.size, dtype=complex)
    points, weights = PROOF_245.quadrature_on_symmetric_interval(
        args.support_length, args.quadrature_order
    )
    train_nodes = spectral_grid(
        args.height_start,
        args.height_end,
        args.train_heights,
        args.sigma_count,
    )
    validation_nodes = spectral_grid(
        args.height_start,
        args.height_end,
        args.validation_heights,
        2 * args.sigma_count - 1,
        phase_shift=0.5,
    )

    print("probe=fixed-support Yoshida base contraction")
    print(f"support_length={args.support_length:.12f}")
    print(
        "target_geometry="
        f"synthetic({target.real:+.6f}{target.imag:+.6f}i)"
    )
    print(
        f"stop_band=[{args.height_start:.6f},{args.height_end:.6f}]"
    )
    passed = False
    for radius in radii:
        basis, gram_error = PROOF_245.orthonormal_bump_fourier_basis(
            points, weights, args.support_length, radius
        )
        target_matrix = evaluation_matrix(
            source_orbit, points, weights, basis
        )
        train_matrix = evaluation_matrix(
            train_nodes, points, weights, basis
        )
        coefficients, result = constrained_stopband_solution(
            target_matrix,
            target_values,
            train_matrix,
            args.regularization,
        )
        validation_matrix = evaluation_matrix(
            validation_nodes, points, weights, basis
        )
        validation_values = validation_matrix @ coefficients
        validation_sup = float(np.max(np.abs(validation_values)))
        validation_rms = float(
            np.linalg.norm(validation_values)
            / math.sqrt(validation_values.size)
        )
        passed = passed or validation_sup < args.required_contraction
        print(
            " ".join(
                [
                    f"radius={radius}",
                    f"dimension={basis.shape[1]}",
                    f"gram_error={gram_error:.3e}",
                    f"target_sigma_min={result['target_sigma_min']:.3e}",
                    f"target_residual={result['target_residual']:.3e}",
                    f"coefficient_norm={result['coefficient_norm']:.3e}",
                    f"train_rms={result['train_rms']:.3e}",
                    f"train_sup={result['train_sup']:.3e}",
                    f"validation_rms={validation_rms:.3e}",
                    f"validation_sup={validation_sup:.3e}",
                ]
            )
        )
    print(
        "required_contraction_status="
        + ("SURVIVES_DIAGNOSTIC" if passed else "FAILS_DIAGNOSTIC")
    )
    print("route_status=DIAGNOSTIC_ONLY")


if __name__ == "__main__":
    main()
