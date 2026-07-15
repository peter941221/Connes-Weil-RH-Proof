#!/usr/bin/env python3
"""Global critical-line contraction with exact centered-orbit normalization.

Let ``u = delta + i gamma`` be a synthetic centered off-critical point.  A
compact smooth seed has transform one at ``{+/-delta +/- i gamma}``.  Translate
the seed by ``+/-ell`` and normalize by ``cosh(ell * delta)``, with
``ell * gamma`` an integer multiple of ``2*pi``.  The resulting transform is

    Seed(v) * cosh(ell * v) / cosh(ell * delta).

It remains one on the complete centered orbit, while its entire critical-line
supremum has the rigorous elementary bound

    ||seed||_1 / cosh(ell * |delta|).

The probe checks the finite interpolation and reports the support cost of a
chosen strict contraction.  It does not prove a finite-S trace estimate.
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


def centered_orbit(target: complex) -> np.ndarray:
    delta = target.real - 0.5
    gamma = target.imag
    return np.asarray(
        [
            delta + 1j * gamma,
            -delta + 1j * gamma,
            delta - 1j * gamma,
            -delta - 1j * gamma,
        ],
        dtype=complex,
    )


def evaluation_matrix(
    nodes: np.ndarray,
    points: np.ndarray,
    weights: np.ndarray,
    basis: np.ndarray,
) -> np.ndarray:
    return (
        np.exp(np.outer(nodes, points)) * weights[None, :]
    ) @ basis


def choose_resonant_shift(
    delta: float,
    gamma: float,
    seed_l1_bound: float,
    required_contraction: float,
    safety_factor: float,
) -> tuple[float, int]:
    needed_cosh = safety_factor * seed_l1_bound / required_contraction
    needed_cosh = max(needed_cosh, 1.0 + np.finfo(float).eps)
    needed_product = math.acosh(needed_cosh)
    if gamma == 0.0:
        return needed_product / abs(delta), 0
    resonance = math.ceil(
        needed_product * abs(gamma) / (2.0 * math.pi * abs(delta))
    )
    shift = 2.0 * math.pi * resonance / abs(gamma)
    return shift, resonance


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--target-real", type=float, default=0.4)
    parser.add_argument("--target-imag", type=float, default=14.134725141734695)
    parser.add_argument("--seed-support", type=float, default=math.log(2.0))
    parser.add_argument("--seed-frequency-radius", type=int, default=8)
    parser.add_argument("--quadrature-order", type=int, default=512)
    parser.add_argument("--required-contraction", type=float, default=0.5)
    parser.add_argument("--safety-factor", type=float, default=1.05)
    parser.add_argument("--validation-height", type=float, default=250.0)
    parser.add_argument("--validation-points", type=int, default=20001)
    args = parser.parse_args()

    target = complex(args.target_real, args.target_imag)
    delta = target.real - 0.5
    gamma = target.imag
    if delta == 0.0:
        raise ValueError("the target must be off the critical line")
    if args.seed_support <= 0.0:
        raise ValueError("seed support must be positive")
    if not 0.0 < args.required_contraction < 1.0:
        raise ValueError("required contraction must lie in (0,1)")
    if args.safety_factor <= 1.0:
        raise ValueError("safety factor must exceed one")

    orbit = centered_orbit(target)
    points, weights = PROOF_245.quadrature_on_symmetric_interval(
        args.seed_support, args.quadrature_order
    )
    basis, gram_error = PROOF_245.orthonormal_bump_fourier_basis(
        points,
        weights,
        args.seed_support,
        args.seed_frequency_radius,
    )
    interpolation = evaluation_matrix(orbit, points, weights, basis)
    singular_values = np.linalg.svd(interpolation, compute_uv=False)
    coefficients = np.linalg.lstsq(
        interpolation, np.ones(orbit.size, dtype=complex), rcond=1e-13
    )[0]
    seed_values = basis @ coefficients
    seed_residual = float(
        np.linalg.norm(interpolation @ coefficients - np.ones(orbit.size))
    )
    seed_l1_bound = float(np.sum(weights * np.abs(seed_values)))

    shift, resonance = choose_resonant_shift(
        delta,
        gamma,
        seed_l1_bound,
        args.required_contraction,
        args.safety_factor,
    )
    denominator = math.cosh(shift * abs(delta))
    analytic_contraction = seed_l1_bound / denominator
    support_span = args.seed_support + 2.0 * shift
    contraction_rate = -math.log(analytic_contraction) / support_span

    heights = np.linspace(
        -args.validation_height,
        args.validation_height,
        args.validation_points,
    )
    critical_nodes = 1j * heights
    seed_transform = evaluation_matrix(
        critical_nodes, points, weights, basis
    ) @ coefficients
    critical_values = (
        seed_transform * np.cos(shift * heights) / denominator
    )
    sampled_contraction = float(np.max(np.abs(critical_values)))

    orbit_seed = interpolation @ coefficients
    if gamma == 0.0:
        orbit_cosh_ratio = np.cosh(shift * orbit) / denominator
    else:
        # Evaluate the exact resonance identity without large-angle reduction.
        orbit_cosh_ratio = np.ones(orbit.size, dtype=complex)
    orbit_values = orbit_seed * orbit_cosh_ratio
    orbit_residual = float(np.linalg.norm(orbit_values - 1.0))

    print("probe=global critical-line contraction")
    print(
        "target_geometry="
        f"synthetic({target.real:+.9f}{target.imag:+.9f}i)"
    )
    print(f"centered_distance={abs(delta):.12e}")
    print(f"seed_support={args.seed_support:.12f}")
    print(f"seed_dimension={basis.shape[1]}")
    print(f"seed_gram_error={gram_error:.3e}")
    print(f"seed_sigma_min={singular_values[-1]:.3e}")
    print(f"seed_interpolation_residual={seed_residual:.3e}")
    print(f"seed_l1_bound={seed_l1_bound:.12e}")
    print(f"resonance_index={resonance}")
    print(f"resonant_shift={shift:.12e}")
    print(f"support_span={support_span:.12e}")
    print(f"analytic_critical_contraction={analytic_contraction:.12e}")
    print(f"sampled_critical_contraction={sampled_contraction:.12e}")
    print(f"contraction_per_support_rate={contraction_rate:.12e}")
    print(f"orbit_residual={orbit_residual:.3e}")
    passed = (
        analytic_contraction < args.required_contraction
        and sampled_contraction <= analytic_contraction * (1.0 + 1e-10)
        and orbit_residual < 1e-10
    )
    print(
        "global_contraction_status="
        + ("SURVIVES_DIAGNOSTIC" if passed else "FAILS_DIAGNOSTIC")
    )
    print("route_status=DIAGNOSTIC_ONLY")


if __name__ == "__main__":
    main()
