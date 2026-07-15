#!/usr/bin/env python3
"""Certificate for Proof 280's Toeplitz semicommutator cocycle.

The script imports Proof 279's Burnol boundary model.  For a projection J and
commuting positive multipliers U,V it checks the detector-first cocycle

    K_J=T_J(UV) T_J(V)^(-1) T_J(U)^(-1).

Its difference from the identity is exactly one completed boundary crossing.
The determinant is also the multiplicative second difference of the Jacobi
complement, and the relative E/R version agrees with the complete Burnol
plus/minus Schur coordinate from Proof 279.
"""

from __future__ import annotations

import argparse
import importlib.util
import math
from pathlib import Path
from types import ModuleType

import numpy as np


def load_proof_279() -> ModuleType:
    path = Path(__file__).with_name(
        "279_burnol_channel_schur_cocycle_probe.py"
    )
    specification = importlib.util.spec_from_file_location(
        "proof_279_for_280", path
    )
    if specification is None or specification.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(specification)
    specification.loader.exec_module(module)
    return module


PROOF_279 = load_proof_279()
PROOF_278 = PROOF_279.PROOF_278


def compression(basis: np.ndarray, matrix: np.ndarray) -> np.ndarray:
    return basis.conj().T @ matrix @ basis


def relative_error(
    actual: complex | np.ndarray, expected: complex | np.ndarray
) -> float:
    actual_array = np.asarray(actual)
    expected_array = np.asarray(expected)
    scale = max(
        float(np.linalg.norm(actual_array)),
        float(np.linalg.norm(expected_array)),
        1.0,
    )
    return float(np.linalg.norm(actual_array - expected_array) / scale)


def toeplitz_cocycle(
    projection: np.ndarray,
    basis: np.ndarray,
    detector_multiplier: np.ndarray,
    generator_multiplier: np.ndarray,
) -> dict[str, np.ndarray | float]:
    identity = np.eye(projection.shape[0], dtype=complex)
    compressed_identity = np.eye(basis.shape[1], dtype=complex)
    product_multiplier = detector_multiplier @ generator_multiplier

    detector_toeplitz = compression(basis, detector_multiplier)
    generator_toeplitz = compression(basis, generator_multiplier)
    product_toeplitz = compression(basis, product_multiplier)
    detector_inverse = np.linalg.inv(detector_toeplitz)
    generator_inverse = np.linalg.inv(generator_toeplitz)

    cocycle = (
        product_toeplitz @ generator_inverse @ detector_inverse
    )
    crossing = (
        basis.conj().T
        @ detector_multiplier
        @ (identity - projection)
        @ generator_multiplier
        @ basis
    )
    crossing_factor = (
        compressed_identity
        + crossing @ generator_inverse @ detector_inverse
    )
    logarithm = (
        PROOF_279.log_positive_determinant(product_toeplitz)
        - PROOF_279.log_positive_determinant(detector_toeplitz)
        - PROOF_279.log_positive_determinant(generator_toeplitz)
    )
    return {
        "detector_toeplitz": detector_toeplitz,
        "generator_toeplitz": generator_toeplitz,
        "product_toeplitz": product_toeplitz,
        "cocycle": cocycle,
        "crossing": crossing,
        "crossing_factor": crossing_factor,
        "log_determinant": logarithm,
    }


def boundary_log_determinant(
    complement_basis: np.ndarray, inverse_multiplier: np.ndarray
) -> float:
    return PROOF_279.log_positive_determinant(
        compression(complement_basis, inverse_multiplier)
    )


def boundary_cross_ratio(
    complement_basis: np.ndarray,
    detector_inverse: np.ndarray,
    generator_inverse: np.ndarray,
    product_inverse: np.ndarray,
) -> float:
    return (
        boundary_log_determinant(complement_basis, product_inverse)
        - boundary_log_determinant(
            complement_basis, detector_inverse
        )
        - boundary_log_determinant(
            complement_basis, generator_inverse
        )
    )


def multiplier_family(
    basis: np.ndarray,
    detector_values: np.ndarray,
    generator_values: np.ndarray,
    detector_parameter: float,
    generator_parameter: float,
) -> dict[str, np.ndarray]:
    detector_multiplier = PROOF_278.multiplier_exponential(
        basis,
        detector_values,
        generator_values,
        detector_parameter,
        0.0,
    )
    generator_multiplier = PROOF_278.multiplier_exponential(
        basis,
        detector_values,
        generator_values,
        0.0,
        generator_parameter,
    )
    product_multiplier = PROOF_278.multiplier_exponential(
        basis,
        detector_values,
        generator_values,
        detector_parameter,
        generator_parameter,
    )
    detector_inverse = PROOF_278.multiplier_exponential(
        basis,
        detector_values,
        generator_values,
        -detector_parameter,
        0.0,
    )
    generator_inverse = PROOF_278.multiplier_exponential(
        basis,
        detector_values,
        generator_values,
        0.0,
        -generator_parameter,
    )
    product_inverse = PROOF_278.multiplier_exponential(
        basis,
        detector_values,
        generator_values,
        -detector_parameter,
        -generator_parameter,
    )
    return {
        "detector": detector_multiplier,
        "generator": generator_multiplier,
        "product": product_multiplier,
        "detector_inverse": detector_inverse,
        "generator_inverse": generator_inverse,
        "product_inverse": product_inverse,
    }


def cocycle_logs(
    model: dict[str, np.ndarray],
    channels: dict[str, np.ndarray],
    multiplier_basis: np.ndarray,
    detector_values: np.ndarray,
    generator_values: np.ndarray,
    detector_parameter: float,
    generator_parameter: float,
) -> dict[str, float]:
    family = multiplier_family(
        multiplier_basis,
        detector_values,
        generator_values,
        detector_parameter,
        generator_parameter,
    )
    outer_basis = PROOF_278.projection_basis(model["outer"])
    sonin_basis = PROOF_278.projection_basis(model["sonin"])

    outer_cocycle = toeplitz_cocycle(
        model["outer"],
        outer_basis,
        family["detector"],
        family["generator"],
    )
    sonin_cocycle = toeplitz_cocycle(
        model["sonin"],
        sonin_basis,
        family["detector"],
        family["generator"],
    )
    outer_log = float(outer_cocycle["log_determinant"])
    sonin_log = float(sonin_cocycle["log_determinant"])

    outer_boundary_cross_ratio = boundary_cross_ratio(
        model["support_basis"],
        family["detector_inverse"],
        family["generator_inverse"],
        family["product_inverse"],
    )
    burnol_boundary_cross_ratio = boundary_cross_ratio(
        channels["boundary_isometry"],
        family["detector_inverse"],
        family["generator_inverse"],
        family["product_inverse"],
    )
    relative_boundary_cross_ratio = (
        outer_boundary_cross_ratio - burnol_boundary_cross_ratio
    )

    relative_coordinates = []
    for inverse_multiplier in (
        family["product_inverse"],
        family["detector_inverse"],
        family["generator_inverse"],
    ):
        relative_coordinates.append(
            PROOF_279.channel_log_determinants(
                channels,
                model["support_basis"],
                inverse_multiplier,
            )
        )
    channel_relative_cross_ratio = (
        relative_coordinates[0]["factorized_relative"]
        - relative_coordinates[1]["factorized_relative"]
        - relative_coordinates[2]["factorized_relative"]
    )

    return {
        "outer": outer_log,
        "sonin": sonin_log,
        "relative": outer_log - sonin_log,
        "outer_boundary": outer_boundary_cross_ratio,
        "burnol_boundary": burnol_boundary_cross_ratio,
        "relative_boundary": relative_boundary_cross_ratio,
        "channel_relative": channel_relative_cross_ratio,
    }


def mixed_derivatives(
    model: dict[str, np.ndarray],
    channels: dict[str, np.ndarray],
    multiplier_basis: np.ndarray,
    detector_values: np.ndarray,
    generator_values: np.ndarray,
    step: float,
) -> dict[str, float]:
    corners: dict[tuple[int, int], dict[str, float]] = {}
    for detector_sign in (-1, 1):
        for generator_sign in (-1, 1):
            corners[(detector_sign, generator_sign)] = cocycle_logs(
                model,
                channels,
                multiplier_basis,
                detector_values,
                generator_values,
                detector_sign * step,
                generator_sign * step,
            )

    derivatives: dict[str, float] = {}
    for label in corners[(1, 1)]:
        derivatives[label] = (
            corners[(1, 1)][label]
            - corners[(1, -1)][label]
            - corners[(-1, 1)][label]
            + corners[(-1, -1)][label]
        ) / (4.0 * step**2)
    return derivatives


def generic_checks(
    size: int,
    support_rank: int,
    seed: int,
    detector_parameter: float,
    generator_parameter: float,
    derivative_step: float,
) -> tuple[dict[str, float], dict[str, float], dict[str, float]]:
    rng = np.random.default_rng(seed)
    model = PROOF_278.build_source_model(size, support_rank, rng)
    detector, generator, basis, detector_values, generator_values = (
        PROOF_278.build_commuting_multipliers(size, rng)
    )
    channels = PROOF_279.channel_data(model)
    family = multiplier_family(
        basis,
        detector_values,
        generator_values,
        detector_parameter,
        generator_parameter,
    )
    outer_basis = PROOF_278.projection_basis(model["outer"])
    sonin_basis = PROOF_278.projection_basis(model["sonin"])
    outer_cocycle = toeplitz_cocycle(
        model["outer"],
        outer_basis,
        family["detector"],
        family["generator"],
    )
    sonin_cocycle = toeplitz_cocycle(
        model["sonin"],
        sonin_basis,
        family["detector"],
        family["generator"],
    )
    logs = cocycle_logs(
        model,
        channels,
        basis,
        detector_values,
        generator_values,
        detector_parameter,
        generator_parameter,
    )

    outer_covariance = PROOF_279.covariance(
        model["outer"], detector, generator
    )
    sonin_covariance = PROOF_279.covariance(
        model["sonin"], detector, generator
    )
    relative_covariance = outer_covariance - sonin_covariance
    derivatives = mixed_derivatives(
        model,
        channels,
        basis,
        detector_values,
        generator_values,
        derivative_step,
    )
    expected_derivatives = {
        "outer": outer_covariance.real,
        "sonin": sonin_covariance.real,
        "relative": relative_covariance.real,
        "outer_boundary": outer_covariance.real,
        "burnol_boundary": sonin_covariance.real,
        "relative_boundary": relative_covariance.real,
        "channel_relative": relative_covariance.real,
    }

    algebra = {
        "multiplier product error": relative_error(
            family["detector"] @ family["generator"],
            family["product"],
        ),
        "outer crossing factorization error": relative_error(
            outer_cocycle["cocycle"],
            outer_cocycle["crossing_factor"],
        ),
        "Sonin crossing factorization error": relative_error(
            sonin_cocycle["cocycle"],
            sonin_cocycle["crossing_factor"],
        ),
        "outer Jacobi cross-ratio error": float(
            abs(logs["outer"] - logs["outer_boundary"])
        ),
        "Sonin Jacobi cross-ratio error": float(
            abs(logs["sonin"] - logs["burnol_boundary"])
        ),
        "relative boundary cross-ratio error": float(
            abs(logs["relative"] - logs["relative_boundary"])
        ),
        "channel Schur cross-ratio error": float(
            abs(logs["relative"] - logs["channel_relative"])
        ),
    }
    derivative_errors = {
        f"{label} mixed derivative error": float(
            abs(derivatives[label] - expected)
        )
        for label, expected in expected_derivatives.items()
    }
    diagnostics = {
        "outer cocycle displacement norm": float(
            np.linalg.norm(
                outer_cocycle["cocycle"]
                - np.eye(outer_basis.shape[1], dtype=complex),
                ord=2,
            )
        ),
        "Sonin cocycle displacement norm": float(
            np.linalg.norm(
                sonin_cocycle["cocycle"]
                - np.eye(sonin_basis.shape[1], dtype=complex),
                ord=2,
            )
        ),
        "relative cocycle log magnitude": float(abs(logs["relative"])),
        "relative covariance magnitude": float(abs(relative_covariance)),
    }
    return algebra, derivative_errors, diagnostics


def zero_prolate_guard(
    detector_parameter: float,
    generator_parameter: float,
    derivative_step: float,
) -> dict[str, float]:
    transform = np.array(
        [[0.0, 1.0, 0.0], [1.0, 0.0, 0.0], [0.0, 0.0, 1.0]],
        dtype=complex,
    )
    model = PROOF_278.assemble_source_model(transform, support_rank=1)
    channels = PROOF_279.channel_data(model)
    vector = np.array([0.0, 1.0, 1.0], dtype=complex) / math.sqrt(2.0)
    detector = np.outer(vector, vector.conj())
    generator = detector.copy()
    eigenvalues, eigenvectors = np.linalg.eigh(detector)

    logs = cocycle_logs(
        model,
        channels,
        eigenvectors,
        eigenvalues,
        eigenvalues,
        detector_parameter,
        generator_parameter,
    )
    derivatives = mixed_derivatives(
        model,
        channels,
        eigenvectors,
        eigenvalues,
        eigenvalues,
        derivative_step,
    )
    outer_covariance = PROOF_279.covariance(
        model["outer"], detector, generator
    ).real
    sonin_covariance = PROOF_279.covariance(
        model["sonin"], detector, generator
    ).real
    relative_covariance = outer_covariance - sonin_covariance

    return {
        "truncated Fourier norm": float(
            np.linalg.norm(model["truncated_transform"], ord=2)
        ),
        "prolate correction norm": float(
            np.linalg.norm(model["prolate"], ord=2)
        ),
        "outer covariance": float(outer_covariance),
        "Sonin covariance": float(sonin_covariance),
        "relative covariance": float(relative_covariance),
        "relative cocycle log magnitude": float(abs(logs["relative"])),
        "relative boundary error": float(
            abs(logs["relative"] - logs["relative_boundary"])
        ),
        "relative channel error": float(
            abs(logs["relative"] - logs["channel_relative"])
        ),
        "relative derivative error": float(
            abs(derivatives["relative"] - relative_covariance)
        ),
        "relative target error": float(
            abs(relative_covariance + 1.0 / 4.0)
        ),
    }


def print_checks(title: str, checks: dict[str, float]) -> None:
    width = max(len(label) for label in checks)
    border = f"+-{'-' * width}-+----------------+"
    print(title)
    print(border)
    print(f"| {'check':<{width}} | value          |")
    print(border)
    for label, value in checks.items():
        print(f"| {label:<{width}} | {value:>14.6e} |")
    print(border)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--size", type=int, default=28)
    parser.add_argument("--support-rank", type=int, default=7)
    parser.add_argument("--seed", type=int, default=1280)
    parser.add_argument("--detector-parameter", type=float, default=0.16)
    parser.add_argument("--generator-parameter", type=float, default=-0.11)
    parser.add_argument("--derivative-step", type=float, default=7e-4)
    parser.add_argument("--algebra-tolerance", type=float, default=2e-10)
    parser.add_argument("--derivative-tolerance", type=float, default=2e-6)
    args = parser.parse_args()

    if args.size < 8:
        raise ValueError("size must be at least eight")
    if args.support_rank < 1 or 2 * args.support_rank >= args.size:
        raise ValueError("support-rank must satisfy 1 <= 2 rank < size")

    algebra, derivative_errors, diagnostics = generic_checks(
        args.size,
        args.support_rank,
        args.seed,
        args.detector_parameter,
        args.generator_parameter,
        args.derivative_step,
    )
    guard = zero_prolate_guard(
        args.detector_parameter,
        args.generator_parameter,
        args.derivative_step,
    )

    print("identity=Toeplitz semicommutator Fredholm cocycle")
    print("status=fixed-S determinant domain exact; uniform bound open")
    print_checks("Cocycle and boundary algebra", algebra)
    print()
    print_checks("Mixed derivative readback", derivative_errors)
    print()
    print_checks("Generic diagnostics", diagnostics)
    print()
    print_checks("Deterministic zero-prolate guard", guard)

    algebra_error = max(algebra.values())
    derivative_error = max(derivative_errors.values())
    guard_error = max(
        guard["relative boundary error"],
        guard["relative channel error"],
        guard["relative derivative error"],
        guard["relative target error"],
    )
    print(f"maximum algebra error={algebra_error:.12e}")
    print(f"maximum mixed derivative error={derivative_error:.12e}")
    print(f"maximum zero-prolate guard error={guard_error:.12e}")

    if algebra_error > args.algebra_tolerance:
        raise SystemExit(
            f"semicommutator cocycle algebra failed: {algebra_error:.6e}"
        )
    if derivative_error > args.derivative_tolerance:
        raise SystemExit(
            f"semicommutator derivative failed: {derivative_error:.6e}"
        )
    if guard_error > args.derivative_tolerance:
        raise SystemExit(
            f"zero-prolate cocycle guard failed: {guard_error:.6e}"
        )

    print("detector_first_crossing_factorization=EXACT")
    print("fixed_s_semicommutator_fredholm_domain=EXACT")
    print("relative_burnol_multiplicative_cross_ratio=EXACT")
    print("channel_schur_cross_ratio=EXACT")
    print("mixed_toeplitz_covariance_readback=EXACT")
    print("ambient_determinant_required=FALSE")
    print("uniform_polynomial_support_bound=OPEN")
    print("determinant_resummed_prime_telescope=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
