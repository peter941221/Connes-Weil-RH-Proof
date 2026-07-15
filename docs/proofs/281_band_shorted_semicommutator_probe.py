#!/usr/bin/env python3
"""Certificate for Proof 281's band-shorted semicommutator.

The script imports Proof 280's source model.  It shorts each positive
multiplier from E=R direct-sum B onto the common band B and checks that the
determinant of the resulting semicommutator is the relative E/R Toeplitz
cocycle.  Its mixed derivative is the signed pair of physical band crossings.
"""

from __future__ import annotations

import argparse
import importlib.util
import math
from pathlib import Path
from types import ModuleType

import numpy as np


def load_proof_280() -> ModuleType:
    path = Path(__file__).with_name(
        "280_toeplitz_semicommutator_cocycle_probe.py"
    )
    specification = importlib.util.spec_from_file_location(
        "proof_280_for_281", path
    )
    if specification is None or specification.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(specification)
    specification.loader.exec_module(module)
    return module


PROOF_280 = load_proof_280()
PROOF_279 = PROOF_280.PROOF_279
PROOF_278 = PROOF_280.PROOF_278


def shorted_band(
    model: dict[str, np.ndarray], matrix: np.ndarray
) -> dict[str, np.ndarray]:
    sonin_basis = PROOF_278.projection_basis(model["sonin"])
    band_projection = model["outer"] - model["sonin"]
    band_basis = PROOF_278.projection_basis(band_projection)

    sonin_block = PROOF_280.compression(sonin_basis, matrix)
    sonin_to_band = sonin_basis.conj().T @ matrix @ band_basis
    band_to_sonin = band_basis.conj().T @ matrix @ sonin_basis
    band_block = PROOF_280.compression(band_basis, matrix)
    shorted = band_block - band_to_sonin @ np.linalg.solve(
        sonin_block, sonin_to_band
    )
    return {
        "sonin_basis": sonin_basis,
        "band_basis": band_basis,
        "sonin_block": sonin_block,
        "sonin_to_band": sonin_to_band,
        "band_to_sonin": band_to_sonin,
        "band_block": band_block,
        "shorted": shorted,
    }


def band_cocycle(
    model: dict[str, np.ndarray],
    detector_multiplier: np.ndarray,
    generator_multiplier: np.ndarray,
) -> dict[str, np.ndarray | float]:
    product_multiplier = detector_multiplier @ generator_multiplier
    detector_data = shorted_band(model, detector_multiplier)
    generator_data = shorted_band(model, generator_multiplier)
    product_data = shorted_band(model, product_multiplier)
    detector_short = detector_data["shorted"]
    generator_short = generator_data["shorted"]
    product_short = product_data["shorted"]
    cocycle = (
        product_short
        @ np.linalg.inv(generator_short)
        @ np.linalg.inv(detector_short)
    )
    logarithm = (
        PROOF_279.log_positive_determinant(product_short)
        - PROOF_279.log_positive_determinant(detector_short)
        - PROOF_279.log_positive_determinant(generator_short)
    )
    return {
        "detector_short": detector_short,
        "generator_short": generator_short,
        "product_short": product_short,
        "cocycle": cocycle,
        "log_determinant": logarithm,
        "band_basis": detector_data["band_basis"],
    }


def band_log(
    model: dict[str, np.ndarray],
    multiplier_basis: np.ndarray,
    detector_values: np.ndarray,
    generator_values: np.ndarray,
    detector_parameter: float,
    generator_parameter: float,
) -> float:
    family = PROOF_280.multiplier_family(
        multiplier_basis,
        detector_values,
        generator_values,
        detector_parameter,
        generator_parameter,
    )
    return float(
        band_cocycle(
            model, family["detector"], family["generator"]
        )["log_determinant"]
    )


def mixed_derivative(
    model: dict[str, np.ndarray],
    multiplier_basis: np.ndarray,
    detector_values: np.ndarray,
    generator_values: np.ndarray,
    step: float,
) -> float:
    values: dict[tuple[int, int], float] = {}
    for detector_sign in (-1, 1):
        for generator_sign in (-1, 1):
            values[(detector_sign, generator_sign)] = band_log(
                model,
                multiplier_basis,
                detector_values,
                generator_values,
                detector_sign * step,
                generator_sign * step,
            )
    return (
        values[(1, 1)]
        - values[(1, -1)]
        - values[(-1, 1)]
        + values[(-1, -1)]
    ) / (4.0 * step**2)


def band_crossing_scalar(
    model: dict[str, np.ndarray],
    detector: np.ndarray,
    generator: np.ndarray,
) -> complex:
    size = detector.shape[0]
    identity = np.eye(size, dtype=complex)
    outer = model["outer"]
    sonin = model["sonin"]
    band = outer - sonin
    exterior = identity - outer
    return np.trace(
        band @ detector @ exterior @ generator @ band
    ) - np.trace(
        sonin @ detector @ band @ generator @ sonin
    )


def block_diagonal_detector_guard(
    model: dict[str, np.ndarray],
    generator_multiplier: np.ndarray,
) -> dict[str, float]:
    size = generator_multiplier.shape[0]
    identity = np.eye(size, dtype=complex)
    outer = model["outer"]
    sonin = model["sonin"]
    band = outer - sonin
    exterior = identity - outer
    detector_multiplier = (
        1.13 * exterior + 0.91 * sonin + 1.27 * band
    )
    detector_short = shorted_band(
        model, detector_multiplier
    )["shorted"]
    generator_short = shorted_band(
        model, generator_multiplier
    )["shorted"]
    product_short = shorted_band(
        model, detector_multiplier @ generator_multiplier
    )["shorted"]
    band_cocycle_matrix = (
        product_short
        @ np.linalg.inv(generator_short)
        @ np.linalg.inv(detector_short)
    )
    band_identity = np.eye(detector_short.shape[0], dtype=complex)

    outer_basis = PROOF_278.projection_basis(outer)
    sonin_basis = PROOF_278.projection_basis(sonin)
    outer_detector = PROOF_280.compression(
        outer_basis, detector_multiplier
    )
    outer_generator = PROOF_280.compression(
        outer_basis, generator_multiplier
    )
    outer_product = PROOF_280.compression(
        outer_basis, detector_multiplier @ generator_multiplier
    )
    outer_cocycle_matrix = (
        outer_product
        @ np.linalg.inv(outer_generator)
        @ np.linalg.inv(outer_detector)
    )
    sonin_detector = PROOF_280.compression(
        sonin_basis, detector_multiplier
    )
    sonin_generator = PROOF_280.compression(
        sonin_basis, generator_multiplier
    )
    sonin_product = PROOF_280.compression(
        sonin_basis, detector_multiplier @ generator_multiplier
    )
    sonin_cocycle_matrix = (
        sonin_product
        @ np.linalg.inv(sonin_generator)
        @ np.linalg.inv(sonin_detector)
    )
    return {
        "detector outer commutator norm": float(
            np.linalg.norm(
                detector_multiplier @ outer
                - outer @ detector_multiplier,
                ord=2,
            )
        ),
        "detector Sonin commutator norm": float(
            np.linalg.norm(
                detector_multiplier @ sonin
                - sonin @ detector_multiplier,
                ord=2,
            )
        ),
        "band cocycle identity error": float(
            np.linalg.norm(
                band_cocycle_matrix - band_identity, ord=2
            )
        ),
        "outer cocycle identity error": float(
            np.linalg.norm(
                outer_cocycle_matrix
                - np.eye(outer_basis.shape[1], dtype=complex),
                ord=2,
            )
        ),
        "Sonin cocycle identity error": float(
            np.linalg.norm(
                sonin_cocycle_matrix
                - np.eye(sonin_basis.shape[1], dtype=complex),
                ord=2,
            )
        ),
    }


def generic_checks(
    size: int,
    support_rank: int,
    seed: int,
    detector_parameter: float,
    generator_parameter: float,
    derivative_step: float,
) -> tuple[
    dict[str, float],
    dict[str, float],
    dict[str, float],
    dict[str, float],
]:
    rng = np.random.default_rng(seed)
    model = PROOF_278.build_source_model(size, support_rank, rng)
    detector, generator, basis, detector_values, generator_values = (
        PROOF_278.build_commuting_multipliers(size, rng)
    )
    channels = PROOF_279.channel_data(model)
    family = PROOF_280.multiplier_family(
        basis,
        detector_values,
        generator_values,
        detector_parameter,
        generator_parameter,
    )
    data = band_cocycle(
        model, family["detector"], family["generator"]
    )
    cocycle_coordinates = PROOF_280.cocycle_logs(
        model,
        channels,
        basis,
        detector_values,
        generator_values,
        detector_parameter,
        generator_parameter,
    )
    derivative = mixed_derivative(
        model,
        basis,
        detector_values,
        generator_values,
        derivative_step,
    )
    outer_covariance = PROOF_279.covariance(
        model["outer"], detector, generator
    )
    sonin_covariance = PROOF_279.covariance(
        model["sonin"], detector, generator
    )
    relative_covariance = outer_covariance - sonin_covariance
    crossing_scalar = band_crossing_scalar(model, detector, generator)

    algebra = {
        "band determinant-line error": float(
            abs(
                data["log_determinant"]
                - cocycle_coordinates["relative"]
            )
        ),
        "band versus Burnol boundary error": float(
            abs(
                data["log_determinant"]
                - cocycle_coordinates["relative_boundary"]
            )
        ),
        "band versus channel Schur error": float(
            abs(
                data["log_determinant"]
                - cocycle_coordinates["channel_relative"]
            )
        ),
        "relative band crossing error": float(
            abs(relative_covariance - crossing_scalar)
        ),
        "band mixed derivative error": float(
            abs(derivative - relative_covariance.real)
        ),
    }
    diagnostics = {
        "band cocycle displacement norm": float(
            np.linalg.norm(
                data["cocycle"]
                - np.eye(data["band_basis"].shape[1], dtype=complex),
                ord=2,
            )
        ),
        "band cocycle log magnitude": float(
            abs(data["log_determinant"])
        ),
        "relative covariance magnitude": float(abs(relative_covariance)),
        "band crossing magnitude": float(abs(crossing_scalar)),
    }
    positivity = {
        "detector short minimum eigenvalue": float(
            np.linalg.eigvalsh(data["detector_short"])[0]
        ),
        "generator short minimum eigenvalue": float(
            np.linalg.eigvalsh(data["generator_short"])[0]
        ),
        "product short minimum eigenvalue": float(
            np.linalg.eigvalsh(data["product_short"])[0]
        ),
    }
    diagonal_guard = block_diagonal_detector_guard(
        model, family["generator"]
    )
    return algebra, diagnostics, positivity, diagonal_guard


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
    vector = np.array([0.0, 1.0, 1.0], dtype=complex) / math.sqrt(2.0)
    detector = np.outer(vector, vector.conj())
    eigenvalues, eigenvectors = np.linalg.eigh(detector)
    family = PROOF_280.multiplier_family(
        eigenvectors,
        eigenvalues,
        eigenvalues,
        detector_parameter,
        generator_parameter,
    )
    data = band_cocycle(
        model, family["detector"], family["generator"]
    )
    derivative = mixed_derivative(
        model,
        eigenvectors,
        eigenvalues,
        eigenvalues,
        derivative_step,
    )
    relative_covariance = (
        PROOF_279.covariance(model["outer"], detector, detector)
        - PROOF_279.covariance(model["sonin"], detector, detector)
    ).real
    crossing_scalar = band_crossing_scalar(
        model, detector, detector
    ).real
    return {
        "truncated Fourier norm": float(
            np.linalg.norm(model["truncated_transform"], ord=2)
        ),
        "prolate correction norm": float(
            np.linalg.norm(model["prolate"], ord=2)
        ),
        "band cocycle log magnitude": float(
            abs(data["log_determinant"])
        ),
        "relative covariance": float(relative_covariance),
        "band crossing scalar": float(crossing_scalar),
        "band crossing error": float(
            abs(crossing_scalar - relative_covariance)
        ),
        "band derivative error": float(
            abs(derivative - relative_covariance)
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
    parser.add_argument("--seed", type=int, default=1281)
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

    algebra, diagnostics, positivity, diagonal_guard = generic_checks(
        args.size,
        args.support_rank,
        args.seed,
        args.detector_parameter,
        args.generator_parameter,
        args.derivative_step,
    )
    zero_guard = zero_prolate_guard(
        args.detector_parameter,
        args.generator_parameter,
        args.derivative_step,
    )

    print("identity=nested band-shorted semicommutator")
    print("status=fixed-S band determinant exact; uniform bound open")
    print_checks("Band determinant and derivative checks", algebra)
    print()
    print_checks("Band diagnostics", diagnostics)
    print()
    print_checks("Shorted positivity", positivity)
    print()
    print_checks("Block-diagonal detector guard", diagonal_guard)
    print()
    print_checks("Deterministic zero-prolate guard", zero_guard)

    algebra_error = max(algebra.values())
    diagonal_error = max(diagonal_guard.values())
    zero_error = max(
        zero_guard["band crossing error"],
        zero_guard["band derivative error"],
        zero_guard["relative target error"],
    )
    print(f"maximum band algebra error={algebra_error:.12e}")
    print(f"maximum block-diagonal guard error={diagonal_error:.12e}")
    print(f"maximum zero-prolate guard error={zero_error:.12e}")

    if algebra_error > args.derivative_tolerance:
        raise SystemExit(
            f"band semicommutator algebra failed: {algebra_error:.6e}"
        )
    if diagonal_error > args.algebra_tolerance:
        raise SystemExit(
            f"block-diagonal ownership guard failed: {diagonal_error:.6e}"
        )
    if zero_error > args.derivative_tolerance:
        raise SystemExit(
            f"zero-prolate band guard failed: {zero_error:.6e}"
        )
    if min(positivity.values()) <= 0.0:
        raise SystemExit("a shorted multiplier lost positivity")

    print("nested_band_determinant_coordinate=EXACT")
    print("band_semicommutator_fredholm_domain=EXACT")
    print("relative_physical_band_crossings=EXACT")
    print("block_diagonal_detector_gives_identity=EXACT")
    print("separate_E_R_determinant_estimates_required=FALSE")
    print("uniform_relative_band_bound=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
