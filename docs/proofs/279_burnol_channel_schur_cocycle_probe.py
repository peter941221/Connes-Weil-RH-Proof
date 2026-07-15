#!/usr/bin/env python3
"""Certificate for Proof 279's Burnol channel Schur cocycle.

The script imports Proof 278's source-shaped finite model.  It turns the
Hadamard plus/minus Gram diagonalization into an exact determinant
factorization with two diagonal boundary channels and one off-diagonal Schur
coupling.  Its mixed derivative reads back the complete boundary covariance.

A deterministic three-dimensional guard has F_0=K_prol=0 but a nonzero
relative covariance.  It proves that diagonalizing the static Gram does not
diagonalize a perturbed boundary determinant.
"""

from __future__ import annotations

import argparse
import importlib.util
import math
from pathlib import Path
from types import ModuleType

import numpy as np


def load_proof_278() -> ModuleType:
    path = Path(__file__).with_name(
        "278_burnol_boundary_gram_covariance_probe.py"
    )
    specification = importlib.util.spec_from_file_location(
        "proof_278_for_279", path
    )
    if specification is None or specification.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(specification)
    specification.loader.exec_module(module)
    return module


PROOF_278 = load_proof_278()


def log_positive_determinant(matrix: np.ndarray) -> float:
    hermitian = (matrix + matrix.conj().T) / 2.0
    sign, logarithm = np.linalg.slogdet(hermitian)
    if abs(sign - 1.0) > 1e-8:
        raise ValueError("expected a positive determinant")
    return float(logarithm)


def covariance(
    projection: np.ndarray,
    detector: np.ndarray,
    generator: np.ndarray,
) -> complex:
    identity = np.eye(projection.shape[0], dtype=complex)
    return np.trace(
        projection
        @ detector
        @ (identity - projection)
        @ generator
        @ projection
    )


def channel_data(
    model: dict[str, np.ndarray],
) -> dict[str, np.ndarray]:
    transform = model["transform"]
    support_basis = model["support_basis"]
    truncated_transform = model["truncated_transform"]
    small_identity = np.eye(support_basis.shape[1], dtype=complex)

    plus_synthesis = (
        support_basis + transform @ support_basis
    ) / math.sqrt(2.0)
    minus_synthesis = (
        support_basis - transform @ support_basis
    ) / math.sqrt(2.0)
    plus_gram = small_identity + truncated_transform
    minus_gram = small_identity - truncated_transform
    plus_isometry = plus_synthesis @ PROOF_278.inverse_square_root(
        plus_gram
    )
    minus_isometry = minus_synthesis @ PROOF_278.inverse_square_root(
        minus_gram
    )
    boundary_isometry = np.concatenate(
        [plus_isometry, minus_isometry], axis=1
    )
    plus_projection = plus_isometry @ plus_isometry.conj().T
    minus_projection = minus_isometry @ minus_isometry.conj().T

    return {
        "plus_synthesis": plus_synthesis,
        "minus_synthesis": minus_synthesis,
        "plus_gram": plus_gram,
        "minus_gram": minus_gram,
        "plus_isometry": plus_isometry,
        "minus_isometry": minus_isometry,
        "boundary_isometry": boundary_isometry,
        "plus_projection": plus_projection,
        "minus_projection": minus_projection,
    }


def boundary_blocks(
    channels: dict[str, np.ndarray], inverse_multiplier: np.ndarray
) -> dict[str, np.ndarray]:
    plus_isometry = channels["plus_isometry"]
    minus_isometry = channels["minus_isometry"]
    boundary_isometry = channels["boundary_isometry"]

    plus_block = (
        plus_isometry.conj().T
        @ inverse_multiplier
        @ plus_isometry
    )
    minus_block = (
        minus_isometry.conj().T
        @ inverse_multiplier
        @ minus_isometry
    )
    coupling_block = (
        plus_isometry.conj().T
        @ inverse_multiplier
        @ minus_isometry
    )
    schur_complement = minus_block - coupling_block.conj().T @ np.linalg.solve(
        plus_block, coupling_block
    )
    minus_inverse_square_root = PROOF_278.inverse_square_root(minus_block)
    normalized_coupling = (
        minus_inverse_square_root
        @ schur_complement
        @ minus_inverse_square_root
    )
    full_boundary = (
        boundary_isometry.conj().T
        @ inverse_multiplier
        @ boundary_isometry
    )
    return {
        "plus": plus_block,
        "minus": minus_block,
        "cross": coupling_block,
        "schur": schur_complement,
        "normalized_coupling": normalized_coupling,
        "full": full_boundary,
    }


def channel_log_determinants(
    channels: dict[str, np.ndarray],
    support_basis: np.ndarray,
    inverse_multiplier: np.ndarray,
) -> dict[str, float]:
    blocks = boundary_blocks(channels, inverse_multiplier)
    outer_boundary = (
        support_basis.conj().T
        @ inverse_multiplier
        @ support_basis
    )
    plus_log = log_positive_determinant(blocks["plus"])
    minus_log = log_positive_determinant(blocks["minus"])
    coupling_log = log_positive_determinant(
        blocks["normalized_coupling"]
    )
    full_log = log_positive_determinant(blocks["full"])
    outer_log = log_positive_determinant(outer_boundary)
    return {
        "outer": outer_log,
        "plus": plus_log,
        "minus": minus_log,
        "coupling": coupling_log,
        "full": full_log,
        "relative": outer_log - full_log,
        "factorized_relative": (
            outer_log - plus_log - minus_log - coupling_log
        ),
    }


def mixed_derivatives(
    channels: dict[str, np.ndarray],
    support_basis: np.ndarray,
    multiplier_basis: np.ndarray,
    detector_values: np.ndarray,
    generator_values: np.ndarray,
    step: float,
) -> dict[str, float]:
    corner_logs: dict[tuple[int, int], dict[str, float]] = {}
    for detector_sign in (-1, 1):
        for generator_sign in (-1, 1):
            detector_parameter = detector_sign * step
            generator_parameter = generator_sign * step
            inverse_multiplier = PROOF_278.multiplier_exponential(
                multiplier_basis,
                detector_values,
                generator_values,
                -detector_parameter,
                -generator_parameter,
            )
            corner_logs[(detector_sign, generator_sign)] = (
                channel_log_determinants(
                    channels, support_basis, inverse_multiplier
                )
            )

    derivatives: dict[str, float] = {}
    for label in corner_logs[(1, 1)]:
        derivatives[label] = (
            corner_logs[(1, 1)][label]
            - corner_logs[(1, -1)][label]
            - corner_logs[(-1, 1)][label]
            + corner_logs[(-1, -1)][label]
        ) / (4.0 * step**2)
    return derivatives


def generic_checks(
    size: int,
    support_rank: int,
    seed: int,
    determinant_parameter: float,
    derivative_step: float,
) -> tuple[dict[str, float], dict[str, float], dict[str, float]]:
    rng = np.random.default_rng(seed)
    model = PROOF_278.build_source_model(size, support_rank, rng)
    detector, generator, basis, detector_values, generator_values = (
        PROOF_278.build_commuting_multipliers(size, rng)
    )
    channels = channel_data(model)
    plus_isometry = channels["plus_isometry"]
    minus_isometry = channels["minus_isometry"]
    plus_projection = channels["plus_projection"]
    minus_projection = channels["minus_projection"]
    boundary_isometry = channels["boundary_isometry"]
    small_identity = np.eye(support_rank, dtype=complex)
    boundary_identity = np.eye(2 * support_rank, dtype=complex)

    inverse_multiplier = PROOF_278.multiplier_exponential(
        basis,
        detector_values,
        generator_values,
        -determinant_parameter,
        0.61 * determinant_parameter,
    )
    blocks = boundary_blocks(channels, inverse_multiplier)
    logs = channel_log_determinants(
        channels, model["support_basis"], inverse_multiplier
    )

    support_covariance = covariance(
        model["support"], detector, generator
    )
    outer_covariance = covariance(model["outer"], detector, generator)
    plus_covariance = covariance(
        plus_projection, detector, generator
    )
    minus_covariance = covariance(
        minus_projection, detector, generator
    )
    complement_covariance = covariance(
        model["complement"], detector, generator
    )
    sonin_covariance = covariance(model["sonin"], detector, generator)
    cross_penalty = 2.0 * np.real(
        np.trace(
            plus_projection
            @ detector
            @ minus_projection
            @ generator
            @ plus_projection
        )
    )
    relative_covariance = outer_covariance - sonin_covariance
    channel_relative_covariance = (
        support_covariance
        - plus_covariance
        - minus_covariance
        + cross_penalty
    )

    derivatives = mixed_derivatives(
        channels,
        model["support_basis"],
        basis,
        detector_values,
        generator_values,
        derivative_step,
    )
    expected_derivatives = {
        "outer": support_covariance.real,
        "plus": plus_covariance.real,
        "minus": minus_covariance.real,
        "coupling": -cross_penalty,
        "full": complement_covariance.real,
        "relative": relative_covariance.real,
        "factorized_relative": relative_covariance.real,
    }

    transform = model["transform"]
    plus_isometry = channels["plus_isometry"]
    minus_isometry = channels["minus_isometry"]
    fourier_even_multiplier = (
        inverse_multiplier
        + transform @ inverse_multiplier @ transform
    ) / 2.0
    fourier_odd_multiplier = (
        inverse_multiplier
        - transform @ inverse_multiplier @ transform
    ) / 2.0
    commutator_block = (
        plus_isometry.conj().T
        @ (transform @ inverse_multiplier - inverse_multiplier @ transform)
        @ minus_isometry
    ) / 2.0

    algebra = {
        "plus Fourier eigenchannel error": float(
            np.linalg.norm(
                transform @ plus_isometry - plus_isometry, ord=2
            )
        ),
        "minus Fourier eigenchannel error": float(
            np.linalg.norm(
                transform @ minus_isometry + minus_isometry, ord=2
            )
        ),
        "plus isometry error": float(
            np.linalg.norm(
                plus_isometry.conj().T @ plus_isometry - small_identity,
                ord=2,
            )
        ),
        "minus isometry error": float(
            np.linalg.norm(
                minus_isometry.conj().T @ minus_isometry - small_identity,
                ord=2,
            )
        ),
        "channel orthogonality error": float(
            np.linalg.norm(
                plus_isometry.conj().T @ minus_isometry, ord=2
            )
        ),
        "boundary isometry error": float(
            np.linalg.norm(
                boundary_isometry.conj().T @ boundary_isometry
                - boundary_identity,
                ord=2,
            )
        ),
        "complement channel split error": float(
            np.linalg.norm(
                plus_projection
                + minus_projection
                - model["complement"],
                ord=2,
            )
        ),
        "boundary block assembly error": float(
            np.linalg.norm(
                blocks["full"]
                - np.block(
                    [
                        [blocks["plus"], blocks["cross"]],
                        [
                            blocks["cross"].conj().T,
                            blocks["minus"],
                        ],
                    ]
                ),
                ord=2,
            )
        ),
        "plus Fourier-even block error": float(
            np.linalg.norm(
                blocks["plus"]
                - plus_isometry.conj().T
                @ fourier_even_multiplier
                @ plus_isometry,
                ord=2,
            )
        ),
        "minus Fourier-even block error": float(
            np.linalg.norm(
                blocks["minus"]
                - minus_isometry.conj().T
                @ fourier_even_multiplier
                @ minus_isometry,
                ord=2,
            )
        ),
        "cross Fourier-odd block error": float(
            np.linalg.norm(
                blocks["cross"]
                - plus_isometry.conj().T
                @ fourier_odd_multiplier
                @ minus_isometry,
                ord=2,
            )
        ),
        "cross Fourier-commutator error": float(
            np.linalg.norm(blocks["cross"] - commutator_block, ord=2)
        ),
        "Schur log-determinant error": float(
            abs(
                logs["full"]
                - logs["plus"]
                - logs["minus"]
                - logs["coupling"]
            )
        ),
        "relative channel determinant error": float(
            abs(logs["relative"] - logs["factorized_relative"])
        ),
        "complement covariance split error": float(
            abs(
                complement_covariance
                - plus_covariance
                - minus_covariance
                + cross_penalty
            )
        ),
        "relative covariance split error": float(
            abs(relative_covariance - channel_relative_covariance)
        ),
        "projection-complement covariance error": float(
            max(
                abs(support_covariance - outer_covariance),
                abs(complement_covariance - sonin_covariance),
            )
        ),
    }
    derivative_errors = {
        f"{label} mixed derivative error": float(
            abs(derivatives[label] - expected)
        )
        for label, expected in expected_derivatives.items()
    }
    diagnostics = {
        "off-diagonal boundary block norm": float(
            np.linalg.norm(blocks["cross"], ord=2)
        ),
        "cross-channel covariance magnitude": float(abs(cross_penalty)),
        "relative covariance magnitude": float(abs(relative_covariance)),
    }
    return algebra, derivative_errors, diagnostics


def deterministic_zero_prolate_guard() -> dict[str, float]:
    transform = np.array(
        [[0.0, 1.0, 0.0], [1.0, 0.0, 0.0], [0.0, 0.0, 1.0]],
        dtype=complex,
    )
    model = PROOF_278.assemble_source_model(transform, support_rank=1)
    channels = channel_data(model)
    vector = np.array([0.0, 1.0, 1.0], dtype=complex) / math.sqrt(2.0)
    multiplier = np.outer(vector, vector.conj())

    plus_covariance = covariance(
        channels["plus_projection"], multiplier, multiplier
    ).real
    minus_covariance = covariance(
        channels["minus_projection"], multiplier, multiplier
    ).real
    cross_penalty = 2.0 * np.real(
        np.trace(
            channels["plus_projection"]
            @ multiplier
            @ channels["minus_projection"]
            @ multiplier
            @ channels["plus_projection"]
        )
    )
    sonin_covariance = covariance(
        model["sonin"], multiplier, multiplier
    ).real
    outer_covariance = covariance(
        model["outer"], multiplier, multiplier
    ).real
    relative_covariance = outer_covariance - sonin_covariance

    return {
        "truncated Fourier norm": float(
            np.linalg.norm(model["truncated_transform"], ord=2)
        ),
        "prolate correction norm": float(
            np.linalg.norm(model["prolate"], ord=2)
        ),
        "plus direct covariance": float(plus_covariance),
        "minus direct covariance": float(minus_covariance),
        "cross-channel repair": float(cross_penalty),
        "Sonin covariance": float(sonin_covariance),
        "relative E/R covariance": float(relative_covariance),
        "plus target error": float(abs(plus_covariance - 3.0 / 16.0)),
        "minus target error": float(abs(minus_covariance - 3.0 / 16.0)),
        "cross target error": float(abs(cross_penalty - 1.0 / 8.0)),
        "Sonin target error": float(abs(sonin_covariance - 1.0 / 4.0)),
        "relative target error": float(abs(relative_covariance + 1.0 / 4.0)),
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
    parser.add_argument("--seed", type=int, default=1279)
    parser.add_argument("--determinant-parameter", type=float, default=0.17)
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
        args.determinant_parameter,
        args.derivative_step,
    )
    guard = deterministic_zero_prolate_guard()

    print("identity=Burnol plus/minus channel Schur cocycle")
    print("status=exact finite algebra; continuous relative theorem open")
    print_checks("Channel algebra checks", algebra)
    print()
    print_checks("Mixed derivative checks", derivative_errors)
    print()
    print_checks("Generic channel diagnostics", diagnostics)
    print()
    print_checks("Deterministic zero-prolate guard", guard)

    algebra_error = max(algebra.values())
    derivative_error = max(derivative_errors.values())
    guard_error = max(
        value for label, value in guard.items() if label.endswith("error")
    )
    print(f"maximum algebra error={algebra_error:.12e}")
    print(f"maximum mixed derivative error={derivative_error:.12e}")
    print(f"maximum deterministic guard error={guard_error:.12e}")

    if algebra_error > args.algebra_tolerance:
        raise SystemExit(
            f"channel Schur algebra failed: {algebra_error:.6e}"
        )
    if derivative_error > args.derivative_tolerance:
        raise SystemExit(
            f"channel derivative readback failed: {derivative_error:.6e}"
        )
    if guard_error > args.algebra_tolerance:
        raise SystemExit(
            f"zero-prolate exact guard failed: {guard_error:.6e}"
        )

    print("burnol_plus_minus_orthogonal_split=EXACT")
    print("boundary_schur_determinant=EXACT")
    print("channel_mixed_derivative_readback=EXACT")
    print("static_gram_diagonalizes_perturbed_boundary=REJECTED")
    print("prolate_only_half_power=REJECTED")
    print("continuous_root_sandwiched_channel_domain=OPEN")
    print("source_relative_wiener_hopf_bogc=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
