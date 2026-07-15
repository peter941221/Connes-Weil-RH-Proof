#!/usr/bin/env python3
"""Certificate for the one-sided collapse of the inverse-metric coframe.

The continuous Euler inverse A = T^-1 is a normal one-sided convolution.  If
the preserved half-line C is invariant under A and T, then M = H^-1 may be
written as A* A and

    C M C = (C A C)* (C A C).

Consequently the coframe from Proof 255 has no independent conditioned
inverse:

    D = B - C (C M C)^-1 C M B = T E T^-1 B.

The first certificate checks the block factorization for an exact triangular
spectral factor.  The periodic Sonin section checks the exact
hard-linear/two-crossing response split but destroys half-line invariance.  A
second zero-fill section preserves the causal triangular factor exactly, but
its artificial outer endpoint destroys normality and exact convolution
commutation.  The two finite models are complementary diagnostics; neither is
used as a finite-dimensional substitute for the continuous theorem.
"""

from __future__ import annotations

import argparse
import importlib.util
import math
from pathlib import Path
from types import ModuleType

import numpy as np


def load_proof_255() -> ModuleType:
    path = Path(__file__).with_name(
        "255_nested_shorting_cancellation_probe.py"
    )
    spec = importlib.util.spec_from_file_location("proof_255", path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path.name}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


PROOF_255 = load_proof_255()
PROOF_252 = PROOF_255.PROOF_252
PROOF_251 = PROOF_255.PROOF_251


def projection(columns: np.ndarray) -> np.ndarray:
    return columns @ columns.conj().T


def relative_error(actual: np.ndarray, expected: np.ndarray) -> float:
    denominator = max(float(np.linalg.norm(expected, ord="fro")), 1e-15)
    return float(np.linalg.norm(actual - expected, ord="fro") / denominator)


def selector_basis(size: int, start: int, stop: int) -> np.ndarray:
    basis = np.zeros((size, stop - start), dtype=complex)
    basis[np.arange(start, stop), np.arange(stop - start)] = 1.0
    return basis


def stable_random_block(
    rng: np.random.Generator, size: int, scale: float
) -> np.ndarray:
    random = rng.normal(size=(size, size)) + 1j * rng.normal(
        size=(size, size)
    )
    random /= max(float(np.linalg.norm(random, ord=2)), 1e-15)
    return np.eye(size, dtype=complex) + scale * random


def triangular_factor_certificate(size: int, seed: int) -> dict[str, float]:
    rng = np.random.default_rng(seed)
    e_rank = size // 2
    r_rank = size // 4
    c_rank = size - e_rank
    r_basis = selector_basis(size, 0, r_rank)
    b_basis = selector_basis(size, r_rank, e_rank)
    c_basis = selector_basis(size, e_rank, size)
    e_basis = np.concatenate([r_basis, b_basis], axis=1)
    e_projection = projection(e_basis)

    e_block = stable_random_block(rng, e_rank, 0.18)
    c_block = stable_random_block(rng, c_rank, 0.16)
    crossing = rng.normal(size=(c_rank, e_rank)) + 1j * rng.normal(
        size=(c_rank, e_rank)
    )
    crossing *= 0.12 / max(float(np.linalg.norm(crossing, ord=2)), 1e-15)

    inverse_transport = np.block(
        [
            [e_block, np.zeros((e_rank, c_rank), dtype=complex)],
            [crossing, c_block],
        ]
    )
    transport = np.linalg.inv(inverse_transport)
    inverse_metric_factor = inverse_transport.conj().T @ inverse_transport

    c_metric = (
        c_basis.conj().T @ inverse_metric_factor @ c_basis
    )
    cb_metric = (
        c_basis.conj().T @ inverse_metric_factor @ b_basis
    )
    shorted_coframe = b_basis - c_basis @ np.linalg.solve(
        c_metric, cb_metric
    )
    oblique_coframe = transport @ e_projection @ inverse_transport @ b_basis

    restricted_factor = c_basis.conj().T @ inverse_transport @ c_basis
    direct_c_metric = restricted_factor.conj().T @ restricted_factor
    direct_cb_metric = (
        restricted_factor.conj().T
        @ c_basis.conj().T
        @ inverse_transport
        @ b_basis
    )
    triangular_coframe = b_basis - c_basis @ np.linalg.solve(
        restricted_factor,
        c_basis.conj().T @ inverse_transport @ b_basis,
    )

    preserved_error = float(
        np.linalg.norm(
            e_basis.conj().T @ inverse_transport @ c_basis, ord="fro"
        )
    )
    return {
        "inverse_error": float(
            np.linalg.norm(
                inverse_transport @ transport - np.eye(size), ord=2
            )
        ),
        "preserved_halfline_error": preserved_error,
        "metric_factor_error": relative_error(c_metric, direct_c_metric),
        "cross_factor_error": relative_error(cb_metric, direct_cb_metric),
        "triangular_coframe_error": relative_error(
            shorted_coframe, triangular_coframe
        ),
        "oblique_coframe_error": relative_error(
            shorted_coframe, oblique_coframe
        ),
        "coframe_pairing_error": relative_error(
            b_basis.conj().T @ shorted_coframe,
            np.eye(b_basis.shape[1]),
        ),
        "shorted_coframe_norm": float(
            np.linalg.norm(shorted_coframe, ord=2)
        ),
    }


def finite_sonin_row(
    size: int,
    step: float,
    root_width: float,
    cutoff: int,
    intersection_tolerance: float,
) -> dict[str, float]:
    primes = PROOF_252.primes_up_to(cutoff)
    r_basis, b_basis, c_basis, nesting_error, _ = PROOF_255.sonin_bases(
        size, step, intersection_tolerance
    )
    detector, _, row_residual = PROOF_255.root_detector(
        size, step, root_width
    )
    transport, inverse_transport, log_condition = (
        PROOF_255.normalized_fourier_transport(primes, size, step)
    )
    data = PROOF_255.nested_data(
        transport,
        inverse_transport,
        r_basis,
        b_basis,
        c_basis,
    )

    b_projection = projection(b_basis)
    e_projection = projection(np.concatenate([r_basis, b_basis], axis=1))
    schur_coordinates = np.asarray(data["schur_coordinates"])
    dual_coordinates = np.asarray(data["dual_coordinates"])
    oblique_e = np.asarray(data["oblique_e"])
    oblique_coframe = oblique_e @ b_basis
    detector_b = b_basis.conj().T @ detector @ b_basis
    intrinsic_defect = (
        detector @ schur_coordinates
        - schur_coordinates @ detector_b
    )

    graph_coordinates = -r_basis.conj().T @ schur_coordinates
    hard_linear = -np.trace(
        b_basis.conj().T
        @ detector
        @ r_basis
        @ graph_coordinates
    )
    base_defect = b_basis.conj().T @ intrinsic_defect
    hard_linear_direct = np.trace(base_defect)
    coframe_correction = np.trace(
        (dual_coordinates - b_basis).conj().T @ intrinsic_defect
    )
    complete_response = np.trace(
        dual_coordinates.conj().T @ intrinsic_defect
    )

    inverse_crossing = c_basis.conj().T @ inverse_transport @ b_basis
    transport_crossing = c_basis.conj().T @ transport @ e_projection
    return {
        "size": float(size),
        "step": step,
        "half_domain": size * step / 2.0,
        "cutoff": float(cutoff),
        "prime_count": float(len(primes)),
        "sonin_rank": float(r_basis.shape[1]),
        "nesting_error": nesting_error,
        "row_residual": row_residual,
        "log_condition": log_condition,
        "coframe_collapse_error": relative_error(
            dual_coordinates, oblique_coframe
        ),
        "hard_linear_identity_error": abs(
            hard_linear - hard_linear_direct
        )
        / max(abs(hard_linear), 1.0),
        "response_split_error": abs(
            hard_linear + coframe_correction - complete_response
        )
        / max(abs(complete_response), 1.0),
        "hard_linear": float(hard_linear.real),
        "hard_linear_abs": float(abs(hard_linear)),
        "coframe_correction": float(coframe_correction.real),
        "coframe_correction_abs": float(abs(coframe_correction)),
        "complete_response": float(complete_response.real),
        "complete_imaginary": float(abs(complete_response.imag)),
        "graph_norm": float(np.linalg.norm(graph_coordinates, ord=2)),
        "dual_coordinate_norm": float(
            np.linalg.norm(dual_coordinates, ord=2)
        ),
        "oblique_coframe_norm": float(
            np.linalg.norm(oblique_coframe, ord=2)
        ),
        "inverse_crossing_norm": float(
            np.linalg.norm(inverse_crossing, ord=2)
        ),
        "transport_crossing_norm": float(
            np.linalg.norm(transport_crossing, ord=2)
        ),
    }


def negative_shift(values: np.ndarray, displacement: int) -> np.ndarray:
    shifted = np.zeros_like(values)
    if displacement == 0:
        shifted[:] = values
    else:
        shifted[:-displacement] = values[displacement:]
    return shifted


def causal_factors(primes: list[int], step: float) -> list[tuple[float, int]]:
    factors: list[tuple[float, int]] = []
    for prime in primes:
        displacement = int(round(math.log(prime) / step))
        if displacement <= 0:
            raise ValueError("causal prime displacement vanished on the grid")
        factors.append((prime ** -0.5, displacement))
    return factors


def apply_causal_transport(
    values: np.ndarray, factors: list[tuple[float, int]]
) -> np.ndarray:
    result = values.copy()
    for amplitude, displacement in factors:
        result = result - amplitude * negative_shift(result, displacement)
    return result


def apply_causal_inverse(
    values: np.ndarray, factors: list[tuple[float, int]]
) -> np.ndarray:
    result = values.copy()
    for amplitude, displacement in reversed(factors):
        solved = result.copy()
        for index in range(len(result) - displacement - 1, -1, -1):
            solved[index] += amplitude * solved[index + displacement]
        result = solved
    return result


def compact_toeplitz_detector(
    size: int, step: float, root_width: float
) -> tuple[np.ndarray, float]:
    root_size = int(round(root_width / step)) + 1
    witness, row_residual = PROOF_251.four_mode_row_witness(root_size, step)
    derivative = np.gradient(witness, step)
    root = derivative + 0.5 * witness
    correlation = step * np.correlate(root, root, mode="full")
    lag = np.arange(size)[:, None] - np.arange(size)[None, :]
    detector = np.zeros((size, size), dtype=complex)
    selected = np.abs(lag) < root_size
    detector[selected] = correlation[
        lag[selected] + root_size - 1
    ]
    detector = (detector + detector.conj().T) / 2.0
    return detector, row_residual


def causal_sonin_row(
    size: int,
    step: float,
    root_width: float,
    cutoff: int,
    intersection_tolerance: float,
) -> dict[str, float]:
    primes = PROOF_252.primes_up_to(cutoff)
    factors = causal_factors(primes, step)
    r_basis, b_basis, c_basis, nesting_error, _ = PROOF_255.sonin_bases(
        size, step, intersection_tolerance
    )
    e_basis = np.concatenate([r_basis, b_basis], axis=1)
    e_projection = projection(e_basis)
    b_projection = projection(b_basis)
    identity = np.eye(size, dtype=complex)
    transport = apply_causal_transport(identity, factors)
    inverse_transport = apply_causal_inverse(identity, factors)
    inverse_error = float(
        np.linalg.norm(inverse_transport @ transport - identity, ord=2)
    )

    transported_r = transport @ r_basis
    transported_b = transport @ b_basis
    r_metric = transported_r.conj().T @ transported_r
    cross_metric = transported_r.conj().T @ transported_b
    graph_coordinates = np.linalg.solve(r_metric, cross_metric)
    schur_coordinates = b_basis - r_basis @ graph_coordinates
    generator = transport @ schur_coordinates
    polar = PROOF_255.polar_data(generator)
    band_projection = (
        np.asarray(polar["isometry"])
        @ np.asarray(polar["isometry"]).conj().T
    )

    inverse_metric = inverse_transport @ inverse_transport.conj().T
    c_metric = c_basis.conj().T @ inverse_metric @ c_basis
    cb_metric = c_basis.conj().T @ inverse_metric @ b_basis
    shorted_coframe = b_basis - c_basis @ np.linalg.solve(
        c_metric, cb_metric
    )

    inverse_b = inverse_transport @ b_basis
    oblique_coframe = transport @ e_projection @ inverse_b
    restricted_inverse = c_basis.conj().T @ inverse_transport @ c_basis
    triangular_coframe = b_basis - c_basis @ np.linalg.solve(
        restricted_inverse,
        c_basis.conj().T @ inverse_transport @ b_basis,
    )

    reordered_metric = inverse_transport.conj().T @ inverse_transport
    reordered_c_metric = c_basis.conj().T @ reordered_metric @ c_basis
    reordered_cb_metric = c_basis.conj().T @ reordered_metric @ b_basis
    reordered_shorted_coframe = b_basis - c_basis @ np.linalg.solve(
        reordered_c_metric, reordered_cb_metric
    )

    detector, row_residual = compact_toeplitz_detector(
        size, step, root_width
    )
    detector_b = b_basis.conj().T @ detector @ b_basis
    intrinsic_defect = (
        detector @ schur_coordinates
        - schur_coordinates @ detector_b
    )
    true_response = np.trace(
        shorted_coframe.conj().T @ intrinsic_defect
    )
    oblique_response = np.trace(
        oblique_coframe.conj().T @ intrinsic_defect
    )
    triangular_response = np.trace(
        triangular_coframe.conj().T @ intrinsic_defect
    )
    hard_linear = -np.trace(
        b_basis.conj().T
        @ detector
        @ r_basis
        @ graph_coordinates
    )
    coframe_correction = np.trace(
        (shorted_coframe - b_basis).conj().T @ intrinsic_defect
    )
    direct_response = np.trace(
        detector @ (band_projection - b_projection)
    )

    coordinates = (np.arange(size) - size // 2) * step
    central_mask = np.diag(
        (np.abs(coordinates) <= size * step / 4.0).astype(float)
    )
    transport_commutator = detector @ transport - transport @ detector
    central_commutator_norm = float(
        np.linalg.norm(
            central_mask @ transport_commutator @ central_mask,
            ord="fro",
        )
    )

    normality_scale = max(
        float(np.linalg.norm(inverse_metric, ord="fro")), 1e-15
    )
    inverse_metric_reordered = (
        inverse_transport.conj().T @ inverse_transport
    )
    return {
        "size": float(size),
        "step": step,
        "half_domain": size * step / 2.0,
        "cutoff": float(cutoff),
        "prime_count": float(len(primes)),
        "sonin_rank": float(r_basis.shape[1]),
        "nesting_error": nesting_error,
        "row_residual": row_residual,
        "inverse_error": inverse_error,
        "normality_error": float(
            np.linalg.norm(
                inverse_metric - inverse_metric_reordered, ord="fro"
            )
            / normality_scale
        ),
        "shorted_oblique_error": relative_error(
            shorted_coframe, oblique_coframe
        ),
        "reordered_shorted_oblique_error": relative_error(
            reordered_shorted_coframe, oblique_coframe
        ),
        "triangular_oblique_error": relative_error(
            triangular_coframe, oblique_coframe
        ),
        "transport_commutator_error": relative_error(
            detector @ transport, transport @ detector
        ),
        "central_commutator_norm": central_commutator_norm,
        "true_response": float(true_response.real),
        "oblique_response": float(oblique_response.real),
        "triangular_response": float(triangular_response.real),
        "direct_response": float(direct_response.real),
        "true_transport_deletion_error": abs(
            true_response - direct_response
        )
        / max(abs(direct_response), 1.0),
        "triangular_transport_deletion_error": abs(
            triangular_response - direct_response
        )
        / max(abs(direct_response), 1.0),
        "hard_linear": float(hard_linear.real),
        "coframe_correction": float(coframe_correction.real),
        "response_split_error": abs(
            hard_linear + coframe_correction - true_response
        )
        / max(abs(true_response), 1.0),
        "true_dual_norm": float(
            np.linalg.norm(shorted_coframe, ord=2)
        ),
        "oblique_dual_norm": float(
            np.linalg.norm(oblique_coframe, ord=2)
        ),
        "graph_norm": float(np.linalg.norm(graph_coordinates, ord=2)),
    }


def parse_configurations(raw: str) -> list[tuple[int, float]]:
    result: list[tuple[int, float]] = []
    for item in raw.split(","):
        size_text, step_text = item.split(":", maxsplit=1)
        size = int(size_text)
        step = float(step_text)
        if size < 64 or size % 2 or step <= 0.0:
            raise ValueError("configurations require positive even sizes")
        result.append((size, step))
    if not result:
        raise ValueError("at least one finite configuration is required")
    return result


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--triangular-size", type=int, default=24)
    parser.add_argument("--seed", type=int, default=256)
    parser.add_argument("--root-width", type=float, default=0.96)
    parser.add_argument("--cutoff", type=int, default=97)
    parser.add_argument(
        "--configurations",
        default="192:0.08,208:0.08,288:0.06,320:0.05",
    )
    parser.add_argument("--causal-configuration", default="320:0.05")
    parser.add_argument("--intersection-tolerance", type=float, default=1e-8)
    parser.add_argument("--max-algebra-error", type=float, default=2e-10)
    args = parser.parse_args()

    if args.triangular_size < 8 or args.triangular_size % 4:
        raise ValueError("triangular-size must be a multiple of four")
    if args.cutoff < 2 or args.root_width <= 0.0:
        raise ValueError("cutoff and root-width must be positive")

    triangular = triangular_factor_certificate(
        args.triangular_size, args.seed
    )
    configurations = parse_configurations(args.configurations)
    rows = [
        finite_sonin_row(
            size,
            step,
            args.root_width,
            args.cutoff,
            args.intersection_tolerance,
        )
        for size, step in configurations
    ]
    causal_size, causal_step = parse_configurations(
        args.causal_configuration
    )[0]
    causal = causal_sonin_row(
        causal_size,
        causal_step,
        args.root_width,
        args.cutoff,
        args.intersection_tolerance,
    )

    triangular_errors = [
        value
        for key, value in triangular.items()
        if key.endswith("_error")
    ]
    maximum_triangular_error = max(triangular_errors)
    maximum_split_error = max(
        max(
            row["hard_linear_identity_error"],
            row["response_split_error"],
            row["complete_imaginary"],
        )
        for row in rows
    )

    print("identity=one-sided inverse-metric shorting collapse")
    print("status=exact triangular algebra plus finite Sonin diagnostic")
    print(f"maximum_triangular_error={maximum_triangular_error:.12e}")
    print(f"maximum_response_split_error={maximum_split_error:.12e}")
    print("triangular_factor_table=BEGIN")
    for key, value in triangular.items():
        print(f"{key}={value:.12e}")
    print("triangular_factor_table=END")
    print("finite_sonin_split_table=BEGIN")
    for row in rows:
        print(
            f"size={int(row['size'])} "
            f"step={row['step']:.8f} "
            f"half_domain={row['half_domain']:.8f} "
            f"cutoff={int(row['cutoff'])} "
            f"prime_count={int(row['prime_count'])} "
            f"sonin_rank={int(row['sonin_rank'])} "
            f"log_condition={row['log_condition']:.12e} "
            f"collapse_error={row['coframe_collapse_error']:.12e} "
            f"hard={row['hard_linear']:.12e} "
            f"correction={row['coframe_correction']:.12e} "
            f"complete={row['complete_response']:.12e} "
            f"graph_norm={row['graph_norm']:.12e} "
            f"hard_abs={row['hard_linear_abs']:.12e} "
            f"correction_abs={row['coframe_correction_abs']:.12e} "
            f"dual_norm={row['dual_coordinate_norm']:.12e} "
            f"oblique_norm={row['oblique_coframe_norm']:.12e} "
            f"inverse_crossing={row['inverse_crossing_norm']:.12e} "
            f"transport_crossing={row['transport_crossing_norm']:.12e} "
            f"split_error={row['response_split_error']:.3e}"
        )
    print("finite_sonin_split_table=END")
    print("causal_sonin_table=BEGIN")
    for key, value in causal.items():
        print(f"{key}={value:.12e}")
    print("causal_sonin_table=END")

    if maximum_triangular_error > args.max_algebra_error:
        raise RuntimeError("triangular spectral-factor certificate failed")
    if maximum_split_error > args.max_algebra_error:
        raise RuntimeError("finite Sonin response split failed")
    if causal["inverse_error"] > args.max_algebra_error:
        raise RuntimeError("causal Euler inverse certificate failed")
    if causal["triangular_oblique_error"] > args.max_algebra_error:
        raise RuntimeError("causal triangular coframe identity failed")
    if causal["response_split_error"] > args.max_algebra_error:
        raise RuntimeError("causal response split failed")

    print("certificate=PASS")
    print("preserved_halfline_factorization_verdict=EXACT")
    print("conditioned_inverse_collapse_verdict=EXACT")
    print("hard_linear_two_crossing_split_verdict=EXACT")
    print("periodic_coframe_collapse_verdict=DIAGNOSTIC_ONLY")
    print("causal_finite_section_verdict=OUTER_BOUNDARY_DIAGNOSTIC")
    print("continuous_hard_linear_bound=OPEN")
    print("uniform_detector_bound=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
