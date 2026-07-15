#!/usr/bin/env python3
"""Certificate for the two-boundary synchronized Sonin graph flow.

Proof 256 leaves the endpoint channel

    -Tr_B(B W R L),  L = (R H R)^-1 R H B.

For the second support projection Q with R <= Q, its detector crossing splits
as

    B W R = B Q W R + B (I-Q) [W,Q] R.

In the exact two-projection geometry, (B Q)(B Q)* is the compact prolate
remainder.  Along a differentiable transport T_t, the graph coordinate obeys

    L_t' = A_t^-1 R H_t' Z_t
         = A_t^-1/2 V_t* K_t G_t,

and V_t* G_t = 0 deletes every scalar part of K_t.

This script separates exact finite-dimensional algebra from a periodic Sonin
diagnostic.  The diagnostic tests identities and growth; it is not a
continuous trace-ideal theorem or an RH argument.
"""

from __future__ import annotations

import argparse
import importlib.util
import math
from pathlib import Path
from types import ModuleType

import numpy as np


def load_probe(number: int, name: str) -> ModuleType:
    path = Path(__file__).with_name(f"{number}_{name}_probe.py")
    spec = importlib.util.spec_from_file_location(f"proof_{number}", path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path.name}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


PROOF_256 = load_probe(256, "one_sided_shorting_collapse")
PROOF_255 = PROOF_256.PROOF_255
PROOF_252 = PROOF_256.PROOF_252
PROOF_251 = PROOF_256.PROOF_251


def projection(columns: np.ndarray) -> np.ndarray:
    return columns @ columns.conj().T


def relative_error(actual: np.ndarray, expected: np.ndarray) -> float:
    denominator = max(float(np.linalg.norm(expected, ord="fro")), 1e-15)
    return float(np.linalg.norm(actual - expected, ord="fro") / denominator)


def scalar_relative_error(actual: complex, expected: complex) -> float:
    return float(abs(actual - expected) / max(abs(expected), 1.0))


def relative_norm(matrix: np.ndarray, scale: np.ndarray) -> float:
    denominator = max(float(np.linalg.norm(scale, ord="fro")), 1e-15)
    return float(np.linalg.norm(matrix, ord="fro") / denominator)


def selector_basis(size: int, start: int, stop: int) -> np.ndarray:
    basis = np.zeros((size, stop - start), dtype=complex)
    basis[np.arange(start, stop), np.arange(stop - start)] = 1.0
    return basis


def inverse_square_root(matrix: np.ndarray) -> np.ndarray:
    hermitian = (matrix + matrix.conj().T) / 2.0
    values, vectors = np.linalg.eigh(hermitian)
    if float(values.min()) <= 0.0:
        raise RuntimeError("positive metric lost invertibility")
    return vectors @ np.diag(values ** -0.5) @ vectors.conj().T


def nuclear_norm(matrix: np.ndarray) -> float:
    return float(np.linalg.svd(matrix, compute_uv=False).sum())


def generic_two_projection_certificate(
    size: int, seed: int
) -> dict[str, float]:
    if size < 12 or size % 4:
        raise ValueError("generic size must be a multiple of four")
    rng = np.random.default_rng(seed)
    block = size // 4
    r_basis = selector_basis(size, 0, block)
    b_basis = selector_basis(size, block, 2 * block)
    c_basis = selector_basis(size, 2 * block, 3 * block)
    extra_basis = selector_basis(size, 3 * block, size)
    e_basis = np.concatenate([r_basis, b_basis], axis=1)

    angles = np.linspace(0.31, 1.17, block)
    q_generic = (
        b_basis @ np.diag(np.cos(angles))
        + c_basis @ np.diag(np.sin(angles))
    )
    q_basis = np.concatenate([r_basis, q_generic, extra_basis], axis=1)
    r_projection = projection(r_basis)
    b_projection = projection(b_basis)
    e_projection = projection(e_basis)
    q_projection = projection(q_basis)
    identity = np.eye(size, dtype=complex)

    random = rng.normal(size=(size, size)) + 1j * rng.normal(
        size=(size, size)
    )
    detector = (random + random.conj().T) / 2.0
    graph = rng.normal(size=(block, block)) + 1j * rng.normal(
        size=(block, block)
    )

    hard = -np.trace(
        b_basis.conj().T @ detector @ r_basis @ graph
    )
    prolate = -np.trace(
        b_basis.conj().T
        @ q_projection
        @ detector
        @ r_basis
        @ graph
    )
    raw_crossing = -np.trace(
        b_basis.conj().T
        @ (identity - q_projection)
        @ detector
        @ r_basis
        @ graph
    )
    commutator = detector @ q_projection - q_projection @ detector
    commutator_crossing = -np.trace(
        b_basis.conj().T
        @ (identity - q_projection)
        @ commutator
        @ r_basis
        @ graph
    )

    prolate_owner = e_projection @ q_projection @ e_projection - r_projection
    prolate_square = (
        b_projection @ q_projection @ q_projection @ b_projection
    )
    flow_random = rng.normal(size=(size, size)) + 1j * rng.normal(
        size=(size, size)
    )
    flow_generator = (
        flow_random
        - (identity - q_projection) @ flow_random @ q_projection
    )
    outer_crossing = (
        (identity - e_projection) @ flow_generator @ b_projection
    )
    inner_crossing = (
        r_projection @ flow_generator.conj().T @ b_projection
    )
    factored_inner_crossing = (
        r_projection
        @ flow_generator.conj().T
        @ q_projection
        @ b_projection
    )
    nested_flow = outer_crossing - inner_crossing
    factored_nested_flow = outer_crossing - factored_inner_crossing
    shifted_generator = flow_generator + (2.6 - 1.9j) * identity
    shifted_nested_flow = (
        (identity - e_projection) @ shifted_generator @ b_projection
        - r_projection
        @ shifted_generator.conj().T
        @ q_projection
        @ b_projection
    )
    expected_spectrum = np.diag(np.cos(angles) ** 2)
    return {
        "e_nesting_error": relative_error(
            e_projection @ r_projection, r_projection
        ),
        "q_nesting_error": relative_error(
            q_projection @ r_projection, r_projection
        ),
        "prolate_owner_error": relative_error(
            prolate_owner, prolate_square
        ),
        "prolate_spectrum_error": relative_error(
            b_basis.conj().T @ prolate_square @ b_basis,
            expected_spectrum,
        ),
        "raw_split_error": scalar_relative_error(
            prolate + raw_crossing, hard
        ),
        "commutator_rewrite_error": scalar_relative_error(
            commutator_crossing, raw_crossing
        ),
        "complete_split_error": scalar_relative_error(
            prolate + commutator_crossing, hard
        ),
        "flow_q_invariance_error": float(
            np.linalg.norm(
                (identity - q_projection)
                @ flow_generator
                @ q_projection,
                ord="fro",
            )
        ),
        "inner_prolate_factor_error": relative_error(
            inner_crossing, factored_inner_crossing
        ),
        "nested_flow_factor_error": relative_error(
            nested_flow, factored_nested_flow
        ),
        "nested_flow_scalar_gauge_error": relative_error(
            shifted_nested_flow, nested_flow
        ),
        "prolate_trace_norm": nuclear_norm(
            b_projection @ q_projection
        ),
        "hard_abs": float(abs(hard)),
    }


def generic_transport(
    generator: np.ndarray, parameter: float
) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    identity = np.eye(len(generator), dtype=complex)
    transport = identity + parameter * generator
    derivative = generator
    inverse = np.linalg.inv(transport)
    right_generator = derivative @ inverse
    return transport, derivative, right_generator


def graph_data(
    transport: np.ndarray,
    derivative: np.ndarray,
    right_generator: np.ndarray,
    r_basis: np.ndarray,
    b_basis: np.ndarray,
) -> dict[str, np.ndarray]:
    metric = transport.conj().T @ transport
    metric_derivative = (
        derivative.conj().T @ transport
        + transport.conj().T @ derivative
    )
    r_metric = r_basis.conj().T @ metric @ r_basis
    cross_metric = r_basis.conj().T @ metric @ b_basis
    graph = np.linalg.solve(r_metric, cross_metric)
    schur = b_basis - r_basis @ graph
    graph_derivative = np.linalg.solve(
        r_metric,
        r_basis.conj().T @ metric_derivative @ schur,
    )

    r_inverse_square_root = inverse_square_root(r_metric)
    r_isometry = transport @ r_basis @ r_inverse_square_root
    schur_generator = transport @ schur
    selfadjoint_generator = (
        right_generator.conj().T + right_generator
    )
    frame_derivative = (
        r_inverse_square_root
        @ r_isometry.conj().T
        @ selfadjoint_generator
        @ schur_generator
    )
    return {
        "metric": metric,
        "metric_derivative": metric_derivative,
        "r_metric": r_metric,
        "graph": graph,
        "schur": schur,
        "graph_derivative": graph_derivative,
        "frame_derivative": frame_derivative,
        "r_inverse_square_root": r_inverse_square_root,
        "r_isometry": r_isometry,
        "schur_generator": schur_generator,
        "selfadjoint_generator": selfadjoint_generator,
    }


def generic_graph_flow_certificate(
    size: int, seed: int, parameter: float, finite_difference: float
) -> dict[str, float]:
    if size < 12 or size % 3:
        raise ValueError("flow size must be a multiple of three")
    rng = np.random.default_rng(seed + 1)
    block = size // 3
    r_basis = selector_basis(size, 0, block)
    b_basis = selector_basis(size, block, 2 * block)

    random = rng.normal(size=(size, size)) + 1j * rng.normal(
        size=(size, size)
    )
    random /= max(float(np.linalg.norm(random, ord=2)), 1e-15)
    generator = 0.24 * random
    transport, derivative, right_generator = generic_transport(
        generator, parameter
    )
    data = graph_data(
        transport,
        derivative,
        right_generator,
        r_basis,
        b_basis,
    )

    plus_transport, plus_derivative, plus_right = generic_transport(
        generator, parameter + finite_difference
    )
    minus_transport, minus_derivative, minus_right = generic_transport(
        generator, parameter - finite_difference
    )
    plus_graph = graph_data(
        plus_transport,
        plus_derivative,
        plus_right,
        r_basis,
        b_basis,
    )["graph"]
    minus_graph = graph_data(
        minus_transport,
        minus_derivative,
        minus_right,
        r_basis,
        b_basis,
    )["graph"]
    finite_difference_graph = (
        np.asarray(plus_graph) - np.asarray(minus_graph)
    ) / (2.0 * finite_difference)

    r_isometry = np.asarray(data["r_isometry"])
    schur_generator = np.asarray(data["schur_generator"])
    scalar = 3.7 - 1.4j
    shifted_selfadjoint = (
        np.asarray(data["selfadjoint_generator"])
        + 2.0 * scalar.real * np.eye(size, dtype=complex)
    )
    shifted_frame = (
        np.asarray(data["r_inverse_square_root"])
        @ r_isometry.conj().T
        @ shifted_selfadjoint
        @ schur_generator
    )
    return {
        "metric_formula_error": relative_error(
            np.asarray(data["metric_derivative"]),
            transport.conj().T
            @ np.asarray(data["selfadjoint_generator"])
            @ transport,
        ),
        "graph_frame_error": relative_error(
            np.asarray(data["graph_derivative"]),
            np.asarray(data["frame_derivative"]),
        ),
        "finite_difference_error": relative_error(
            finite_difference_graph,
            np.asarray(data["graph_derivative"]),
        ),
        "frame_orthogonality_error": float(
            np.linalg.norm(
                r_isometry.conj().T @ schur_generator, ord="fro"
            )
        ),
        "scalar_gauge_error": relative_error(
            shifted_frame, np.asarray(data["frame_derivative"])
        ),
        "r_isometry_error": relative_error(
            r_isometry.conj().T @ r_isometry,
            np.eye(block, dtype=complex),
        ),
    }


def transported_basis(
    transport: np.ndarray, basis: np.ndarray
) -> np.ndarray:
    result, _ = np.linalg.qr(transport @ basis, mode="reduced")
    return result


def generic_q_preserving_flow_certificate(
    size: int, seed: int, parameter: float, finite_difference: float
) -> dict[str, float]:
    if size < 12 or size % 4:
        raise ValueError("Q-preserving size must be a multiple of four")
    rng = np.random.default_rng(seed + 2)
    block = size // 4
    r_basis = selector_basis(size, 0, block)
    b_basis = selector_basis(size, block, 2 * block)
    c_basis = selector_basis(size, 2 * block, 3 * block)
    extra_basis = selector_basis(size, 3 * block, size)
    e_basis = np.concatenate([r_basis, b_basis], axis=1)
    angles = np.linspace(0.27, 1.09, block)
    q_generic = (
        b_basis @ np.diag(np.cos(angles))
        + c_basis @ np.diag(np.sin(angles))
    )
    q_basis = np.concatenate([r_basis, q_generic, extra_basis], axis=1)
    q_projection = projection(q_basis)
    identity = np.eye(size, dtype=complex)

    raw_generator = rng.normal(size=(size, size)) + 1j * rng.normal(
        size=(size, size)
    )
    raw_generator /= max(
        float(np.linalg.norm(raw_generator, ord=2)), 1e-15
    )
    generator = 0.19 * (
        raw_generator
        - (identity - q_projection)
        @ raw_generator
        @ q_projection
    )

    def flow_at(value: float) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
        transport = identity + value * generator
        inverse = np.linalg.inv(transport)
        right_generator = generator @ inverse
        e_columns = transported_basis(transport, e_basis)
        r_columns = transported_basis(transport, r_basis)
        e_projection = projection(e_columns)
        r_projection = projection(r_columns)
        return e_projection, r_projection, right_generator

    e_projection, r_projection, right_generator = flow_at(parameter)
    band_projection = e_projection - r_projection
    plus_e, plus_r, _ = flow_at(parameter + finite_difference)
    minus_e, minus_r, _ = flow_at(parameter - finite_difference)
    finite_difference_derivative = (
        (plus_e - plus_r) - (minus_e - minus_r)
    ) / (2.0 * finite_difference)

    e_columns = transported_basis(
        identity + parameter * generator, e_basis
    )
    r_columns = transported_basis(
        identity + parameter * generator, r_basis
    )
    direct_derivative = PROOF_252.projection_derivative(
        e_projection, e_columns, right_generator
    ) - PROOF_252.projection_derivative(
        r_projection, r_columns, right_generator
    )
    outer_crossing = (
        (identity - e_projection)
        @ right_generator
        @ band_projection
    )
    inner_crossing = (
        r_projection
        @ right_generator.conj().T
        @ band_projection
    )
    factored_inner = (
        r_projection
        @ right_generator.conj().T
        @ q_projection
        @ band_projection
    )
    crossing = outer_crossing - inner_crossing
    factored_crossing = outer_crossing - factored_inner
    crossing_derivative = crossing + crossing.conj().T
    factored_derivative = factored_crossing + factored_crossing.conj().T

    shifted_generator = right_generator + (3.1 - 0.8j) * identity
    shifted_crossing = (
        (identity - e_projection)
        @ shifted_generator
        @ band_projection
        - r_projection
        @ shifted_generator.conj().T
        @ q_projection
        @ band_projection
    )
    shifted_derivative = shifted_crossing + shifted_crossing.conj().T
    return {
        "q_generator_invariance_error": relative_norm(
            (identity - q_projection)
            @ right_generator
            @ q_projection,
            right_generator @ q_projection,
        ),
        "transported_r_q_nesting_error": relative_error(
            q_projection @ r_projection, r_projection
        ),
        "inner_prolate_factor_error": relative_error(
            inner_crossing, factored_inner
        ),
        "nested_flow_formula_error": relative_error(
            direct_derivative, crossing_derivative
        ),
        "nested_flow_prolate_factor_error": relative_error(
            crossing_derivative, factored_derivative
        ),
        "nested_flow_scalar_gauge_error": relative_error(
            shifted_derivative, factored_derivative
        ),
        "nested_flow_finite_difference_error": relative_error(
            finite_difference_derivative, direct_derivative
        ),
    }


def second_support_projection(size: int, step: float) -> np.ndarray:
    coordinates = (np.arange(size) - size // 2) * step
    frequencies = 2.0 * np.pi * np.fft.fftfreq(size, d=step)
    scattering = PROOF_251.archimedean_scattering(frequencies)
    identity = np.eye(size, dtype=complex)
    scattering_operator = np.fft.ifft(
        scattering[:, None] * np.fft.fft(identity, axis=0), axis=0
    )
    negative = np.diag((coordinates < 0.0).astype(float))
    result = scattering_operator.conj().T @ negative @ scattering_operator
    return (result + result.conj().T) / 2.0


def normalized_transport(
    factors: list[dict[str, object]], parameter: float
) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    if not factors:
        raise ValueError("at least one finite-place factor is required")
    size = len(np.asarray(factors[0]["multiplier"]))
    multiplier = np.ones(size, dtype=complex)
    logarithmic_derivative = np.zeros(size, dtype=complex)
    for factor in factors:
        amplitude = float(factor["amplitude"])
        phase = np.asarray(factor["multiplier"])
        multiplier *= (
            (1.0 - parameter * amplitude * phase)
            / (1.0 - parameter * amplitude)
        )
        logarithmic_derivative += (
            -amplitude * phase / (1.0 - parameter * amplitude * phase)
            + amplitude / (1.0 - parameter * amplitude)
        )
    identity = np.eye(size, dtype=complex)
    transport = np.fft.ifft(
        multiplier[:, None] * np.fft.fft(identity, axis=0), axis=0
    )
    right_generator = np.fft.ifft(
        logarithmic_derivative[:, None]
        * np.fft.fft(identity, axis=0),
        axis=0,
    )
    derivative = right_generator @ transport
    return transport, derivative, right_generator


def sonin_cutoff_row(
    r_basis: np.ndarray,
    b_basis: np.ndarray,
    e_projection: np.ndarray,
    q_projection: np.ndarray,
    detector: np.ndarray,
    factors: list[dict[str, object]],
    quadrature_order: int,
) -> dict[str, float]:
    size = len(detector)
    identity = np.eye(size, dtype=complex)
    r_projection = projection(r_basis)
    b_projection = projection(b_basis)
    commutator = detector @ q_projection - q_projection @ detector

    endpoint_transport, endpoint_derivative, endpoint_right = (
        normalized_transport(factors, 1.0)
    )
    endpoint_data = graph_data(
        endpoint_transport,
        endpoint_derivative,
        endpoint_right,
        r_basis,
        b_basis,
    )
    endpoint_graph = np.asarray(endpoint_data["graph"])
    endpoint_schur = np.asarray(endpoint_data["schur"])
    endpoint_generator = endpoint_transport @ endpoint_schur
    endpoint_polar = PROOF_255.polar_data(endpoint_generator)
    endpoint_band_projection = (
        np.asarray(endpoint_polar["isometry"])
        @ np.asarray(endpoint_polar["isometry"]).conj().T
    )
    complete_response = np.trace(
        detector @ (endpoint_band_projection - b_projection)
    )
    hard = -np.trace(
        b_basis.conj().T @ detector @ r_basis @ endpoint_graph
    )
    prolate_endpoint = -np.trace(
        b_basis.conj().T
        @ q_projection
        @ detector
        @ r_basis
        @ endpoint_graph
    )
    raw_crossing_endpoint = -np.trace(
        b_basis.conj().T
        @ (identity - q_projection)
        @ detector
        @ r_basis
        @ endpoint_graph
    )
    commutator_endpoint = -np.trace(
        b_basis.conj().T
        @ (identity - q_projection)
        @ commutator
        @ r_basis
        @ endpoint_graph
    )

    nodes, weights = np.polynomial.legendre.leggauss(quadrature_order)
    integrated_graph = np.zeros_like(endpoint_graph)
    integrated_hard = 0.0j
    integrated_prolate = 0.0j
    integrated_raw_crossing = 0.0j
    integrated_commutator = 0.0j
    absolute_hard = 0.0
    absolute_prolate = 0.0
    absolute_raw_crossing = 0.0
    maximum_graph_frame_error = 0.0
    maximum_scalar_gauge_error = 0.0
    maximum_orthogonality_error = 0.0
    maximum_metric_minimum_violation = 0.0

    for node, weight in zip((nodes + 1.0) / 2.0, weights / 2.0):
        parameter = float(node)
        transport, derivative, right_generator = normalized_transport(
            factors, parameter
        )
        data = graph_data(
            transport,
            derivative,
            right_generator,
            r_basis,
            b_basis,
        )
        graph_derivative = np.asarray(data["graph_derivative"])
        frame_derivative = np.asarray(data["frame_derivative"])
        integrated_graph += weight * graph_derivative
        maximum_graph_frame_error = max(
            maximum_graph_frame_error,
            relative_error(graph_derivative, frame_derivative),
        )
        maximum_orthogonality_error = max(
            maximum_orthogonality_error,
            float(
                np.linalg.norm(
                    np.asarray(data["r_isometry"]).conj().T
                    @ np.asarray(data["schur_generator"]),
                    ord="fro",
                )
            ),
        )
        shifted_frame = (
            np.asarray(data["r_inverse_square_root"])
            @ np.asarray(data["r_isometry"]).conj().T
            @ (
                np.asarray(data["selfadjoint_generator"])
                + 4.6 * identity
            )
            @ np.asarray(data["schur_generator"])
        )
        maximum_scalar_gauge_error = max(
            maximum_scalar_gauge_error,
            relative_error(shifted_frame, frame_derivative),
        )
        metric_minimum = float(
            np.linalg.eigvalsh(
                (np.asarray(data["metric"]) + np.asarray(data["metric"]).conj().T)
                / 2.0
            ).min()
        )
        maximum_metric_minimum_violation = max(
            maximum_metric_minimum_violation, max(1.0 - metric_minimum, 0.0)
        )

        hard_integrand = -np.trace(
            b_basis.conj().T
            @ detector
            @ r_basis
            @ graph_derivative
        )
        prolate_integrand = -np.trace(
            b_basis.conj().T
            @ q_projection
            @ detector
            @ r_basis
            @ graph_derivative
        )
        raw_crossing_integrand = -np.trace(
            b_basis.conj().T
            @ (identity - q_projection)
            @ detector
            @ r_basis
            @ graph_derivative
        )
        commutator_integrand = -np.trace(
            b_basis.conj().T
            @ (identity - q_projection)
            @ commutator
            @ r_basis
            @ graph_derivative
        )
        integrated_hard += weight * hard_integrand
        integrated_prolate += weight * prolate_integrand
        integrated_raw_crossing += weight * raw_crossing_integrand
        integrated_commutator += weight * commutator_integrand
        absolute_hard += weight * abs(hard_integrand)
        absolute_prolate += weight * abs(prolate_integrand)
        absolute_raw_crossing += weight * abs(raw_crossing_integrand)

    prolate_owner = e_projection @ q_projection @ e_projection - r_projection
    prolate_square = b_projection @ q_projection @ b_projection
    transported_r_columns, _ = PROOF_252.orthonormalize(
        endpoint_transport @ r_basis
    )
    transported_r_projection = projection(transported_r_columns)
    endpoint_q_invariance = (
        (identity - q_projection) @ endpoint_right @ q_projection
    )
    endpoint_inner_crossing = (
        transported_r_projection
        @ endpoint_right.conj().T
        @ endpoint_band_projection
    )
    endpoint_factored_inner = (
        transported_r_projection
        @ endpoint_right.conj().T
        @ q_projection
        @ endpoint_band_projection
    )
    q_nesting_error = relative_error(
        q_projection @ r_projection, r_projection
    )
    return {
        "prime_count": float(len(factors)),
        "largest_prime": float(factors[-1]["prime"]),
        "q_nesting_error": q_nesting_error,
        "prolate_owner_error": relative_error(
            prolate_owner, prolate_square
        ),
        "prolate_square_root_error": relative_error(
            (b_projection @ q_projection)
            @ (b_projection @ q_projection).conj().T,
            prolate_square,
        ),
        "graph_endpoint_error": relative_error(
            integrated_graph, endpoint_graph
        ),
        "hard_endpoint_error": scalar_relative_error(
            integrated_hard, hard
        ),
        "raw_endpoint_split_error": scalar_relative_error(
            prolate_endpoint + raw_crossing_endpoint, hard
        ),
        "commutator_endpoint_split_error": scalar_relative_error(
            prolate_endpoint + commutator_endpoint, hard
        ),
        "integrated_raw_split_error": scalar_relative_error(
            integrated_prolate + integrated_raw_crossing,
            integrated_hard,
        ),
        "integrated_commutator_split_error": scalar_relative_error(
            integrated_prolate + integrated_commutator,
            integrated_hard,
        ),
        "maximum_graph_frame_error": maximum_graph_frame_error,
        "maximum_scalar_gauge_error": maximum_scalar_gauge_error,
        "maximum_orthogonality_error": maximum_orthogonality_error,
        "maximum_metric_minimum_violation": (
            maximum_metric_minimum_violation
        ),
        "transported_q_nesting_error": relative_error(
            q_projection @ transported_r_projection,
            transported_r_projection,
        ),
        "endpoint_q_generator_invariance_error": relative_norm(
            endpoint_q_invariance, endpoint_right @ q_projection
        ),
        "endpoint_inner_prolate_factor_error": relative_error(
            endpoint_inner_crossing, endpoint_factored_inner
        ),
        "hard": float(hard.real),
        "hard_imaginary": float(abs(hard.imag)),
        "prolate": float(prolate_endpoint.real),
        "raw_crossing": float(raw_crossing_endpoint.real),
        "commutator_crossing": float(commutator_endpoint.real),
        "two_crossing_correction": float(
            (complete_response - hard).real
        ),
        "complete_response": float(complete_response.real),
        "complete_imaginary": float(abs(complete_response.imag)),
        "graph_norm": float(np.linalg.norm(endpoint_graph, ord=2)),
        "absolute_hard_flow": absolute_hard,
        "absolute_prolate_flow": absolute_prolate,
        "absolute_raw_crossing_flow": absolute_raw_crossing,
        "prolate_leakage_trace_norm": nuclear_norm(
            b_projection @ q_projection
        ),
        "detector_second_crossing_trace_norm": nuclear_norm(
            (identity - q_projection) @ commutator @ r_projection
        ),
        "transported_prolate_trace_norm": nuclear_norm(
            endpoint_band_projection @ q_projection
        ),
    }


def parse_cutoffs(raw: str) -> list[int]:
    values = sorted({int(item) for item in raw.split(",") if item.strip()})
    if not values or values[0] < 2:
        raise ValueError("prime cutoffs must contain integers at least two")
    return values


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--generic-size", type=int, default=16)
    parser.add_argument("--flow-size", type=int, default=15)
    parser.add_argument("--seed", type=int, default=257)
    parser.add_argument("--flow-parameter", type=float, default=0.57)
    parser.add_argument("--finite-difference", type=float, default=1e-6)
    parser.add_argument("--size", type=int, default=192)
    parser.add_argument("--step", type=float, default=0.08)
    parser.add_argument("--root-width", type=float, default=0.96)
    parser.add_argument("--prime-cutoffs", default="2,3,5,11,29,97")
    parser.add_argument("--intersection-tolerance", type=float, default=1e-8)
    parser.add_argument("--quadrature-order", type=int, default=16)
    parser.add_argument("--max-algebra-error", type=float, default=2e-8)
    args = parser.parse_args()

    if args.size < 96 or args.size % 2:
        raise ValueError("Sonin size must be an even integer at least 96")
    if args.step <= 0.0 or args.root_width <= 0.0:
        raise ValueError("step and root-width must be positive")
    if args.quadrature_order < 8:
        raise ValueError("quadrature-order must be at least eight")

    generic = generic_two_projection_certificate(
        args.generic_size, args.seed
    )
    flow = generic_graph_flow_certificate(
        args.flow_size,
        args.seed,
        args.flow_parameter,
        args.finite_difference,
    )
    q_flow = generic_q_preserving_flow_certificate(
        args.generic_size,
        args.seed,
        args.flow_parameter,
        args.finite_difference,
    )

    cutoffs = parse_cutoffs(args.prime_cutoffs)
    primes = PROOF_252.primes_up_to(cutoffs[-1])
    factors = PROOF_252.make_factors(primes, args.size, args.step)
    r_basis, b_basis, _, nesting_error, top_eigenvalue = (
        PROOF_255.sonin_bases(
            args.size, args.step, args.intersection_tolerance
        )
    )
    coordinates = (np.arange(args.size) - args.size // 2) * args.step
    e_basis = PROOF_251.halfline_basis(coordinates)
    e_projection = projection(e_basis)
    q_projection = second_support_projection(args.size, args.step)
    detector, _, row_residual = PROOF_255.root_detector(
        args.size, args.step, args.root_width
    )
    rows = []
    for cutoff in cutoffs:
        active = [factor for factor in factors if int(factor["prime"]) <= cutoff]
        rows.append(
            sonin_cutoff_row(
                r_basis,
                b_basis,
                e_projection,
                q_projection,
                detector,
                active,
                args.quadrature_order,
            )
        )

    generic_errors = [
        value for key, value in generic.items() if key.endswith("_error")
    ]
    flow_errors = [
        value for key, value in flow.items() if key.endswith("_error")
    ]
    q_flow_errors = [
        value for key, value in q_flow.items() if key.endswith("_error")
    ]
    maximum_generic_error = max(generic_errors)
    maximum_flow_error = max(flow_errors)
    maximum_q_flow_error = max(q_flow_errors)
    strict_rows = [row for row in rows if int(row["largest_prime"]) <= 29]
    if not strict_rows:
        strict_rows = rows
    maximum_strict_flow_error = max(
        max(
            row["graph_endpoint_error"],
            row["hard_endpoint_error"],
            row["integrated_raw_split_error"],
            row["maximum_graph_frame_error"],
            row["maximum_scalar_gauge_error"],
        )
        for row in strict_rows
    )

    print("identity=two-boundary synchronized Sonin graph flow")
    print("status=exact algebra plus periodic Sonin death diagnostic")
    print(f"maximum_generic_error={maximum_generic_error:.12e}")
    print(f"maximum_generic_flow_error={maximum_flow_error:.12e}")
    print(f"maximum_q_preserving_flow_error={maximum_q_flow_error:.12e}")
    print(f"maximum_strict_sonin_flow_error={maximum_strict_flow_error:.12e}")
    print("generic_two_projection_table=BEGIN")
    for key, value in generic.items():
        print(f"{key}={value:.12e}")
    print("generic_two_projection_table=END")
    print("generic_graph_flow_table=BEGIN")
    for key, value in flow.items():
        print(f"{key}={value:.12e}")
    print("generic_graph_flow_table=END")
    print("generic_q_preserving_flow_table=BEGIN")
    for key, value in q_flow.items():
        print(f"{key}={value:.12e}")
    print("generic_q_preserving_flow_table=END")
    print("sonin_metadata=BEGIN")
    print(f"size={args.size}")
    print(f"step={args.step:.12e}")
    print(f"half_domain={args.size * args.step / 2.0:.12e}")
    print(f"sonin_rank={r_basis.shape[1]}")
    print(f"band_rank={b_basis.shape[1]}")
    print(f"nesting_error={nesting_error:.12e}")
    print(f"sonin_top_eigenvalue={top_eigenvalue:.12e}")
    print(f"root_row_residual={row_residual:.12e}")
    print("sonin_metadata=END")
    print("sonin_two_boundary_table=BEGIN")
    for row in rows:
        print(
            f"largest_prime={int(row['largest_prime'])} "
            f"prime_count={int(row['prime_count'])} "
            f"q_nesting={row['q_nesting_error']:.3e} "
            f"prolate_owner={row['prolate_owner_error']:.3e} "
            f"graph_endpoint={row['graph_endpoint_error']:.3e} "
            f"hard_endpoint={row['hard_endpoint_error']:.3e} "
            f"commutator_split={row['integrated_commutator_split_error']:.3e} "
            f"hard={row['hard']:.12e} "
            f"prolate={row['prolate']:.12e} "
            f"crossing={row['commutator_crossing']:.12e} "
            f"correction={row['two_crossing_correction']:.12e} "
            f"complete={row['complete_response']:.12e} "
            f"graph_norm={row['graph_norm']:.12e} "
            f"abs_flow={row['absolute_hard_flow']:.12e} "
            f"abs_prolate={row['absolute_prolate_flow']:.12e} "
            f"abs_crossing={row['absolute_raw_crossing_flow']:.12e} "
            f"prolate_trace_norm={row['prolate_leakage_trace_norm']:.12e} "
            f"transported_prolate={row['transported_prolate_trace_norm']:.12e} "
            f"crossing_trace_norm={row['detector_second_crossing_trace_norm']:.12e} "
            f"transported_q_nesting={row['transported_q_nesting_error']:.3e} "
            f"flow_prolate_factor={row['endpoint_inner_prolate_factor_error']:.3e}"
        )
    print("sonin_two_boundary_table=END")

    if maximum_generic_error > args.max_algebra_error:
        raise RuntimeError("generic two-projection certificate failed")
    if maximum_flow_error > args.max_algebra_error:
        raise RuntimeError("generic graph-flow certificate failed")
    if maximum_q_flow_error > args.max_algebra_error:
        raise RuntimeError("generic Q-preserving flow certificate failed")
    if maximum_strict_flow_error > args.max_algebra_error:
        raise RuntimeError("strict Sonin graph-flow certificate failed")

    print("certificate=PASS")
    print("prolate_square_root_factorization=EXACT")
    print("second_boundary_commutator_rewrite=EXACT")
    print("synchronized_graph_derivative=EXACT")
    print("scalar_generator_cancellation=EXACT")
    print("periodic_sonin_growth_verdict=DIAGNOSTIC_ONLY")
    print("uniform_polynomial_support_bound=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
