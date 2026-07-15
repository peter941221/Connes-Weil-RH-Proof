#!/usr/bin/env python3
"""Certificate for nested shorting cancellation and its polar owner.

For nested orthogonal projections R <= E, put B = E - R and C = I - E.
If T is invertible, H = T* T, and B_T is the orthogonal projection onto

    T Ran(E) intersect (T Ran(R))^perp,

then the Schur construction gives G with G*G = Sigma and

    B_T = G Sigma^-1 G*.

The corresponding oblique band projection A has the exact decomposition

    B_T = A A* - (A - B_T)(A - B_T)*.

The two large positive terms can be replaced by the polar isometry

    V = G Sigma^-1/2,  V*V = B,  VV* = B_T.

The default certificate verifies the algebra, a closed three-dimensional
conditioning guard, and the same cancellation in the finite Sonin geometry.
The finite sections are diagnostics, not continuous operator theorems.
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


PROOF_254 = load_probe(254, "shorted_markov_boundary_gate")
PROOF_253 = PROOF_254.load_proof_253()
PROOF_252 = PROOF_253.PROOF_252
PROOF_251 = PROOF_253.PROOF_251


def projection(columns: np.ndarray) -> np.ndarray:
    return columns @ columns.conj().T


def orthonormalize(columns: np.ndarray) -> np.ndarray:
    basis, _ = np.linalg.qr(columns, mode="reduced")
    return basis


def nuclear_norm(matrix: np.ndarray) -> float:
    return float(np.linalg.svd(matrix, compute_uv=False).sum())


def relative_matrix_error(actual: np.ndarray, expected: np.ndarray) -> float:
    denominator = max(float(np.linalg.norm(expected, ord="fro")), 1e-15)
    return float(np.linalg.norm(actual - expected, ord="fro") / denominator)


def relative_scalar_error(actual: complex, expected: complex) -> float:
    return float(abs(actual - expected) / max(abs(expected), 1e-15))


def make_selector_basis(size: int, start: int, stop: int) -> np.ndarray:
    basis = np.zeros((size, stop - start), dtype=complex)
    basis[np.arange(start, stop), np.arange(stop - start)] = 1.0
    return basis


def polar_data(matrix: np.ndarray) -> dict[str, np.ndarray]:
    left, singular_values, right_adjoint = np.linalg.svd(
        matrix, full_matrices=False
    )
    right = right_adjoint.conj().T
    modulus = (
        right * singular_values[None, :]
    ) @ right.conj().T
    inverse_modulus = (
        right * (1.0 / singular_values)[None, :]
    ) @ right.conj().T
    inverse_square = (
        right * (1.0 / singular_values**2)[None, :]
    ) @ right.conj().T
    return {
        "isometry": left @ right_adjoint,
        "modulus": modulus,
        "inverse_modulus": inverse_modulus,
        "inverse_square": inverse_square,
        "singular_values": singular_values,
    }


def nested_data(
    transport: np.ndarray,
    inverse_transport: np.ndarray,
    r_basis: np.ndarray,
    b_basis: np.ndarray,
    c_basis: np.ndarray,
) -> dict[str, np.ndarray]:
    size = len(transport)
    identity = np.eye(size, dtype=complex)
    r_projection = projection(r_basis)
    b_projection = projection(b_basis)
    e_basis = np.concatenate([r_basis, b_basis], axis=1)
    e_projection = projection(e_basis)

    transported_r_columns = transport @ r_basis
    transported_b_columns = transport @ b_basis
    r_metric = transported_r_columns.conj().T @ transported_r_columns
    cross_metric = transported_r_columns.conj().T @ transported_b_columns
    schur_coordinates = b_basis - (
        r_basis @ np.linalg.solve(r_metric, cross_metric)
    )
    generator = transport @ schur_coordinates
    sigma = generator.conj().T @ generator

    polar = polar_data(generator)
    isometry_coordinates = np.asarray(polar["isometry"])
    modulus = np.asarray(polar["modulus"])
    inverse_sigma = np.asarray(polar["inverse_square"])
    band_projection = isometry_coordinates @ isometry_coordinates.conj().T
    isometry = isometry_coordinates @ b_basis.conj().T

    transported_r_basis = orthonormalize(transported_r_columns)
    transported_e_basis = orthonormalize(transport @ e_basis)
    transported_r_projection = projection(transported_r_basis)
    transported_e_projection = projection(transported_e_basis)
    direct_band_projection = (
        transported_e_projection - transported_r_projection
    )

    oblique_e = transport @ e_projection @ inverse_transport
    oblique_band = (
        generator @ b_basis.conj().T @ inverse_transport
    )

    inverse_metric = inverse_transport @ inverse_transport.conj().T
    b_markov = b_basis.conj().T @ inverse_metric @ b_basis
    bc_markov = b_basis.conj().T @ inverse_metric @ c_basis
    c_markov = c_basis.conj().T @ inverse_metric @ c_basis
    shorting_defect = (
        bc_markov @ np.linalg.solve(c_markov, bc_markov.conj().T)
    )
    shorted_inverse = b_markov - shorting_defect
    dual_coordinates = b_basis - (
        c_basis @ np.linalg.solve(c_markov, bc_markov.conj().T)
    )
    dual_frame = inverse_transport.conj().T @ dual_coordinates

    return {
        "identity": identity,
        "r_projection": r_projection,
        "b_projection": b_projection,
        "e_projection": e_projection,
        "generator": generator,
        "schur_coordinates": schur_coordinates,
        "sigma": sigma,
        "inverse_sigma": inverse_sigma,
        "modulus": modulus,
        "isometry_coordinates": isometry_coordinates,
        "isometry": isometry,
        "band_projection": band_projection,
        "direct_band_projection": direct_band_projection,
        "transported_r_projection": transported_r_projection,
        "oblique_e": oblique_e,
        "oblique_band": oblique_band,
        "inverse_metric": inverse_metric,
        "b_markov": b_markov,
        "shorting_defect": shorting_defect,
        "shorted_inverse": shorted_inverse,
        "dual_coordinates": dual_coordinates,
        "dual_frame": dual_frame,
        "singular_values": np.asarray(polar["singular_values"]),
    }


def sylvester_solution(modulus: np.ndarray, right_side: np.ndarray) -> np.ndarray:
    eigenvalues, eigenvectors = np.linalg.eigh(
        (modulus + modulus.conj().T) / 2.0
    )
    transformed = eigenvectors.conj().T @ right_side @ eigenvectors
    solution = transformed / (
        eigenvalues[:, None] + eigenvalues[None, :]
    )
    return eigenvectors @ solution @ eigenvectors.conj().T


def algebra_certificate(
    transport: np.ndarray,
    inverse_transport: np.ndarray,
    r_basis: np.ndarray,
    b_basis: np.ndarray,
    c_basis: np.ndarray,
    detector: np.ndarray,
) -> dict[str, float]:
    data = nested_data(
        transport,
        inverse_transport,
        r_basis,
        b_basis,
        c_basis,
    )
    identity = np.asarray(data["identity"])
    b_projection = np.asarray(data["b_projection"])
    generator = np.asarray(data["generator"])
    schur_coordinates = np.asarray(data["schur_coordinates"])
    sigma = np.asarray(data["sigma"])
    inverse_sigma = np.asarray(data["inverse_sigma"])
    modulus = np.asarray(data["modulus"])
    isometry_coordinates = np.asarray(data["isometry_coordinates"])
    isometry = np.asarray(data["isometry"])
    band_projection = np.asarray(data["band_projection"])
    direct_band_projection = np.asarray(data["direct_band_projection"])
    transported_r_projection = np.asarray(
        data["transported_r_projection"]
    )
    oblique_e = np.asarray(data["oblique_e"])
    oblique_band = np.asarray(data["oblique_band"])
    b_markov = np.asarray(data["b_markov"])
    shorting_defect = np.asarray(data["shorting_defect"])
    shorted_inverse = np.asarray(data["shorted_inverse"])
    dual_coordinates = np.asarray(data["dual_coordinates"])
    dual_frame = np.asarray(data["dual_frame"])
    singular_values = np.asarray(data["singular_values"])

    band_from_schur = generator @ inverse_sigma @ generator.conj().T
    expected_oblique_band = (
        identity - transported_r_projection
    ) @ oblique_e
    phase_defect = oblique_band - band_projection
    phase_square = oblique_band @ oblique_band.conj().T
    defect_square = phase_defect @ phase_defect.conj().T
    shorting_square = (
        generator @ shorting_defect @ generator.conj().T
    )
    metric = transport.conj().T @ transport
    dual_expected = generator @ inverse_sigma
    dual_band_projection = generator @ dual_frame.conj().T

    detector_b = b_basis.conj().T @ detector @ b_basis
    response_operator = (
        isometry_coordinates.conj().T
        @ detector
        @ isometry_coordinates
        - detector_b
    )
    intertwining_defect = (
        detector @ generator - generator @ detector_b
    )
    sylvester_right = (
        isometry_coordinates.conj().T @ intertwining_defect
        + intertwining_defect.conj().T @ isometry_coordinates
    )
    sylvester_left = (
        modulus @ response_operator + response_operator @ modulus
    )
    recovered_response = sylvester_solution(modulus, sylvester_right)

    direct_response = np.trace(
        detector @ (band_projection - b_projection)
    )
    polar_response = np.trace(response_operator)
    commutator_response = np.trace(
        isometry.conj().T
        @ (
            detector @ isometry
            - isometry @ b_projection @ detector @ b_projection
        )
    )
    dual_response = np.trace(
        dual_frame.conj().T @ detector @ generator - detector_b
    )
    intrinsic_response = np.trace(
        dual_coordinates.conj().T
        @ (detector @ schur_coordinates - schur_coordinates @ detector_b)
    )
    response_trace_scale = max(abs(direct_response), 1.0)

    response_nuclear = nuclear_norm(response_operator)
    intertwining_nuclear = nuclear_norm(intertwining_defect)
    minimum_modulus = float(singular_values.min())
    sylvester_bound = intertwining_nuclear / minimum_modulus

    return {
        "inverse_transport_error": float(
            np.linalg.norm(inverse_transport @ transport - identity, ord=2)
        ),
        "generator_gram_error": relative_matrix_error(
            generator.conj().T @ generator, sigma
        ),
        "band_schur_error": relative_matrix_error(
            band_from_schur, band_projection
        ),
        "band_direct_error": relative_matrix_error(
            direct_band_projection, band_projection
        ),
        "oblique_identity_error": relative_matrix_error(
            oblique_band, expected_oblique_band
        ),
        "oblique_idempotence_error": relative_matrix_error(
            oblique_band @ oblique_band, oblique_band
        ),
        "oblique_range_left_error": relative_matrix_error(
            band_projection @ oblique_band, oblique_band
        ),
        "oblique_range_right_error": relative_matrix_error(
            oblique_band @ band_projection, band_projection
        ),
        "shorting_inverse_error": relative_matrix_error(
            shorted_inverse, inverse_sigma
        ),
        "dual_frame_error": relative_matrix_error(
            dual_frame, dual_expected
        ),
        "dual_pairing_error": relative_matrix_error(
            generator.conj().T @ dual_frame,
            np.eye(generator.shape[1]),
        ),
        "dual_band_error": relative_matrix_error(
            dual_band_projection, band_projection
        ),
        "dual_metric_owner_error": relative_matrix_error(
            dual_coordinates,
            metric @ schur_coordinates @ inverse_sigma,
        ),
        "dual_coordinate_pairing_error": relative_matrix_error(
            dual_coordinates.conj().T @ schur_coordinates,
            np.eye(generator.shape[1]),
        ),
        "transport_commutator_error": relative_matrix_error(
            detector @ transport, transport @ detector
        ),
        "phase_shorting_error": relative_matrix_error(
            phase_square - band_projection, shorting_square
        ),
        "phase_defect_error": relative_matrix_error(
            phase_square - band_projection, defect_square
        ),
        "isometry_initial_error": relative_matrix_error(
            isometry.conj().T @ isometry, b_projection
        ),
        "isometry_final_error": relative_matrix_error(
            isometry @ isometry.conj().T, band_projection
        ),
        "response_polar_error": float(
            abs(direct_response - polar_response) / response_trace_scale
        ),
        "response_commutator_error": float(
            abs(direct_response - commutator_response)
            / response_trace_scale
        ),
        "response_dual_error": float(
            abs(direct_response - dual_response) / response_trace_scale
        ),
        "response_intrinsic_error": float(
            abs(direct_response - intrinsic_response)
            / response_trace_scale
        ),
        "sylvester_identity_error": relative_matrix_error(
            sylvester_left, sylvester_right
        ),
        "sylvester_solution_error": relative_matrix_error(
            recovered_response, response_operator
        ),
        "minimum_modulus": minimum_modulus,
        "response_nuclear_norm": response_nuclear,
        "intertwining_nuclear_norm": intertwining_nuclear,
        "sylvester_bound": sylvester_bound,
        "sylvester_bound_violation": max(
            response_nuclear - sylvester_bound, 0.0
        ),
        "oblique_norm": float(np.linalg.norm(oblique_band, ord=2)),
        "dual_frame_norm": float(np.linalg.norm(dual_frame, ord=2)),
        "dual_frame_contraction_violation": max(
            float(np.linalg.norm(dual_frame, ord=2)) - 1.0, 0.0
        ),
        "dual_coordinate_norm": float(
            np.linalg.norm(dual_coordinates, ord=2)
        ),
        "phase_trace": float(np.trace(detector @ phase_square).real),
        "defect_trace": float(np.trace(detector @ defect_square).real),
        "band_trace": float(np.trace(detector @ band_projection).real),
        "endpoint_response": float(direct_response.real),
        "shorting_minimum_eigenvalue": float(
            np.linalg.eigvalsh(
                (shorted_inverse + shorted_inverse.conj().T) / 2.0
            ).min()
        ),
        "shorting_defect_minimum_eigenvalue": float(
            np.linalg.eigvalsh(
                (shorting_defect + shorting_defect.conj().T) / 2.0
            ).min()
        ),
    }


def generic_certificate(size: int) -> dict[str, float]:
    factors = PROOF_254.parse_factors("2:1,3:3,5:7")
    transport, inverse_transport = PROOF_254.normalized_product(size, factors)
    r_rank = size // 4
    e_rank = size // 2
    r_basis = make_selector_basis(size, 0, r_rank)
    b_basis = make_selector_basis(size, r_rank, e_rank)
    c_basis = make_selector_basis(size, e_rank, size)
    shift = PROOF_254.cyclic_translation(size, 1)
    detector = (
        np.eye(size, dtype=complex)
        + 0.15 * (shift + shift.conj().T)
    )
    return algebra_certificate(
        transport,
        inverse_transport,
        r_basis,
        b_basis,
        c_basis,
        detector,
    )


def three_dimensional_row(kappa: float) -> dict[str, float]:
    transport = np.diag([1.0, kappa, 1.0]).astype(complex)
    inverse_transport = np.diag([1.0, 1.0 / kappa, 1.0]).astype(complex)
    e1 = np.array([[1.0], [0.0], [0.0]], dtype=complex)
    band = np.array([[0.0], [1.0], [1.0]], dtype=complex) / math.sqrt(2.0)
    complement = (
        np.array([[0.0], [-1.0], [1.0]], dtype=complex)
        / math.sqrt(2.0)
    )
    detector = np.diag([0.0, 1.0, 0.0]).astype(complex)
    data = nested_data(
        transport,
        inverse_transport,
        e1,
        band,
        complement,
    )
    oblique = np.asarray(data["oblique_band"])
    band_projection = np.asarray(data["band_projection"])
    isometry = np.asarray(data["isometry"])
    base_band = np.asarray(data["b_projection"])
    defect = oblique - band_projection

    block = oblique[1:, 1:]
    expected_block = 0.5 * np.array(
        [[1.0, kappa], [1.0 / kappa, 1.0]], dtype=complex
    )
    phase = float(
        np.trace(detector @ oblique @ oblique.conj().T).real
    )
    actual = float(np.trace(detector @ band_projection).real)
    defect_value = float(
        np.trace(detector @ defect @ defect.conj().T).real
    )
    base = float(np.trace(detector @ base_band).real)
    commutator_response = float(
        np.trace(
            isometry.conj().T
            @ (
                detector @ isometry
                - isometry @ base_band @ detector @ base_band
            )
        ).real
    )

    expected_phase = (1.0 + kappa**2) / 4.0
    expected_actual = kappa**2 / (kappa**2 + 1.0)
    expected_defect = (kappa**2 - 1.0) ** 2 / (
        4.0 * (kappa**2 + 1.0)
    )
    expected_response = (kappa**2 - 1.0) / (
        2.0 * (kappa**2 + 1.0)
    )

    metric_block = np.diag([kappa**-2, 1.0])
    physical_basis = np.array(
        [[1.0, -1.0], [1.0, 1.0]], dtype=complex
    ) / math.sqrt(2.0)
    physical_metric = (
        physical_basis.conj().T @ metric_block @ physical_basis
    )
    markov_identity = (1.0 + kappa**-2) / 2.0
    markov_swap = (1.0 - kappa**-2) / 2.0
    expected_metric = markov_identity * np.eye(2) + markov_swap * np.array(
        [[0.0, 1.0], [1.0, 0.0]]
    )

    formula_errors = [
        relative_matrix_error(block, expected_block),
        relative_scalar_error(phase, expected_phase),
        relative_scalar_error(actual, expected_actual),
        relative_scalar_error(defect_value, expected_defect),
        relative_scalar_error(actual - base, expected_response),
        relative_scalar_error(commutator_response, expected_response),
        relative_matrix_error(physical_metric, expected_metric),
    ]
    return {
        "kappa": kappa,
        "oblique_norm": float(np.linalg.norm(oblique, ord=2)),
        "isometry_norm": float(np.linalg.norm(isometry, ord=2)),
        "phase": phase,
        "defect": defect_value,
        "actual": actual,
        "base": base,
        "endpoint_response": actual - base,
        "commutator_response": commutator_response,
        "markov_identity": markov_identity,
        "markov_swap": markov_swap,
        "maximum_formula_error": max(formula_errors),
    }


def normalized_fourier_transport(
    primes: list[int], size: int, step: float
) -> tuple[np.ndarray, np.ndarray, float]:
    frequencies = np.fft.fftfreq(size, d=step)
    logarithm = np.zeros(size, dtype=complex)
    for prime in primes:
        amplitude = prime ** -0.5
        phase = np.exp(2j * np.pi * frequencies * math.log(prime))
        logarithm += np.log(1.0 - amplitude * phase) - math.log(
            1.0 - amplitude
        )
    multiplier = np.exp(logarithm)
    identity = np.eye(size, dtype=complex)
    transport = np.fft.ifft(
        multiplier[:, None] * np.fft.fft(identity, axis=0), axis=0
    )
    inverse_transport = np.fft.ifft(
        (1.0 / multiplier)[:, None] * np.fft.fft(identity, axis=0),
        axis=0,
    )
    log_condition = float(logarithm.real.max() - logarithm.real.min())
    return transport, inverse_transport, log_condition


def sonin_bases(
    size: int, step: float, intersection_tolerance: float
) -> tuple[np.ndarray, np.ndarray, np.ndarray, float, float]:
    coordinates = (np.arange(size) - size // 2) * step
    r_basis, sonin_eigenvalues = PROOF_251.sonin_basis(
        size, step, intersection_tolerance
    )
    e_basis = PROOF_251.halfline_basis(coordinates)
    r_coordinates = e_basis.conj().T @ r_basis
    complete, _ = np.linalg.qr(r_coordinates, mode="complete")
    b_basis = e_basis @ complete[:, r_basis.shape[1] :]
    negative_indices = np.flatnonzero(coordinates < 0.0)
    c_basis = np.zeros((size, len(negative_indices)), dtype=complex)
    c_basis[negative_indices, np.arange(len(negative_indices))] = 1.0
    nesting_error = float(
        np.linalg.norm(projection(e_basis) @ r_basis - r_basis, ord="fro")
    )
    return (
        r_basis,
        b_basis,
        c_basis,
        nesting_error,
        float(sonin_eigenvalues[-1]),
    )


def root_detector(size: int, step: float, root_width: float) -> tuple[np.ndarray, int, float]:
    root_size = int(round(root_width / step)) + 1
    root_weight, row_residual = PROOF_253.compact_root_weight(
        size, step, root_size
    )
    identity = np.eye(size, dtype=complex)
    detector = np.fft.ifft(
        root_weight[:, None] * np.fft.fft(identity, axis=0), axis=0
    )
    detector = (detector + detector.conj().T) / 2.0
    return detector, root_size, row_residual


def finite_sonin_rows(
    size: int,
    step: float,
    root_width: float,
    cutoffs: list[int],
    intersection_tolerance: float,
) -> tuple[list[dict[str, float]], dict[str, float]]:
    primes = PROOF_252.primes_up_to(max(cutoffs))
    r_basis, b_basis, c_basis, nesting_error, top_eigenvalue = sonin_bases(
        size, step, intersection_tolerance
    )
    detector, root_size, row_residual = root_detector(
        size, step, root_width
    )
    base_band = projection(b_basis)
    base_value = float(np.trace(detector @ base_band).real)
    rows: list[dict[str, float]] = []

    for cutoff in cutoffs:
        active_primes = [prime for prime in primes if prime <= cutoff]
        transport, inverse_transport, log_condition = (
            normalized_fourier_transport(active_primes, size, step)
        )
        data = nested_data(
            transport,
            inverse_transport,
            r_basis,
            b_basis,
            c_basis,
        )
        oblique = np.asarray(data["oblique_band"])
        band_projection = np.asarray(data["band_projection"])
        isometry_coordinates = np.asarray(data["isometry_coordinates"])
        shorting_defect = np.asarray(data["shorting_defect"])
        generator = np.asarray(data["generator"])
        schur_coordinates = np.asarray(data["schur_coordinates"])
        dual_coordinates = np.asarray(data["dual_coordinates"])
        dual_frame = np.asarray(data["dual_frame"])
        defect = oblique - band_projection

        phase_square = oblique @ oblique.conj().T
        defect_square = defect @ defect.conj().T
        shorting_square = (
            generator @ shorting_defect @ generator.conj().T
        )
        phase_value = float(np.trace(detector @ phase_square).real)
        defect_value = float(np.trace(detector @ defect_square).real)
        actual_value = float(np.trace(detector @ band_projection).real)
        canonical_value = float(
            np.trace(
                isometry_coordinates.conj().T
                @ detector
                @ isometry_coordinates
            ).real
        )
        cancellation_error = abs(
            phase_value - defect_value - actual_value
        )
        detector_b = b_basis.conj().T @ detector @ b_basis
        response_operator = (
            isometry_coordinates.conj().T
            @ detector
            @ isometry_coordinates
            - detector_b
        )
        intertwining_defect = (
            detector @ generator - generator @ detector_b
        )
        intrinsic_defect = (
            detector @ schur_coordinates
            - schur_coordinates @ detector_b
        )
        response_nuclear = nuclear_norm(response_operator)
        intertwining_nuclear = nuclear_norm(intertwining_defect)
        minimum_modulus = float(
            np.asarray(data["singular_values"]).min()
        )
        sylvester_bound = intertwining_nuclear / minimum_modulus
        dual_value = float(
            np.trace(
                dual_frame.conj().T @ detector @ generator
            ).real
        )
        intrinsic_value = float(
            np.trace(
                dual_coordinates.conj().T @ intrinsic_defect
                + detector_b
            ).real
        )
        rows.append(
            {
                "cutoff": float(cutoff),
                "prime_count": float(len(active_primes)),
                "log_condition": log_condition,
                "minimum_modulus": minimum_modulus,
                "oblique_norm": float(np.linalg.norm(oblique, ord=2)),
                "phase": phase_value,
                "defect": defect_value,
                "actual": actual_value,
                "base": base_value,
                "endpoint": actual_value - base_value,
                "canonical": canonical_value,
                "dual": dual_value,
                "intrinsic": intrinsic_value,
                "dual_frame_norm": float(
                    np.linalg.norm(dual_frame, ord=2)
                ),
                "dual_coordinate_norm": float(
                    np.linalg.norm(dual_coordinates, ord=2)
                ),
                "intrinsic_defect_nuclear": nuclear_norm(intrinsic_defect),
                "response_nuclear": response_nuclear,
                "intertwining_nuclear": intertwining_nuclear,
                "sylvester_bound": sylvester_bound,
                "sylvester_bound_ratio": response_nuclear
                / max(sylvester_bound, 1e-15),
                "cancellation_error": cancellation_error,
                "cancellation_relative_error": cancellation_error
                / max(abs(actual_value), 1.0),
                "defect_factor_error": relative_matrix_error(
                    defect_square, shorting_square
                ),
                "isometry_final_error": relative_matrix_error(
                    isometry_coordinates
                    @ isometry_coordinates.conj().T,
                    band_projection,
                ),
                "dual_frame_error": relative_matrix_error(
                    dual_frame, generator @ np.asarray(data["inverse_sigma"])
                ),
                "dual_value_error": abs(dual_value - actual_value)
                / max(abs(actual_value), 1.0),
                "intrinsic_value_error": abs(
                    intrinsic_value - actual_value
                )
                / max(abs(actual_value), 1.0),
            }
        )

    metadata = {
        "sonin_rank": float(r_basis.shape[1]),
        "sonin_top_eigenvalue": top_eigenvalue,
        "nesting_error": nesting_error,
        "root_size": float(root_size),
        "root_width": (root_size - 1) * step,
        "row_residual": row_residual,
        "base_value": base_value,
    }
    return rows, metadata


def parse_cutoffs(raw: str) -> list[int]:
    cutoffs = sorted({int(item) for item in raw.split(",") if item.strip()})
    if not cutoffs or cutoffs[0] < 2:
        raise ValueError("cutoffs must contain integers at least two")
    return cutoffs


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--generic-size", type=int, default=32)
    parser.add_argument("--size", type=int, default=192)
    parser.add_argument("--step", type=float, default=0.08)
    parser.add_argument("--root-width", type=float, default=0.96)
    parser.add_argument("--prime-cutoffs", default="2,29,97")
    parser.add_argument("--diagnostic-cutoff", type=int, default=997)
    parser.add_argument("--skip-diagnostic-cutoff", action="store_true")
    parser.add_argument("--intersection-tolerance", type=float, default=1e-8)
    parser.add_argument("--max-algebra-error", type=float, default=3e-9)
    parser.add_argument("--max-sonin-error", type=float, default=2e-7)
    args = parser.parse_args()

    if args.generic_size < 16 or args.generic_size % 4:
        raise ValueError("generic-size must be a multiple of four at least 16")
    if args.size < 64 or args.size % 2:
        raise ValueError("size must be an even integer at least 64")
    if args.step <= 0.0 or args.root_width <= 0.0:
        raise ValueError("step and root-width must be positive")

    strict_cutoffs = parse_cutoffs(args.prime_cutoffs)
    all_cutoffs = strict_cutoffs.copy()
    if not args.skip_diagnostic_cutoff:
        all_cutoffs = sorted(set(all_cutoffs + [args.diagnostic_cutoff]))
    half_domain = args.size * args.step / 2.0
    if math.log(max(strict_cutoffs)) + args.root_width >= half_domain:
        raise ValueError("finite-section domain is too small for a strict cutoff")

    generic = generic_certificate(args.generic_size)
    three_dimensional = [
        three_dimensional_row(kappa)
        for kappa in (2.0, 10.0, 100.0, 1000.0)
    ]
    sonin_rows, sonin_metadata = finite_sonin_rows(
        args.size,
        args.step,
        args.root_width,
        all_cutoffs,
        args.intersection_tolerance,
    )

    generic_error_keys = [
        key
        for key in generic
        if key.endswith("_error") or key.endswith("_violation")
    ]
    maximum_generic_error = max(generic[key] for key in generic_error_keys)
    maximum_three_dimensional_error = max(
        row["maximum_formula_error"] for row in three_dimensional
    )
    strict_sonin_rows = [
        row for row in sonin_rows if int(row["cutoff"]) in strict_cutoffs
    ]
    maximum_sonin_error = max(
        max(
            row["cancellation_relative_error"],
            row["defect_factor_error"],
            row["isometry_final_error"],
            row["dual_frame_error"],
            row["dual_value_error"],
            row["intrinsic_value_error"],
        )
        for row in strict_sonin_rows
    )

    print("identity=nested shorting cancellation and canonical polar owner")
    print("status=exact algebra plus finite-section conditioning guard")
    print(f"maximum_generic_error={maximum_generic_error:.12e}")
    print(
        "maximum_three_dimensional_error="
        f"{maximum_three_dimensional_error:.12e}"
    )
    print(f"maximum_strict_sonin_error={maximum_sonin_error:.12e}")
    print("generic_algebra_table=BEGIN")
    for key, value in generic.items():
        print(f"{key}={value:.12e}")
    print("generic_algebra_table=END")

    print("three_dimensional_guard_table=BEGIN")
    for row in three_dimensional:
        print(
            f"kappa={row['kappa']:.1f} "
            f"oblique_norm={row['oblique_norm']:.12e} "
            f"isometry_norm={row['isometry_norm']:.12e} "
            f"phase={row['phase']:.12e} "
            f"defect={row['defect']:.12e} "
            f"actual={row['actual']:.12e} "
            f"base={row['base']:.12e} "
            f"endpoint={row['endpoint_response']:.12e} "
            f"commutator={row['commutator_response']:.12e} "
            f"markov_identity={row['markov_identity']:.12e} "
            f"markov_swap={row['markov_swap']:.12e} "
            f"formula_error={row['maximum_formula_error']:.3e}"
        )
    print("three_dimensional_guard_table=END")

    print(f"finite_size={args.size}")
    print(f"finite_step={args.step:.12g}")
    print(f"finite_half_domain={half_domain:.12g}")
    for key, value in sonin_metadata.items():
        print(f"finite_{key}={value:.12e}")
    print("finite_sonin_cancellation_table=BEGIN")
    for row in sonin_rows:
        gate = "strict" if int(row["cutoff"]) in strict_cutoffs else "diagnostic"
        print(
            f"cutoff={int(row['cutoff'])} "
            f"gate={gate} "
            f"prime_count={int(row['prime_count'])} "
            f"log_condition={row['log_condition']:.12e} "
            f"minimum_modulus={row['minimum_modulus']:.12e} "
            f"oblique_norm={row['oblique_norm']:.12e} "
            f"phase={row['phase']:.12e} "
            f"defect={row['defect']:.12e} "
            f"actual={row['actual']:.12e} "
            f"base={row['base']:.12e} "
            f"endpoint={row['endpoint']:.12e} "
            f"canonical={row['canonical']:.12e} "
            f"dual={row['dual']:.12e} "
            f"intrinsic={row['intrinsic']:.12e} "
            f"dual_frame_norm={row['dual_frame_norm']:.12e} "
            f"dual_coordinate_norm={row['dual_coordinate_norm']:.12e} "
            f"intrinsic_defect_nuclear={row['intrinsic_defect_nuclear']:.12e} "
            f"response_nuclear={row['response_nuclear']:.12e} "
            f"intertwining_nuclear={row['intertwining_nuclear']:.12e} "
            f"sylvester_bound={row['sylvester_bound']:.12e} "
            f"bound_ratio={row['sylvester_bound_ratio']:.12e} "
            f"cancellation_error={row['cancellation_error']:.3e} "
            f"defect_factor_error={row['defect_factor_error']:.3e}"
        )
    print("finite_sonin_cancellation_table=END")

    if maximum_generic_error > args.max_algebra_error:
        raise RuntimeError("generic nested cancellation certificate failed")
    if maximum_three_dimensional_error > args.max_algebra_error:
        raise RuntimeError("three-dimensional closed formulas failed")
    if maximum_sonin_error > args.max_sonin_error:
        raise RuntimeError("strict finite Sonin cancellation certificate failed")
    if generic["minimum_modulus"] < 1.0 - 2e-11:
        raise RuntimeError("normalized Schur modulus fell below one")
    if generic["shorting_minimum_eigenvalue"] < -2e-11:
        raise RuntimeError("shorted inverse lost positivity")
    if generic["shorting_defect_minimum_eigenvalue"] < -2e-11:
        raise RuntimeError("shorting defect lost positivity")
    if three_dimensional[-1]["phase"] < 1e5:
        raise RuntimeError("three-dimensional phase amplification disappeared")
    if abs(three_dimensional[-1]["endpoint_response"]) > 1.0:
        raise RuntimeError("canonical three-dimensional response became large")

    print("certificate=PASS")
    print("oblique_band_identity_verdict=EXACT")
    print("phase_shorting_cancellation_verdict=EXACT")
    print("canonical_isometry_verdict=EXACT")
    print("polar_commutator_trace_verdict=EXACT")
    print("sylvester_intertwining_reduction_verdict=EXACT")
    print("separate_phase_defect_bound_verdict=REJECTED")
    print("finite_sonin_conditioning_verdict=DIAGNOSTIC_ONLY")
    print("continuous_intertwining_defect_bound=OPEN")
    print("detector_specific_integrated_bound=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
