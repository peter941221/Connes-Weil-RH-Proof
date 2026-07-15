#!/usr/bin/env python3
"""Certificate for Proof 295's reflected Hankel divided differences."""

from __future__ import annotations

import argparse
import importlib.util
from pathlib import Path
from types import ModuleType

import numpy as np


def load_probe(filename: str, module_name: str) -> ModuleType:
    path = Path(__file__).with_name(filename)
    specification = importlib.util.spec_from_file_location(module_name, path)
    if specification is None or specification.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(specification)
    specification.loader.exec_module(module)
    return module


PROOF_294 = load_probe(
    "294_hankel_path_projection_probe.py",
    "proof_294_for_295",
)
PROOF_285 = PROOF_294.PROOF_285
PROOF_266 = PROOF_294.PROOF_266


def relative_error(
    actual: complex | np.ndarray, expected: complex | np.ndarray
) -> float:
    actual_array = np.asarray(actual)
    expected_array = np.asarray(expected)
    scale = max(float(np.linalg.norm(expected_array)), 1.0)
    return float(np.linalg.norm(actual_array - expected_array) / scale)


def commutator(left: np.ndarray, right: np.ndarray) -> np.ndarray:
    return left @ right - right @ left


def kernel_value(value: float, path_length: int, exponent: int) -> float:
    denominator = 1.0 + value ** (2 * path_length + 1)
    return value**exponent * (1.0 + value) / denominator


def kernel_derivative(
    value: float, path_length: int, exponent: int
) -> float:
    power = 2 * path_length + 1
    denominator = 1.0 + value**power
    h_value = (1.0 + value) / denominator
    h_derivative = (
        denominator
        - (1.0 + value) * power * value ** (power - 1)
    ) / denominator**2
    if exponent == 0:
        return h_derivative
    return (
        exponent * value ** (exponent - 1) * h_value
        + value**exponent * h_derivative
    )


def beta_value(value: float, path_length: int, exponent: int) -> float:
    reflected = 2 * path_length - exponent
    return 2.0 - kernel_value(
        value, path_length, exponent
    ) - kernel_value(value, path_length, reflected)


def beta_derivative(
    value: float, path_length: int, exponent: int
) -> float:
    reflected = 2 * path_length - exponent
    return -kernel_derivative(
        value, path_length, exponent
    ) - kernel_derivative(value, path_length, reflected)


def spectral_function(
    operator: np.ndarray,
    scalar_function,
) -> np.ndarray:
    eigenvalues, eigenvectors = np.linalg.eigh(operator)
    diagonal = np.diag(
        [scalar_function(float(value)) for value in eigenvalues]
    )
    return eigenvectors @ diagonal @ eigenvectors.conj().T


def divided_difference(
    operator: np.ndarray,
    scalar_function,
    scalar_derivative,
    direction: np.ndarray,
) -> np.ndarray:
    eigenvalues, eigenvectors = np.linalg.eigh(operator)
    transformed_direction = eigenvectors.conj().T @ direction @ eigenvectors
    function_values = np.array(
        [scalar_function(float(value)) for value in eigenvalues]
    )
    multiplier = np.empty(
        (eigenvalues.size, eigenvalues.size), dtype=float
    )
    for row, left_value in enumerate(eigenvalues):
        for column, right_value in enumerate(eigenvalues):
            difference = right_value - left_value
            if abs(difference) > 1e-10:
                multiplier[row, column] = (
                    function_values[column] - function_values[row]
                ) / difference
            else:
                midpoint = 0.5 * (left_value + right_value)
                multiplier[row, column] = scalar_derivative(float(midpoint))
    return (
        eigenvectors
        @ (multiplier * transformed_direction)
        @ eigenvectors.conj().T
    )


def kernel_matrix(
    delta: np.ndarray, path_length: int, exponent: int
) -> np.ndarray:
    return spectral_function(
        delta,
        lambda value: kernel_value(value, path_length, exponent),
    )


def beta_matrix(
    delta: np.ndarray, path_length: int, exponent: int
) -> np.ndarray:
    return spectral_function(
        delta,
        lambda value: beta_value(value, path_length, exponent),
    )


def kernel_doi(
    delta: np.ndarray,
    path_length: int,
    exponent: int,
    direction: np.ndarray,
) -> np.ndarray:
    return divided_difference(
        delta,
        lambda value: kernel_value(value, path_length, exponent),
        lambda value: kernel_derivative(value, path_length, exponent),
        direction,
    )


def beta_doi(
    delta: np.ndarray,
    path_length: int,
    exponent: int,
    direction: np.ndarray,
) -> np.ndarray:
    return divided_difference(
        delta,
        lambda value: beta_value(value, path_length, exponent),
        lambda value: beta_derivative(value, path_length, exponent),
        direction,
    )


def exact_certificate(
    multiplicity: int,
    root_radius: int,
    seed: int,
    horizon: int,
) -> tuple[dict[str, float], dict[str, np.ndarray]]:
    if horizon < 2:
        raise ValueError("horizon must be at least two")
    state = PROOF_294.build_projection(
        multiplicity, root_radius, seed, horizon
    )
    killed = state["killed"]
    delta = state["delta"]
    detector_outer = state["detector_outer"]
    detector_band = state["detector_band"]
    path_projection = state["path_projection"]
    path_commutator = state["path_commutator"]
    identity_band = state["identity_band"]
    path_length = horizon + 1
    tail = path_length
    slices = PROOF_294.block_slices(
        detector_outer.shape[0], identity_band.shape[0], horizon
    )

    visible_generator = detector_outer @ killed - killed @ detector_band
    visible_left = (
        killed.conj().T @ detector_outer
        - detector_band @ killed.conj().T
    )
    delta_commutator = commutator(detector_band, delta)
    generated_delta_commutator = (
        visible_left @ killed - killed.conj().T @ visible_generator
    )

    maximum_doi_error = 0.0
    maximum_emission_generation_error = 0.0
    maximum_row_tail_generation_error = 0.0
    maximum_tail_row_generation_error = 0.0
    maximum_tail_generation_error = 0.0
    maximum_beta_generation_error = 0.0
    maximum_beta_spectral_violation = 0.0
    maximum_fixed_value_error = 0.0
    maximum_fixed_derivative_error = 0.0
    maximum_quadratic_quotient = 0.0

    grid = np.linspace(0.0, 1.0 - 1e-6, 4001)
    for exponent in range(2 * path_length + 1):
        function_matrix = kernel_matrix(delta, path_length, exponent)
        doi_matrix = kernel_doi(
            delta, path_length, exponent, delta_commutator
        )
        maximum_doi_error = max(
            maximum_doi_error,
            relative_error(
                commutator(detector_band, function_matrix), doi_matrix
            ),
        )

        emission_moment = killed @ function_matrix @ killed.conj().T
        generated_emission = (
            visible_generator @ function_matrix @ killed.conj().T
            - killed @ function_matrix @ visible_left
            + killed @ doi_matrix @ killed.conj().T
        )
        maximum_emission_generation_error = max(
            maximum_emission_generation_error,
            relative_error(
                commutator(detector_outer, emission_moment),
                generated_emission,
            ),
        )

        direct_row_tail = (
            detector_outer @ killed @ function_matrix
            - killed @ function_matrix @ detector_band
        )
        generated_row_tail = (
            visible_generator @ function_matrix + killed @ doi_matrix
        )
        maximum_row_tail_generation_error = max(
            maximum_row_tail_generation_error,
            relative_error(direct_row_tail, generated_row_tail),
        )

        direct_tail_row = (
            detector_band @ function_matrix @ killed.conj().T
            - function_matrix @ killed.conj().T @ detector_outer
        )
        generated_tail_row = (
            doi_matrix @ killed.conj().T - function_matrix @ visible_left
        )
        maximum_tail_row_generation_error = max(
            maximum_tail_row_generation_error,
            relative_error(direct_tail_row, generated_tail_row),
        )
        maximum_tail_generation_error = max(
            maximum_tail_generation_error,
            relative_error(
                commutator(detector_band, function_matrix), doi_matrix
            ),
        )

        beta = beta_matrix(delta, path_length, exponent)
        beta_difference = beta_doi(
            delta, path_length, exponent, delta_commutator
        )
        generated_beta = (
            visible_generator @ beta @ killed.conj().T
            - killed @ beta @ visible_left
            + killed @ beta_difference @ killed.conj().T
        )
        maximum_beta_generation_error = max(
            maximum_beta_generation_error,
            relative_error(
                commutator(detector_outer, killed @ beta @ killed.conj().T),
                generated_beta,
            ),
        )
        beta_eigenvalues = np.linalg.eigvalsh(beta)
        maximum_beta_spectral_violation = max(
            maximum_beta_spectral_violation,
            max(0.0, -float(np.min(beta_eigenvalues))),
            max(0.0, float(np.max(beta_eigenvalues)) - 2.0),
        )
        maximum_fixed_value_error = max(
            maximum_fixed_value_error,
            abs(beta_value(1.0, path_length, exponent)),
        )
        maximum_fixed_derivative_error = max(
            maximum_fixed_derivative_error,
            abs(beta_derivative(1.0, path_length, exponent)),
        )
        beta_grid = np.array(
            [
                beta_value(float(value), path_length, exponent)
                for value in grid
            ]
        )
        maximum_beta_spectral_violation = max(
            maximum_beta_spectral_violation,
            max(0.0, -float(np.min(beta_grid))),
            max(0.0, float(np.max(beta_grid)) - 2.0),
        )
        quotient = beta_grid / (1.0 - grid) ** 2
        maximum_quadratic_quotient = max(
            maximum_quadratic_quotient, float(np.max(quotient))
        )

    maximum_interior_moment_error = 0.0
    maximum_interior_commutator_error = 0.0
    for row in range(1, path_length):
        for column in range(1, path_length):
            exponent = row + column
            beta = beta_matrix(delta, path_length, exponent)
            expected_pair = killed @ (2.0 * identity_band - beta) @ killed.conj().T
            direct_pair = (
                path_projection[slices[row], slices[column]]
                + path_projection[
                    slices[path_length - row],
                    slices[path_length - column],
                ]
            )
            maximum_interior_moment_error = max(
                maximum_interior_moment_error,
                relative_error(direct_pair, expected_pair),
            )
            direct_commutator_pair = (
                path_commutator[slices[row], slices[column]]
                + path_commutator[
                    slices[path_length - row],
                    slices[path_length - column],
                ]
            )
            maximum_interior_commutator_error = max(
                maximum_interior_commutator_error,
                relative_error(
                    direct_commutator_pair,
                    commutator(detector_outer, expected_pair),
                ),
            )

    maximum_boundary_moment_error = 0.0
    maximum_boundary_commutator_error = 0.0
    maximum_naive_boundary_gap = 0.0
    for index in range(1, path_length):
        beta = beta_matrix(delta, path_length, index)
        expected_pair = killed @ (2.0 * identity_band - beta) @ killed.conj().T

        reflected_tail_row = path_projection[
            slices[tail], slices[path_length - index]
        ]
        top_moment = (
            path_projection[slices[0], slices[index]]
            + killed @ reflected_tail_row
        )
        maximum_boundary_moment_error = max(
            maximum_boundary_moment_error,
            relative_error(top_moment, expected_pair),
        )
        naive_top = (
            path_commutator[slices[0], slices[index]]
            + killed
            @ path_commutator[
                slices[tail], slices[path_length - index]
            ]
        )
        corrected_top = naive_top + visible_generator @ reflected_tail_row
        expected_commutator = commutator(detector_outer, expected_pair)
        maximum_boundary_commutator_error = max(
            maximum_boundary_commutator_error,
            relative_error(corrected_top, expected_commutator),
        )
        maximum_naive_boundary_gap = max(
            maximum_naive_boundary_gap,
            relative_error(naive_top, expected_commutator),
        )

        reflected_tail_column = path_projection[
            slices[path_length - index], slices[tail]
        ]
        left_moment = (
            path_projection[slices[index], slices[0]]
            + reflected_tail_column @ killed.conj().T
        )
        maximum_boundary_moment_error = max(
            maximum_boundary_moment_error,
            relative_error(left_moment, expected_pair),
        )
        naive_left = (
            path_commutator[slices[index], slices[0]]
            + path_commutator[
                slices[path_length - index], slices[tail]
            ]
            @ killed.conj().T
        )
        corrected_left = naive_left - reflected_tail_column @ visible_left
        maximum_boundary_commutator_error = max(
            maximum_boundary_commutator_error,
            relative_error(corrected_left, expected_commutator),
        )
        maximum_naive_boundary_gap = max(
            maximum_naive_boundary_gap,
            relative_error(naive_left, expected_commutator),
        )

    beta_zero = beta_matrix(delta, path_length, 0)
    expected_corner = (
        killed @ (2.0 * identity_band - beta_zero) @ killed.conj().T
    )
    tail_tail = path_projection[slices[tail], slices[tail]]
    direct_corner = (
        path_projection[slices[0], slices[0]]
        + killed @ tail_tail @ killed.conj().T
    )
    maximum_boundary_moment_error = max(
        maximum_boundary_moment_error,
        relative_error(direct_corner, expected_corner),
    )
    naive_corner = (
        path_commutator[slices[0], slices[0]]
        + killed
        @ path_commutator[slices[tail], slices[tail]]
        @ killed.conj().T
    )
    corrected_corner = (
        naive_corner
        + visible_generator @ tail_tail @ killed.conj().T
        - killed @ tail_tail @ visible_left
    )
    maximum_boundary_commutator_error = max(
        maximum_boundary_commutator_error,
        relative_error(
            corrected_corner, commutator(detector_outer, expected_corner)
        ),
    )
    maximum_naive_boundary_gap = max(
        maximum_naive_boundary_gap,
        relative_error(
            naive_corner, commutator(detector_outer, expected_corner)
        ),
    )

    common_boundary_error = relative_error(
        commutator(detector_outer, killed @ killed.conj().T),
        visible_generator @ killed.conj().T - killed @ visible_left,
    )

    return {
        "Delta commutator generation error": relative_error(
            delta_commutator, generated_delta_commutator
        ),
        "maximum DOI commutator error": maximum_doi_error,
        "maximum emission DOI generation error": (
            maximum_emission_generation_error
        ),
        "maximum row-tail DOI generation error": (
            maximum_row_tail_generation_error
        ),
        "maximum tail-row DOI generation error": (
            maximum_tail_row_generation_error
        ),
        "maximum tail DOI generation error": maximum_tail_generation_error,
        "maximum beta DOI generation error": maximum_beta_generation_error,
        "beta spectral-bound violation": maximum_beta_spectral_violation,
        "beta fixed-value error": maximum_fixed_value_error,
        "beta fixed-derivative error": maximum_fixed_derivative_error,
        "maximum interior moment-reflection error": (
            maximum_interior_moment_error
        ),
        "maximum interior commutator-reflection error": (
            maximum_interior_commutator_error
        ),
        "maximum boundary moment-completion error": (
            maximum_boundary_moment_error
        ),
        "maximum boundary commutator-completion error": (
            maximum_boundary_commutator_error
        ),
        "common boundary generator error": common_boundary_error,
        "maximum naive boundary-reflection gap": maximum_naive_boundary_gap,
        "maximum normalized quadratic quotient": (
            maximum_quadratic_quotient / path_length**2
        ),
    }, state


def near_survival_guard(
    multiplicity: int,
    root_radius: int,
    seed: int,
    horizon: int,
    scale: float = 0.5,
) -> dict[str, float]:
    model = PROOF_266.build_model(multiplicity, seed)
    detector, _ = PROOF_285.structured_cross_detector(
        multiplicity, root_radius, seed + 59
    )
    outer = model["E"]
    band_basis = model["b_basis"]
    killed = scale * outer @ model["A"] @ band_basis
    band_dimension = band_basis.shape[1]
    identity_band = np.eye(band_dimension, dtype=complex)
    delta = identity_band - killed.conj().T @ killed
    delta = 0.5 * (delta + delta.conj().T)
    detector_outer = outer @ detector @ outer
    detector_band = band_basis.conj().T @ detector @ band_basis
    path_length = horizon + 1

    right_blocks = [
        killed @ np.linalg.matrix_power(delta, exponent)
        for exponent in range(path_length)
    ]
    right_blocks.append(np.linalg.matrix_power(delta, path_length))
    right_path = np.vstack(right_blocks)
    inverse_gram = np.linalg.inv(right_path.conj().T @ right_path)
    path_projection = right_path @ inverse_gram @ right_path.conj().T
    observable = PROOF_294.PROOF_293.block_diagonal(
        [detector_outer for _ in range(path_length)] + [detector_band]
    )
    path_commutator = commutator(observable, path_projection)
    slices = PROOF_294.block_slices(
        detector_outer.shape[0], band_dimension, horizon
    )
    tail = path_length
    visible_generator = detector_outer @ killed - killed @ detector_band
    visible_left = (
        killed.conj().T @ detector_outer
        - detector_band @ killed.conj().T
    )

    maximum_corrected_error = 0.0
    maximum_naive_gap = 0.0
    for index in range(1, path_length):
        beta = beta_matrix(delta, path_length, index)
        expected_pair = killed @ (2.0 * identity_band - beta) @ killed.conj().T
        expected_commutator = commutator(detector_outer, expected_pair)

        tail_row = path_projection[slices[tail], slices[path_length - index]]
        naive_top = (
            path_commutator[slices[0], slices[index]]
            + killed
            @ path_commutator[
                slices[tail], slices[path_length - index]
            ]
        )
        corrected_top = naive_top + visible_generator @ tail_row
        maximum_corrected_error = max(
            maximum_corrected_error,
            relative_error(corrected_top, expected_commutator),
        )
        maximum_naive_gap = max(
            maximum_naive_gap,
            relative_error(naive_top, expected_commutator),
        )

        tail_column = path_projection[
            slices[path_length - index], slices[tail]
        ]
        naive_left = (
            path_commutator[slices[index], slices[0]]
            + path_commutator[
                slices[path_length - index], slices[tail]
            ]
            @ killed.conj().T
        )
        corrected_left = naive_left - tail_column @ visible_left
        maximum_corrected_error = max(
            maximum_corrected_error,
            relative_error(corrected_left, expected_commutator),
        )
        maximum_naive_gap = max(
            maximum_naive_gap,
            relative_error(naive_left, expected_commutator),
        )

    return {
        "scaled maximum Delta eigenvalue": float(
            np.max(np.linalg.eigvalsh(delta))
        ),
        "scaled corrected boundary error": maximum_corrected_error,
        "scaled naive boundary-reflection gap": maximum_naive_gap,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--multiplicity", type=int, default=10)
    parser.add_argument("--root-radius", type=int, default=2)
    parser.add_argument("--seed", type=int, default=295)
    parser.add_argument("--horizon", type=int, default=10)
    parser.add_argument("--tolerance", type=float, default=2e-10)
    parser.add_argument("--guard-floor", type=float, default=1e-3)
    args = parser.parse_args()

    checks, _ = exact_certificate(
        args.multiplicity,
        args.root_radius,
        args.seed,
        args.horizon,
    )
    guard = near_survival_guard(
        args.multiplicity,
        args.root_radius,
        args.seed,
        args.horizon,
    )

    print("identity=reflected Hankel divided-difference pair")
    print("status=local reflected blocks exact; weighted scalar assembly open")
    for title, values in (("checks", checks), ("guard", guard)):
        print(f"{title}=BEGIN")
        for label, value in values.items():
            print(f"{label.replace(' ', '_')}={float(value):.12e}")
        print(f"{title}=END")

    excluded_labels = {
        "maximum naive boundary-reflection gap",
        "maximum normalized quadratic quotient",
    }
    maximum_exact_error = max(
        float(value)
        for label, value in checks.items()
        if label not in excluded_labels
    )
    maximum_exact_error = max(
        maximum_exact_error,
        float(guard["scaled corrected boundary error"]),
    )
    print(f"maximum_exact_error={maximum_exact_error:.12e}")
    if maximum_exact_error > args.tolerance:
        raise SystemExit(
            "reflected Hankel DOI certificate failed: "
            f"{maximum_exact_error:.6e}"
        )
    if guard["scaled naive boundary-reflection gap"] < args.guard_floor:
        raise SystemExit("boundary-correction rejection guard did not fire")

    print("path_commutator_owner=SINGLE_VISIBLE_GENERATOR_PAIR")
    print("reflected_fixed_mode=DOUBLE_ZERO")
    print("beta_filter=POSITIVE_CONTRACTION_UP_TO_TWO")
    print("endpoint_boundary_corrections=MANDATORY")
    print("weighted_reflected_scalar_assembly=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
