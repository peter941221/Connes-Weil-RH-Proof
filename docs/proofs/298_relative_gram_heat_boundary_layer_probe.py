#!/usr/bin/env python3
"""Certificate for Proof 298's relative Gram heat boundary layer."""

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


PROOF_296 = load_probe(
    "296_weighted_reflection_parity_probe.py",
    "proof_296_for_298",
)
PROOF_295 = PROOF_296.PROOF_295
PROOF_294 = PROOF_296.PROOF_294
PROOF_293 = PROOF_294.PROOF_293
PROOF_266 = PROOF_294.PROOF_266
PROOF_264 = load_probe(
    "264_causal_gram_response_probe.py",
    "proof_264_for_298",
)


def relative_error(
    actual: complex | np.ndarray, expected: complex | np.ndarray
) -> float:
    actual_array = np.asarray(actual)
    expected_array = np.asarray(expected)
    scale = max(float(np.linalg.norm(expected_array)), 1.0)
    return float(np.linalg.norm(actual_array - expected_array) / scale)


def hermitian_function(operator: np.ndarray, scalar_function) -> np.ndarray:
    eigenvalues, eigenvectors = np.linalg.eigh(operator)
    diagonal = np.diag(
        [scalar_function(float(value)) for value in eigenvalues]
    )
    return eigenvectors @ diagonal @ eigenvectors.conj().T


def hermitian_exponential(operator: np.ndarray) -> np.ndarray:
    return hermitian_function(operator, np.exp)


def positive_square_root(operator: np.ndarray) -> np.ndarray:
    return hermitian_function(operator, np.sqrt)


def log_determinant_positive(operator: np.ndarray) -> float:
    eigenvalues = np.linalg.eigvalsh(operator)
    if float(np.min(eigenvalues)) <= 0.0:
        raise ValueError("positive log determinant received a nonpositive matrix")
    return float(np.sum(np.log(eigenvalues)))


def build_owner(multiplicity: int, seed: int) -> dict[str, np.ndarray]:
    model = PROOF_266.build_model(multiplicity, seed)
    outer = model["E"]
    band_basis = model["b_basis"]
    detector = model["W"]
    killed = outer @ model["A"] @ band_basis
    gamma = killed.conj().T @ killed
    gamma = 0.5 * (gamma + gamma.conj().T)
    detector_outer = outer @ detector @ outer
    detector_band = band_basis.conj().T @ detector @ band_basis
    numerator = (
        killed.conj().T @ detector_outer @ killed
        - detector_band @ gamma
    )
    return {
        "killed": killed,
        "gamma": gamma,
        "detector": detector,
        "detector_outer": detector_outer,
        "detector_band": detector_band,
        "numerator": numerator,
        "band_basis": band_basis,
    }


def finite_path_checks(
    owner: dict[str, np.ndarray], steps: int, total_time: float
) -> dict[str, float]:
    killed = owner["killed"]
    gamma = owner["gamma"]
    detector_outer = owner["detector_outer"]
    detector_band = owner["detector_band"]
    numerator = owner["numerator"]
    identity_band = np.eye(gamma.shape[0], dtype=complex)
    step = total_time / steps
    scaled_killed = np.sqrt(step) * killed
    delta = identity_band - step * gamma
    if float(np.min(np.linalg.eigvalsh(delta))) <= 0.0:
        raise ValueError("time step is too large for a positive survival step")

    right_path = np.vstack(
        [
            scaled_killed @ np.linalg.matrix_power(delta, index)
            for index in range(steps)
        ]
        + [np.linalg.matrix_power(delta, steps)]
    )
    left_path = np.vstack(
        [scaled_killed for _ in range(steps)] + [identity_band]
    )
    observable = PROOF_293.block_diagonal(
        [detector_outer for _ in range(steps)] + [detector_band]
    )
    direct_response = sum(
        (
            step * numerator @ np.linalg.matrix_power(delta, index)
            for index in range(steps)
        ),
        np.zeros_like(numerator),
    )
    path_response = (
        left_path.conj().T @ observable @ right_path - detector_band
    )

    right_gram = right_path.conj().T @ right_path
    inverse_gram = np.linalg.inv(right_gram)
    canonical_dual = right_path @ inverse_gram
    path_projection = right_path @ inverse_gram @ right_path.conj().T
    null_coframe = left_path - canonical_dual
    intertwinement = observable @ right_path - right_path @ detector_band
    path_commutator = (
        observable @ path_projection - path_projection @ observable
    )
    canonical_split = (
        canonical_dual.conj().T @ intertwinement
        + null_coframe.conj().T
        @ path_commutator
        @ right_path
    )

    tiny_step = 1e-5

    def analytic_response(parameter: float) -> np.ndarray:
        analytic_delta = identity_band - parameter * gamma
        return sum(
            (
                parameter
                * numerator
                @ np.linalg.matrix_power(analytic_delta, index)
                for index in range(steps)
            ),
            np.zeros_like(numerator),
        )

    numerical_first_jet = (
        analytic_response(tiny_step) - analytic_response(-tiny_step)
    ) / (2.0 * tiny_step)

    return {
        "finite path response error": relative_error(
            path_response, direct_response
        ),
        "canonical plus off-range error": relative_error(
            canonical_split, direct_response
        ),
        "fixed-horizon first-jet error": relative_error(
            numerical_first_jet, steps * numerator
        ),
    }


def heat_integral_operator(gamma: np.ndarray, total_time: float) -> np.ndarray:
    return hermitian_function(
        gamma,
        lambda value: -np.expm1(-total_time * value) / value,
    )


def boundary_layer_checks(
    owner: dict[str, np.ndarray], steps: int, total_time: float
) -> dict[str, float]:
    gamma = owner["gamma"]
    numerator = owner["numerator"]
    identity_band = np.eye(gamma.shape[0], dtype=complex)
    heat_response = numerator @ heat_integral_operator(gamma, total_time)
    errors: list[float] = []
    for current_steps in (steps, 2 * steps, 4 * steps):
        step = total_time / current_steps
        delta = identity_band - step * gamma
        discrete_response = sum(
            (
                step
                * numerator
                @ np.linalg.matrix_power(delta, index)
                for index in range(current_steps)
            ),
            np.zeros_like(numerator),
        )
        errors.append(relative_error(discrete_response, heat_response))

    return {
        "boundary-layer error at N": errors[0],
        "boundary-layer error at 2N": errors[1],
        "boundary-layer error at 4N": errors[2],
        "boundary-layer refinement ratio": errors[0]
        / max(errors[2], 1e-30),
    }


def covariance_pair(
    owner: dict[str, np.ndarray], parameter: float
) -> tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray]:
    killed = owner["killed"]
    gamma = owner["gamma"]
    detector = owner["detector"]
    band_basis = owner["band_basis"]
    ambient_exponential = hermitian_exponential(parameter * detector)
    band_compression = (
        band_basis.conj().T @ ambient_exponential @ band_basis
    )
    band_square_root = positive_square_root(band_compression)
    actual_covariance = (
        killed.conj().T @ ambient_exponential @ killed
    )
    ordered_reference = band_compression @ gamma
    positive_representative = (
        band_square_root @ gamma @ band_square_root
    )
    return (
        actual_covariance,
        ordered_reference,
        positive_representative,
        band_square_root,
    )


def ordered_heat_difference(
    owner: dict[str, np.ndarray], parameter: float, heat_time: float
) -> tuple[complex, float]:
    (
        actual_covariance,
        ordered_reference,
        positive_representative,
        band_square_root,
    ) = covariance_pair(owner, parameter)
    inverse_square_root = np.linalg.inv(band_square_root)
    ordered_similarity = (
        band_square_root
        @ positive_representative
        @ inverse_square_root
    )
    positive_heat = hermitian_function(
        positive_representative,
        lambda value: np.exp(-heat_time * value),
    )
    ordered_heat = (
        band_square_root @ positive_heat @ inverse_square_root
    )
    actual_heat = hermitian_function(
        actual_covariance,
        lambda value: np.exp(-heat_time * value),
    )
    return (
        np.trace(actual_heat - ordered_heat),
        relative_error(ordered_reference, ordered_similarity),
    )


def relative_heat_checks(
    owner: dict[str, np.ndarray], derivative_step: float
) -> dict[str, float]:
    gamma = owner["gamma"]
    numerator = owner["numerator"]
    inverse_gamma = np.linalg.inv(gamma)
    endpoint = np.trace(numerator @ inverse_gamma)
    maximum_heat_jet_error = 0.0
    maximum_ordered_similarity_error = 0.0

    for heat_time in (0.2, 0.9, 3.0):
        heat_kernel = hermitian_function(
            gamma, lambda value: np.exp(-heat_time * value)
        )
        expected_jet = -heat_time * np.trace(numerator @ heat_kernel)

        plus_heat_difference, plus_similarity_error = (
            ordered_heat_difference(owner, derivative_step, heat_time)
        )
        minus_heat_difference, minus_similarity_error = (
            ordered_heat_difference(owner, -derivative_step, heat_time)
        )
        maximum_ordered_similarity_error = max(
            maximum_ordered_similarity_error,
            plus_similarity_error,
            minus_similarity_error,
        )
        numerical_jet = (
            plus_heat_difference - minus_heat_difference
        ) / (2.0 * derivative_step)
        maximum_heat_jet_error = max(
            maximum_heat_jet_error,
            relative_error(numerical_jet, expected_jet),
        )

    plus_actual, _, plus_positive, _ = covariance_pair(
        owner, derivative_step
    )
    minus_actual, _, minus_positive, _ = covariance_pair(
        owner, -derivative_step
    )
    plus_log_ratio = (
        log_determinant_positive(plus_actual)
        - log_determinant_positive(plus_positive)
    )
    minus_log_ratio = (
        log_determinant_positive(minus_actual)
        - log_determinant_positive(minus_positive)
    )
    determinant_jet = (
        plus_log_ratio - minus_log_ratio
    ) / (2.0 * derivative_step)

    frullani_parameter = 0.08
    actual, _, positive_representative, _ = covariance_pair(
        owner, frullani_parameter
    )
    actual_eigenvalues = np.linalg.eigvalsh(actual)
    reference_eigenvalues = np.linalg.eigvalsh(positive_representative)
    nodes, weights = np.polynomial.legendre.leggauss(320)
    unit_nodes = 0.5 * (nodes + 1.0)
    unit_weights = 0.5 * weights
    frullani_integral = 0.0
    for unit_node, unit_weight in zip(unit_nodes, unit_weights):
        heat_time = unit_node / (1.0 - unit_node)
        numerator_value = np.sum(
            np.exp(-heat_time * reference_eigenvalues)
            - np.exp(-heat_time * actual_eigenvalues)
        )
        integrand = numerator_value / heat_time
        frullani_integral += (
            unit_weight * integrand / (1.0 - unit_node) ** 2
        )
    expected_log_ratio = (
        log_determinant_positive(actual)
        - log_determinant_positive(positive_representative)
    )

    return {
        "relative heat first-jet error": maximum_heat_jet_error,
        "relative log-determinant first-jet error": relative_error(
            determinant_jet, endpoint
        ),
        "ordered Frullani determinant error": relative_error(
            frullani_integral, expected_log_ratio
        ),
        "finite ordered-similarity error": maximum_ordered_similarity_error,
        "endpoint response magnitude": float(abs(endpoint)),
    }


def similarity_anomaly_guard() -> dict[str, float]:
    rows, maximum_error = PROOF_264.similarity_anomaly_rows(
        [48, 72], 0.5
    )
    final_row = rows[-1]
    return {
        "similarity anomaly certificate error": maximum_error,
        "physical left anomaly magnitude": abs(final_row["left"]),
        "artificial far anomaly magnitude": abs(final_row["right"]),
        "finite total similarity trace": final_row["total"],
    }


def reflection_profile_checks(
    path_length: int,
    profile_x: float,
    alpha: float,
    beta: float,
) -> dict[str, float]:
    if path_length < 16:
        raise ValueError("profile path length must be at least sixteen")
    if not 0.0 < alpha < 1.0 or not 0.0 < beta < 1.0:
        raise ValueError("profile fractions must lie in (0,1)")

    maximum_profile_error = 0.0
    minimum_sector_profile = float("inf")
    largest_path_profiles: tuple[float, ...] | None = None
    for current_length in (path_length, 2 * path_length):
        left_index = max(
            1, min(current_length - 1, round(alpha * current_length))
        )
        right_index = max(
            1, min(current_length - 1, round(beta * current_length))
        )
        left_fraction = left_index / current_length
        right_fraction = right_index / current_length
        value = np.exp(-profile_x / current_length)

        left_value = PROOF_295.kernel_value(
            value, current_length, left_index
        )
        left_reflected = PROOF_295.kernel_value(
            value, current_length, current_length - left_index
        )
        a_plus = 1.0 - 0.5 * (left_value + left_reflected)
        a_minus = 0.5 * (left_reflected - left_value)
        b_plus = 0.5 * (
            value**right_index
            + value ** (current_length - right_index)
        )
        b_minus = 0.5 * (
            value**right_index
            - value ** (current_length - right_index)
        )
        exponent = left_index + right_index
        exponent_reflected = 2 * current_length - exponent
        commutator_value = PROOF_295.kernel_value(
            value, current_length, exponent
        )
        commutator_reflected = PROOF_295.kernel_value(
            value, current_length, exponent_reflected
        )
        c_plus = 0.5 * (commutator_value + commutator_reflected)
        c_minus = 0.5 * (commutator_value - commutator_reflected)

        hyperbolic_denominator = np.cosh(profile_x)
        expected_a_plus = 1.0 - (
            np.exp((1.0 - left_fraction) * profile_x)
            + np.exp(left_fraction * profile_x)
        ) / (2.0 * hyperbolic_denominator)
        expected_a_minus = (
            np.exp(left_fraction * profile_x)
            - np.exp((1.0 - left_fraction) * profile_x)
        ) / (2.0 * hyperbolic_denominator)
        expected_b_plus = 0.5 * (
            np.exp(-right_fraction * profile_x)
            + np.exp(-(1.0 - right_fraction) * profile_x)
        )
        expected_b_minus = 0.5 * (
            np.exp(-right_fraction * profile_x)
            - np.exp(-(1.0 - right_fraction) * profile_x)
        )
        centered_exponent = 1.0 - left_fraction - right_fraction
        expected_c_plus = (
            np.cosh(centered_exponent * profile_x)
            / hyperbolic_denominator
        )
        expected_c_minus = (
            np.sinh(centered_exponent * profile_x)
            / hyperbolic_denominator
        )

        actual_profiles = (
            a_plus,
            a_minus,
            b_plus,
            b_minus,
            c_plus,
            c_minus,
        )
        expected_profiles = (
            expected_a_plus,
            expected_a_minus,
            expected_b_plus,
            expected_b_minus,
            expected_c_plus,
            expected_c_minus,
        )
        maximum_profile_error = max(
            maximum_profile_error,
            max(
                abs(actual_value - expected_value)
                for actual_value, expected_value in zip(
                    actual_profiles, expected_profiles
                )
            ),
        )
        sector_profiles = (
            expected_a_plus * expected_c_plus * expected_b_plus,
            expected_a_plus * expected_c_minus * expected_b_minus,
            expected_a_minus * expected_c_plus * expected_b_minus,
            expected_a_minus * expected_c_minus * expected_b_plus,
        )
        minimum_sector_profile = min(
            minimum_sector_profile,
            min(abs(profile) for profile in sector_profiles),
        )
        largest_path_profiles = sector_profiles

    if largest_path_profiles is None:
        raise AssertionError("profile loop did not run")
    return {
        "maximum hyperbolic profile error": maximum_profile_error,
        "minimum nonzero sector profile": minimum_sector_profile,
        "all-even boundary profile magnitude": float(
            abs(largest_path_profiles[0])
        ),
        "plus-minus-minus boundary profile magnitude": float(
            abs(largest_path_profiles[1])
        ),
        "minus-plus-minus boundary profile magnitude": float(
            abs(largest_path_profiles[2])
        ),
        "minus-minus-plus boundary profile magnitude": float(
            abs(largest_path_profiles[3])
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--multiplicity", type=int, default=10)
    parser.add_argument("--seed", type=int, default=298)
    parser.add_argument("--steps", type=int, default=24)
    parser.add_argument("--time", type=float, default=1.7)
    parser.add_argument("--profile-length", type=int, default=128)
    parser.add_argument("--profile-x", type=float, default=1.4)
    parser.add_argument("--alpha", type=float, default=0.30)
    parser.add_argument("--beta", type=float, default=0.55)
    parser.add_argument("--derivative-step", type=float, default=2e-5)
    parser.add_argument("--tolerance", type=float, default=2e-7)
    parser.add_argument("--profile-tolerance", type=float, default=3e-2)
    parser.add_argument("--profile-floor", type=float, default=5e-5)
    parser.add_argument("--refinement-floor", type=float, default=3.0)
    args = parser.parse_args()

    if args.steps < 4:
        raise ValueError("steps must be at least four")
    owner = build_owner(args.multiplicity, args.seed)
    path_checks = finite_path_checks(owner, args.steps, args.time)
    boundary_checks = boundary_layer_checks(owner, args.steps, args.time)
    heat_checks = relative_heat_checks(owner, args.derivative_step)
    anomaly_checks = similarity_anomaly_guard()
    profile_checks = reflection_profile_checks(
        args.profile_length,
        args.profile_x,
        args.alpha,
        args.beta,
    )

    print("identity=relative Gram heat boundary layer")
    print("status=exact heat owner; uniform source heat bound open")
    for title, checks in (
        ("path", path_checks),
        ("boundary", boundary_checks),
        ("heat", heat_checks),
        ("anomaly", anomaly_checks),
        ("profile", profile_checks),
    ):
        print(f"{title}_checks=BEGIN")
        for label, value in checks.items():
            print(f"{label.replace(' ', '_')}={float(value):.12e}")
        print(f"{title}_checks=END")

    exact_errors = list(path_checks.values()) + [
        heat_checks["relative heat first-jet error"],
        heat_checks["relative log-determinant first-jet error"],
        heat_checks["ordered Frullani determinant error"],
        heat_checks["finite ordered-similarity error"],
        anomaly_checks["similarity anomaly certificate error"],
    ]
    maximum_exact_error = max(float(value) for value in exact_errors)
    print(f"maximum_exact_error={maximum_exact_error:.12e}")
    if maximum_exact_error > args.tolerance:
        raise SystemExit(
            "relative Gram heat certificate failed: "
            f"{maximum_exact_error:.6e}"
        )
    if (
        boundary_checks["boundary-layer refinement ratio"]
        < args.refinement_floor
    ):
        raise SystemExit("discrete-to-heat refinement guard did not fire")
    if (
        profile_checks["maximum hyperbolic profile error"]
        > args.profile_tolerance
    ):
        raise SystemExit("hyperbolic reflection profile did not converge")
    if (
        profile_checks["minimum nonzero sector profile"]
        < args.profile_floor
    ):
        raise SystemExit("reflection boundary-layer guard did not fire")
    if anomaly_checks["physical left anomaly magnitude"] < 0.2:
        raise SystemExit("ordered similarity-anomaly guard did not fire")

    print("finite_path_limit=RELATIVE_GRAM_HEAT_INTEGRAL")
    print("ordered_relative_determinant_jet=EXACT")
    print("positive_reference_symmetrization=FORBIDDEN")
    print("fixed_mode_zero_orders=NONUNIFORM_IN_HORIZON")
    print("blockwise_reflection_norm_estimate=REJECTED")
    print("source_outer_sonin_heat_bound=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
