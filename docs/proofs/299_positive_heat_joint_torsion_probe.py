#!/usr/bin/env python3
"""Certificate for Proof 299's positive heat and joint-torsion split."""

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


PROOF_298 = load_probe(
    "298_relative_gram_heat_boundary_layer_probe.py",
    "proof_298_for_299",
)
PROOF_264 = PROOF_298.PROOF_264


def relative_error(
    actual: complex | np.ndarray, expected: complex | np.ndarray
) -> float:
    actual_array = np.asarray(actual)
    expected_array = np.asarray(expected)
    scale = max(float(np.linalg.norm(expected_array)), 1.0)
    return float(np.linalg.norm(actual_array - expected_array) / scale)


def covariance_factors(
    owner: dict[str, np.ndarray], parameter: float
) -> dict[str, np.ndarray]:
    gamma = owner["gamma"]
    killed = owner["killed"]
    detector = owner["detector"]
    band_basis = owner["band_basis"]

    ambient_exponential = PROOF_298.hermitian_exponential(
        parameter * detector
    )
    band_compression = (
        band_basis.conj().T @ ambient_exponential @ band_basis
    )
    square_root = PROOF_298.positive_square_root(band_compression)
    actual_covariance = (
        killed.conj().T @ ambient_exponential @ killed
    )
    symmetric_covariance = square_root @ gamma @ square_root
    ordered_covariance = band_compression @ gamma

    inverse_gamma = np.linalg.inv(gamma)
    inverse_compression = np.linalg.inv(band_compression)
    inverse_square_root = np.linalg.inv(square_root)
    inverse_symmetric = np.linalg.inv(symmetric_covariance)

    ordered_relative = (
        actual_covariance @ inverse_gamma @ inverse_compression
    )
    symmetric_relative = actual_covariance @ inverse_symmetric
    anomaly_factor = (
        symmetric_covariance @ inverse_gamma @ inverse_compression
    )

    first_commutator = (
        square_root
        @ gamma
        @ inverse_square_root
        @ inverse_gamma
    )
    second_commutator = (
        gamma
        @ band_compression
        @ inverse_gamma
        @ inverse_compression
    )

    return {
        "band_compression": band_compression,
        "square_root": square_root,
        "actual_covariance": actual_covariance,
        "symmetric_covariance": symmetric_covariance,
        "ordered_covariance": ordered_covariance,
        "ordered_relative": ordered_relative,
        "symmetric_relative": symmetric_relative,
        "anomaly_factor": anomaly_factor,
        "first_commutator": first_commutator,
        "second_commutator": second_commutator,
    }


def algebra_checks(
    owner: dict[str, np.ndarray], parameter: float
) -> dict[str, float]:
    factors = covariance_factors(owner, parameter)
    ordered_relative = factors["ordered_relative"]
    symmetric_relative = factors["symmetric_relative"]
    anomaly_factor = factors["anomaly_factor"]
    first_commutator = factors["first_commutator"]
    second_commutator = factors["second_commutator"]

    determinant_ordered = np.linalg.det(ordered_relative)
    determinant_symmetric = np.linalg.det(symmetric_relative)
    determinant_anomaly = np.linalg.det(anomaly_factor)
    determinant_first = np.linalg.det(first_commutator)

    return {
        "ordered factorization error": relative_error(
            ordered_relative,
            symmetric_relative @ anomaly_factor,
        ),
        "anomaly two-commutator error": relative_error(
            anomaly_factor,
            first_commutator @ second_commutator,
        ),
        "relative determinant product error": relative_error(
            determinant_ordered,
            determinant_symmetric * determinant_anomaly,
        ),
        "inverse determinant-invariant error": relative_error(
            determinant_anomaly * determinant_first,
            1.0,
        ),
        "finite anomaly determinant from one error": float(
            abs(determinant_anomaly - 1.0)
        ),
    }


def first_jet_checks(
    owner: dict[str, np.ndarray], derivative_step: float, heat_time: float
) -> dict[str, float]:
    gamma = owner["gamma"]
    killed = owner["killed"]
    detector_outer = owner["detector_outer"]
    detector_band = owner["detector_band"]
    inverse_gamma = np.linalg.inv(gamma)

    covariance_derivative = (
        killed.conj().T @ detector_outer @ killed
    )
    symmetric_numerator = covariance_derivative - 0.5 * (
        detector_band @ gamma + gamma @ detector_band
    )
    ordered_numerator = covariance_derivative - detector_band @ gamma
    anomaly_numerator = 0.5 * (
        gamma @ detector_band - detector_band @ gamma
    )

    ordered_jet = ordered_numerator @ inverse_gamma
    symmetric_jet = symmetric_numerator @ inverse_gamma
    anomaly_jet = 0.5 * (
        gamma @ detector_band @ inverse_gamma - detector_band
    )
    invariant_jet = -anomaly_jet

    plus = covariance_factors(owner, derivative_step)
    minus = covariance_factors(owner, -derivative_step)
    numerical_anomaly_jet = (
        plus["anomaly_factor"] - minus["anomaly_factor"]
    ) / (2.0 * derivative_step)
    numerical_invariant_jet = (
        plus["first_commutator"] - minus["first_commutator"]
    ) / (2.0 * derivative_step)

    heat_integral = PROOF_298.heat_integral_operator(gamma, heat_time)
    ordered_heat = ordered_numerator @ heat_integral
    symmetric_heat = symmetric_numerator @ heat_integral
    anomaly_heat = anomaly_numerator @ heat_integral

    return {
        "numerator split error": relative_error(
            ordered_numerator,
            symmetric_numerator + anomaly_numerator,
        ),
        "endpoint jet split error": relative_error(
            ordered_jet,
            symmetric_jet + anomaly_jet,
        ),
        "anomaly derivative error": relative_error(
            numerical_anomaly_jet, anomaly_jet
        ),
        "determinant-invariant derivative error": relative_error(
            numerical_invariant_jet, invariant_jet
        ),
        "truncated heat split error": relative_error(
            ordered_heat,
            symmetric_heat + anomaly_heat,
        ),
        "finite anomaly trace magnitude": float(abs(np.trace(anomaly_jet))),
        "ordered endpoint reality error": float(
            abs(np.trace(ordered_jet).imag)
        ),
        "symmetric endpoint reality error": float(
            abs(np.trace(symmetric_jet).imag)
        ),
        "diagonal ordered-versus-symmetric trace error": float(
            abs(np.trace(ordered_jet) - np.trace(symmetric_jet))
        ),
        "ordered endpoint trace magnitude": float(abs(np.trace(ordered_jet))),
        "symmetric endpoint trace magnitude": float(
            abs(np.trace(symmetric_jet))
        ),
    }


def infinite_anomaly_guard(anomaly_time: float) -> dict[str, float]:
    rows, maximum_error = PROOF_264.similarity_anomaly_rows(
        [48, 72], anomaly_time
    )
    final_row = rows[-1]
    return {
        "similarity anomaly certificate error": maximum_error,
        "pure-anomaly positive response magnitude": 0.0,
        "physical central anomaly magnitude": 0.5
        * abs(final_row["left"]),
        "artificial far anomaly magnitude": 0.5
        * abs(final_row["right"]),
        "finite total central anomaly": 0.5 * final_row["total"],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--multiplicity", type=int, default=10)
    parser.add_argument("--seed", type=int, default=299)
    parser.add_argument("--parameter", type=float, default=0.12)
    parser.add_argument("--derivative-step", type=float, default=2e-5)
    parser.add_argument("--heat-time", type=float, default=1.8)
    parser.add_argument("--anomaly-time", type=float, default=0.7)
    parser.add_argument("--tolerance", type=float, default=2e-8)
    parser.add_argument("--anomaly-floor", type=float, default=0.1)
    args = parser.parse_args()

    owner = PROOF_298.build_owner(args.multiplicity, args.seed)
    algebra = algebra_checks(owner, args.parameter)
    jets = first_jet_checks(owner, args.derivative_step, args.heat_time)
    guard = infinite_anomaly_guard(args.anomaly_time)

    print("identity=positive heat plus determinant-invariant anomaly")
    print("status=exact split; source recombined bound open")
    for title, checks in (
        ("algebra", algebra),
        ("jet", jets),
        ("guard", guard),
    ):
        print(f"{title}_checks=BEGIN")
        for label, value in checks.items():
            print(f"{label.replace(' ', '_')}={float(value):.12e}")
        print(f"{title}_checks=END")

    excluded = {
        "ordered endpoint trace magnitude",
        "symmetric endpoint trace magnitude",
    }
    exact_errors = [
        value for label, value in algebra.items() if label not in excluded
    ] + [
        value
        for label, value in jets.items()
        if label
        not in {
            "finite anomaly trace magnitude",
            "ordered endpoint reality error",
            "symmetric endpoint reality error",
            "diagonal ordered-versus-symmetric trace error",
            "ordered endpoint trace magnitude",
            "symmetric endpoint trace magnitude",
        }
    ] + [guard["similarity anomaly certificate error"]]
    maximum_exact_error = max(float(value) for value in exact_errors)
    print(f"maximum_exact_error={maximum_exact_error:.12e}")
    if maximum_exact_error > args.tolerance:
        raise SystemExit(
            "positive heat/joint-torsion certificate failed: "
            f"{maximum_exact_error:.6e}"
        )
    if guard["physical central anomaly magnitude"] < args.anomaly_floor:
        raise SystemExit("central anomaly guard did not fire")
    source_reality_errors = (
        jets["ordered endpoint reality error"],
        jets["symmetric endpoint reality error"],
        jets["diagonal ordered-versus-symmetric trace error"],
    )
    if max(source_reality_errors) > args.tolerance:
        raise SystemExit("diagonal source-reality cancellation failed")

    print("ordered_determinant=POSITIVE_FACTOR_TIMES_ANOMALY_FACTOR")
    print("anomaly_factor=INVERSE_DETERMINANT_INVARIANT")
    print("finite_anomaly_determinant_one=BOUNDARY_POLLUTED")
    print("diagonal_source_anomaly_first_jet=ZERO_BY_HERMITIAN_REALITY")
    print("positive_symmetric_diagonal_first_jet=EXACT_OWNER")
    print("nonlinear_or_cross_root_anomaly_deletion=FORBIDDEN")
    print("positive_symmetric_source_bound=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
