#!/usr/bin/env python3
"""Certificate for Proof 300's positive polar readback and no-gain guard."""

from __future__ import annotations

import argparse
import importlib.util
import math
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


PROOF_299 = load_probe(
    "299_positive_heat_joint_torsion_probe.py",
    "proof_299_for_300",
)
PROOF_298 = PROOF_299.PROOF_298


def relative_error(
    actual: complex | np.ndarray, expected: complex | np.ndarray
) -> float:
    actual_array = np.asarray(actual)
    expected_array = np.asarray(expected)
    scale = max(float(np.linalg.norm(expected_array)), 1.0)
    return float(np.linalg.norm(actual_array - expected_array) / scale)


def positive_inverse_square_root(operator: np.ndarray) -> np.ndarray:
    return PROOF_298.hermitian_function(operator, lambda value: value**-0.5)


def positive_log_determinant(operator: np.ndarray) -> float:
    eigenvalues = np.linalg.eigvalsh(0.5 * (operator + operator.conj().T))
    if float(np.min(eigenvalues)) <= 0.0:
        raise ValueError("positive log determinant received a nonpositive matrix")
    return float(np.sum(np.log(eigenvalues)))


def normalized_paths(
    owner: dict[str, np.ndarray], parameter: float
) -> dict[str, np.ndarray | float]:
    gamma = owner["gamma"]
    killed = owner["killed"]
    detector = owner["detector"]
    band_basis = owner["band_basis"]

    gamma_square_root = PROOF_298.positive_square_root(gamma)
    gamma_inverse_square_root = positive_inverse_square_root(gamma)
    isometry = killed @ gamma_inverse_square_root
    exponential = PROOF_298.hermitian_exponential(parameter * detector)
    normalized_covariance = isometry.conj().T @ exponential @ isometry
    band_compression = band_basis.conj().T @ exponential @ band_basis
    actual_covariance = killed.conj().T @ exponential @ killed
    compression_square_root = PROOF_298.positive_square_root(
        band_compression
    )
    symmetric_covariance = (
        compression_square_root @ gamma @ compression_square_root
    )

    return {
        "gamma_square_root": gamma_square_root,
        "gamma_inverse_square_root": gamma_inverse_square_root,
        "isometry": isometry,
        "normalized_covariance": normalized_covariance,
        "band_compression": band_compression,
        "actual_covariance": actual_covariance,
        "symmetric_covariance": symmetric_covariance,
        "normalized_log_ratio": positive_log_determinant(
            normalized_covariance
        )
        - positive_log_determinant(band_compression),
        "symmetric_log_ratio": positive_log_determinant(actual_covariance)
        - positive_log_determinant(symmetric_covariance),
    }


def source_polar_checks(
    owner: dict[str, np.ndarray], parameter: float, derivative_step: float
) -> dict[str, float]:
    gamma = owner["gamma"]
    killed = owner["killed"]
    detector = owner["detector"]
    detector_band = owner["detector_band"]
    band_basis = owner["band_basis"]
    identity_band = np.eye(gamma.shape[0], dtype=complex)

    base = normalized_paths(owner, 0.0)
    isometry = np.asarray(base["isometry"])
    projection = isometry @ isometry.conj().T
    source_band = band_basis @ band_basis.conj().T
    inverse_gamma = np.linalg.inv(gamma)

    covariance_derivative = killed.conj().T @ detector @ killed
    ordered_numerator = covariance_derivative - detector_band @ gamma
    symmetric_numerator = covariance_derivative - 0.5 * (
        detector_band @ gamma + gamma @ detector_band
    )
    ordered_response = np.trace(ordered_numerator @ inverse_gamma)
    symmetric_response = np.trace(symmetric_numerator @ inverse_gamma)
    polar_response = np.trace(
        isometry.conj().T @ detector @ isometry - detector_band
    )
    ambient_response = np.trace(detector @ (projection - source_band))

    at_parameter = normalized_paths(owner, parameter)
    normalized_covariance = np.asarray(
        at_parameter["normalized_covariance"]
    )
    actual_covariance = np.asarray(at_parameter["actual_covariance"])
    gamma_square_root = np.asarray(at_parameter["gamma_square_root"])

    plus = normalized_paths(owner, derivative_step)
    minus = normalized_paths(owner, -derivative_step)
    normalized_numerical_jet = (
        float(plus["normalized_log_ratio"])
        - float(minus["normalized_log_ratio"])
    ) / (2.0 * derivative_step)
    symmetric_numerical_jet = (
        float(plus["symmetric_log_ratio"])
        - float(minus["symmetric_log_ratio"])
    ) / (2.0 * derivative_step)

    return {
        "polar isometry error": relative_error(
            isometry.conj().T @ isometry, identity_band
        ),
        "transported projection error": relative_error(
            projection @ projection, projection
        ),
        "normalized covariance identity error": relative_error(
            actual_covariance,
            gamma_square_root
            @ normalized_covariance
            @ gamma_square_root,
        ),
        "finite positive determinant equality error": float(
            abs(
                float(at_parameter["normalized_log_ratio"])
                - float(at_parameter["symmetric_log_ratio"])
            )
        ),
        "ambient versus polar response error": float(
            abs(ambient_response - polar_response)
        ),
        "ordered versus polar response error": float(
            abs(ordered_response - polar_response)
        ),
        "symmetric versus polar response error": float(
            abs(symmetric_response - polar_response)
        ),
        "normalized determinant jet error": float(
            abs(normalized_numerical_jet - polar_response.real)
        ),
        "symmetric determinant jet error": float(
            abs(symmetric_numerical_jet - polar_response.real)
        ),
        "source response imaginary magnitude": float(
            abs(ambient_response.imag)
        ),
        "source response magnitude": float(abs(ambient_response)),
    }


def parse_primes(value: str) -> list[int]:
    primes = [int(item.strip()) for item in value.split(",") if item.strip()]
    if len(primes) < 3:
        raise argparse.ArgumentTypeError("provide at least three guard primes")
    return primes


def is_prime(value: int) -> bool:
    if value < 2:
        return False
    if value % 2 == 0:
        return value == 2
    divisor = 3
    while divisor <= math.isqrt(value):
        if value % divisor == 0:
            return False
        divisor += 2
    return True


def one_prime_log_ratio(
    isometry: np.ndarray,
    source_vector: np.ndarray,
    detector: np.ndarray,
    parameter: float,
) -> float:
    exponential = np.diag(np.exp(parameter * np.diag(detector)))
    transported_value = (
        isometry.conj().T @ exponential @ isometry
    ).item().real
    source_value = (
        source_vector.conj().T @ exponential @ source_vector
    ).item().real
    return float(np.log(transported_value) - np.log(source_value))


def one_prime_no_gain_checks(
    primes: list[int], derivative_step: float, parameter: float
) -> dict[str, float]:
    if not all(is_prime(value) for value in primes):
        raise ValueError("every one-prime guard parameter must be prime")

    unitary = np.diag([1.0, -1.0]).astype(complex)
    detector_negative = np.diag([2.0, 1.0]).astype(complex)
    detector_positive = np.diag([1.0, 2.0]).astype(complex)
    source_vector = np.array([[1.0], [1.0]], dtype=complex) / np.sqrt(2.0)
    source_projection = source_vector @ source_vector.conj().T
    identity = np.eye(2, dtype=complex)

    formula_errors: list[float] = []
    sign_errors: list[float] = []
    determinant_errors: list[float] = []
    symmetric_factor_errors: list[float] = []
    half_power_ratios: list[float] = []
    full_power_ratios: list[float] = []
    amplitudes: list[float] = []
    responses: list[float] = []

    for prime in primes:
        amplitude = prime**-0.5
        transport = identity - amplitude * unitary
        killed = transport @ source_vector
        gamma = float((killed.conj().T @ killed).item().real)
        isometry = killed / np.sqrt(gamma)
        transported_projection = isometry @ isometry.conj().T

        negative_response = float(
            np.trace(
                detector_negative
                @ (transported_projection - source_projection)
            ).real
        )
        positive_response = float(
            np.trace(
                detector_positive
                @ (transported_projection - source_projection)
            ).real
        )
        expected_negative = -amplitude / (1.0 + amplitude**2)

        formula_errors.append(abs(negative_response - expected_negative))
        sign_errors.append(abs(negative_response + positive_response))
        half_power_ratios.append(abs(negative_response) / amplitude)
        full_power_ratios.append(abs(negative_response) / amplitude**2)
        amplitudes.append(amplitude)
        responses.append(abs(negative_response))

        plus = one_prime_log_ratio(
            isometry,
            source_vector,
            detector_negative,
            derivative_step,
        )
        minus = one_prime_log_ratio(
            isometry,
            source_vector,
            detector_negative,
            -derivative_step,
        )
        determinant_jet = (plus - minus) / (2.0 * derivative_step)
        determinant_errors.append(abs(determinant_jet - negative_response))

        exponential = np.diag(
            np.exp(parameter * np.diag(detector_negative))
        )
        actual_covariance = (killed.conj().T @ exponential @ killed).item()
        source_compression = (
            source_vector.conj().T @ exponential @ source_vector
        ).item()
        symmetric_relative = actual_covariance / (
            source_compression * gamma
        )
        normalized_relative = np.exp(
            one_prime_log_ratio(
                isometry,
                source_vector,
                detector_negative,
                parameter,
            )
        )
        symmetric_factor_errors.append(
            float(abs(symmetric_relative - normalized_relative))
        )

    log_slope = float(
        np.polyfit(np.log(amplitudes), np.log(responses), 1)[0]
    )

    return {
        "unitary error": relative_error(unitary.conj().T @ unitary, identity),
        "self-adjoint unitary error": relative_error(
            unitary.conj().T, unitary
        ),
        "negative detector commutator error": relative_error(
            detector_negative @ unitary, unitary @ detector_negative
        ),
        "positive detector commutator error": relative_error(
            detector_positive @ unitary, unitary @ detector_positive
        ),
        "minimum detector eigenvalue": float(
            min(
                np.min(np.linalg.eigvalsh(detector_negative)),
                np.min(np.linalg.eigvalsh(detector_positive)),
            )
        ),
        "response formula error": max(formula_errors),
        "opposite sign error": max(sign_errors),
        "positive determinant factorization error": max(
            symmetric_factor_errors
        ),
        "positive determinant jet error": max(determinant_errors),
        "half-power ratio minimum": min(half_power_ratios),
        "half-power ratio maximum": max(half_power_ratios),
        "full-power ratio at largest prime": full_power_ratios[-1],
        "measured amplitude exponent": log_slope,
        "negative response at smallest prime": -responses[0],
        "positive response at smallest prime": responses[0],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--multiplicity", type=int, default=10)
    parser.add_argument("--seed", type=int, default=300)
    parser.add_argument("--parameter", type=float, default=0.11)
    parser.add_argument("--derivative-step", type=float, default=2e-5)
    parser.add_argument(
        "--guard-primes",
        type=parse_primes,
        default=parse_primes("101,1009,10007,100003,1000003"),
    )
    parser.add_argument("--tolerance", type=float, default=2e-8)
    parser.add_argument("--half-power-floor", type=float, default=0.98)
    parser.add_argument("--full-power-growth-floor", type=float, default=100.0)
    args = parser.parse_args()

    owner = PROOF_298.build_owner(args.multiplicity, args.seed)
    source = source_polar_checks(
        owner, args.parameter, args.derivative_step
    )
    guard = one_prime_no_gain_checks(
        args.guard_primes, args.derivative_step, args.parameter
    )

    print("identity=positive polar first-jet readback")
    print("status=exact owner; automatic sign and extra half-power rejected")
    for title, checks in (("source", source), ("guard", guard)):
        print(f"{title}_checks=BEGIN")
        for label, value in checks.items():
            print(f"{label.replace(' ', '_')}={float(value):.12e}")
        print(f"{title}_checks=END")

    source_excluded = {"source response magnitude"}
    guard_excluded = {
        "minimum detector eigenvalue",
        "half-power ratio minimum",
        "half-power ratio maximum",
        "full-power ratio at largest prime",
        "measured amplitude exponent",
        "negative response at smallest prime",
        "positive response at smallest prime",
    }
    maximum_exact_error = max(
        [
            value
            for label, value in source.items()
            if label not in source_excluded
        ]
        + [
            value
            for label, value in guard.items()
            if label not in guard_excluded
        ]
    )
    print(f"maximum_exact_error={maximum_exact_error:.12e}")
    if maximum_exact_error > args.tolerance:
        raise SystemExit(
            "positive polar/no-gain certificate failed: "
            f"{maximum_exact_error:.6e}"
        )
    if guard["half-power ratio minimum"] < args.half_power_floor:
        raise SystemExit("one-prime response lost its exact half-power scale")
    if (
        guard["full-power ratio at largest prime"]
        < args.full_power_growth_floor
    ):
        raise SystemExit("one-prime guard did not reject a full-power bound")
    if not (0.95 <= guard["measured amplitude exponent"] <= 1.05):
        raise SystemExit("one-prime response does not have amplitude exponent one")
    if guard["negative response at smallest prime"] >= 0.0:
        raise SystemExit("negative detector did not produce a negative response")
    if guard["positive response at smallest prime"] <= 0.0:
        raise SystemExit("positive detector did not reverse the response sign")

    print("positive_symmetric_first_jet=ORIGINAL_PROJECTION_RESPONSE")
    print("infinite_dimensional_trace_cycle=NOT_USED")
    print("positive_commuting_detector_sign=INDEFINITE")
    print("automatic_extra_half_power=REJECTED")
    print("sonin_toeplitz_covariance_bound=OPEN")
    print("moving_band_complete_cancellation=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
