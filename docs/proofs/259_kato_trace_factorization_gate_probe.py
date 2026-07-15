#!/usr/bin/env python3
"""Certificate for the Kato trace-factorization gate.

The script checks two finite-dimensional identities.

First, for an orthogonal projection P and its codiagonal Kato generator A,
the route form

    Tr(C_eta [A,P] C_xi*)

equals a sum of two products which become trace class when their factors are
Hilbert--Schmidt:

    Tr([P,C_xi*] C_eta A) + Tr([P,C_eta] A C_xi*).

Second, a Q-preserving nested projection path has constant nonzero covariant
leakage C_t=Q mathcalU_t B while a commuting positive detector sees a nonzero
projection response.  The leakage therefore cannot determine the route trace.

The certificate checks algebra only.  It does not prove an infinite-dimensional
Schatten estimate, a finite-S trace identity, or RH.
"""

from __future__ import annotations

import argparse
import math

import numpy as np


def projection(vector: np.ndarray) -> np.ndarray:
    return vector @ vector.conj().T


def commutator(left: np.ndarray, right: np.ndarray) -> np.ndarray:
    return left @ right - right @ left


def relative_error(actual: complex | np.ndarray, expected: complex | np.ndarray) -> float:
    actual_array = np.asarray(actual)
    expected_array = np.asarray(expected)
    denominator = max(float(np.linalg.norm(expected_array)), 1e-15)
    return float(np.linalg.norm(actual_array - expected_array) / denominator)


def trace_factorization_certificate(size: int, seed: int) -> dict[str, float]:
    if size < 4 or size % 2:
        raise ValueError("size must be an even integer at least four")

    rng = np.random.default_rng(seed)
    identity = np.eye(size, dtype=complex)
    band = np.zeros((size, size), dtype=complex)
    band[: size // 2, : size // 2] = np.eye(size // 2)

    raw = rng.normal(size=(size, size)) + 1j * rng.normal(size=(size, size))
    skew = raw - raw.conj().T
    kato = (identity - band) @ skew @ band + band @ skew @ (identity - band)
    kato /= max(float(np.linalg.norm(kato, ord=2)), 1e-15)
    derivative = commutator(kato, band)

    c_eta = (
        rng.normal(size=(size, size))
        + 1j * rng.normal(size=(size, size))
    ) / math.sqrt(2.0 * size)
    c_xi = (
        rng.normal(size=(size, size))
        + 1j * rng.normal(size=(size, size))
    ) / math.sqrt(2.0 * size)

    weight = c_xi.conj().T @ c_eta
    direct = np.trace(c_eta @ derivative @ c_xi.conj().T)
    commutator_form = np.trace(commutator(band, weight) @ kato)
    first_factor = commutator(band, c_xi.conj().T)
    second_factor = c_eta @ kato
    third_factor = commutator(band, c_eta)
    fourth_factor = kato @ c_xi.conj().T
    two_factor_form = np.trace(first_factor @ second_factor) + np.trace(
        third_factor @ fourth_factor
    )
    holder_bound = (
        np.linalg.norm(first_factor, ord="fro")
        * np.linalg.norm(second_factor, ord="fro")
        + np.linalg.norm(third_factor, ord="fro")
        * np.linalg.norm(fourth_factor, ord="fro")
    )

    return {
        "kato_skew_error": relative_error(kato.conj().T, -kato),
        "projection_tangent_error": relative_error(
            band @ derivative @ band, np.zeros_like(band)
        ),
        "kato_reconstruction_error": relative_error(
            commutator(derivative, band), kato
        ),
        "commutator_trace_error": relative_error(commutator_form, direct),
        "two_factor_trace_error": relative_error(two_factor_form, direct),
        "direct_trace_magnitude": float(abs(direct)),
        "two_factor_holder_bound": float(holder_bound),
        "holder_slack": float(holder_bound - abs(direct)),
    }


def leakage_blindness_certificate(
    angle: float, initial_angle: float, base_angle: float
) -> dict[str, float]:
    if not 0.0 < angle < math.pi / 2.0:
        raise ValueError("angle must lie in (0, pi/2)")
    if not 0.0 < initial_angle < math.pi / 2.0:
        raise ValueError("initial-angle must lie in (0, pi/2)")
    if math.isclose(angle, initial_angle):
        raise ValueError("angle and initial-angle must differ")
    if not 0.0 < base_angle < math.pi / 2.0:
        raise ValueError("base-angle must lie in (0, pi/2)")

    identity = np.eye(4, dtype=complex)
    e0 = identity[:, [0]]
    e1 = identity[:, [1]]
    e2 = identity[:, [2]]
    e3 = identity[:, [3]]
    q_projection = projection(e0) + projection(e1)
    r_projection = projection(e0)

    initial_vector = (
        math.cos(base_angle) * e1
        + math.sin(base_angle)
        * (
            math.cos(initial_angle) * e2
            + math.sin(initial_angle) * e3
        )
    )
    current_vector = (
        math.cos(base_angle) * e1
        + math.sin(base_angle)
        * (math.cos(angle) * e2 + math.sin(angle) * e3)
    )
    current_velocity = math.sin(base_angle) * (
        -math.sin(angle) * e2 + math.cos(angle) * e3
    )
    base_band = projection(initial_vector)
    current_band = projection(current_vector)
    current_e = r_projection + current_band
    derivative = (
        current_velocity @ current_vector.conj().T
        + current_vector @ current_velocity.conj().T
    )
    kato = commutator(derivative, current_band)

    raw_diagonal = np.array(
        [
            1.0,
            1.0,
            math.cos(angle) / math.cos(initial_angle),
            math.sin(angle) / math.sin(initial_angle),
        ]
    )
    raw_log_derivative = np.array(
        [0.0, 0.0, -math.tan(angle), 1.0 / math.tan(angle)]
    )
    minimum_index = int(np.argmin(raw_diagonal))
    minimum_singular = float(raw_diagonal[minimum_index])
    transport = np.diag(raw_diagonal / minimum_singular).astype(complex)
    source_generator = np.diag(
        raw_log_derivative - raw_log_derivative[minimum_index]
    ).astype(complex)
    metric = transport.conj().T @ transport
    transported_vector = transport @ initial_vector
    transported_vector /= np.linalg.norm(transported_vector)
    source_lower = (
        (identity - current_e) @ source_generator @ current_band
        - r_projection
        @ source_generator.conj().T
        @ q_projection
        @ current_band
    )

    partial_frame = current_vector @ initial_vector.conj().T
    base_frame = initial_vector @ initial_vector.conj().T
    leakage = q_projection @ partial_frame
    base_leakage = q_projection @ base_frame
    leakage_derivative = q_projection @ kato @ partial_frame

    detector = projection(e3)
    route_endpoint = np.trace(detector @ (current_band - base_band))
    route_derivative = np.trace(detector @ derivative)

    return {
        "q_invariance_error": float(
            np.linalg.norm(
                (identity - q_projection) @ source_generator @ q_projection,
                ord="fro",
            )
        ),
        "detector_transport_commutator_error": float(
            np.linalg.norm(commutator(detector, transport), ord="fro")
        ),
        "detector_generator_commutator_error": float(
            np.linalg.norm(
                commutator(detector, source_generator), ord="fro"
            )
        ),
        "minimum_metric_eigenvalue": float(
            np.linalg.eigvalsh(metric).min()
        ),
        "transported_band_error": relative_error(
            projection(transported_vector), current_band
        ),
        "nested_intersection_error": float(
            np.linalg.norm(r_projection @ current_band, ord="fro")
        ),
        "source_flow_error": relative_error(
            source_lower + source_lower.conj().T, derivative
        ),
        "kato_skew_error": relative_error(kato.conj().T, -kato),
        "kato_commutator_error": relative_error(
            commutator(kato, current_band), derivative
        ),
        "leakage_change_norm": float(
            np.linalg.norm(leakage - base_leakage, ord="fro")
        ),
        "leakage_derivative_norm": float(
            np.linalg.norm(leakage_derivative, ord="fro")
        ),
        "leakage_square_error": relative_error(
            leakage @ leakage.conj().T,
            q_projection @ current_band @ q_projection,
        ),
        "route_endpoint_response": float(route_endpoint.real),
        "route_derivative_response": float(route_derivative.real),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--size", type=int, default=8)
    parser.add_argument("--seed", type=int, default=259)
    parser.add_argument("--angle", type=float, default=math.pi / 3.0)
    parser.add_argument("--initial-angle", type=float, default=math.pi / 6.0)
    parser.add_argument("--base-angle", type=float, default=math.pi / 4.0)
    parser.add_argument("--max-algebra-error", type=float, default=1e-11)
    args = parser.parse_args()

    factor = trace_factorization_certificate(args.size, args.seed)
    blindness = leakage_blindness_certificate(
        args.angle, args.initial_angle, args.base_angle
    )
    algebra_errors = [
        value
        for key, value in factor.items()
        if key.endswith("_error")
    ] + [
        value
        for key, value in blindness.items()
        if key.endswith("_error")
    ]
    maximum_error = max(algebra_errors)

    print("identity=kato trace-factorization gate")
    print("status=exact two-factor identity plus leakage-blindness guard")
    print(f"maximum_algebra_error={maximum_error:.12e}")
    print("trace_factorization=BEGIN")
    for key, value in factor.items():
        print(f"{key}={value:.12e}")
    print("trace_factorization=END")
    print("leakage_blindness=BEGIN")
    for key, value in blindness.items():
        print(f"{key}={value:.12e}")
    print("leakage_blindness=END")

    if maximum_error > args.max_algebra_error:
        raise RuntimeError("Kato trace-factorization certificate failed")
    if factor["holder_slack"] < -args.max_algebra_error:
        raise RuntimeError("Hilbert--Schmidt Holder bound failed")
    if abs(blindness["route_endpoint_response"]) < 1e-3:
        raise RuntimeError("leakage-blindness endpoint response vanished")
    if abs(blindness["route_derivative_response"]) < 1e-3:
        raise RuntimeError("leakage-blindness derivative response vanished")
    if blindness["leakage_change_norm"] > args.max_algebra_error:
        raise RuntimeError("covariant leakage was not constant")

    print("certificate=PASS")
    print("covariant_leakage_as_route_trace_owner=REJECTED")
    print("full_kato_generator_two_factor_identity=EXACT")
    print("uniform_localized_generator_bound=OPEN")
    print("same_object_finite_S_trace_identity=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
