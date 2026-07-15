#!/usr/bin/env python3
"""Certificate for the nested relative Jacobi cocycle.

The first layer verifies three exact finite-dimensional descriptions of the
same nested metric response:

  * the direct transported-projection trace;
  * the logarithmic derivative of tau_E / tau_R;
  * the determinant of one shorted inverse-metric covariance ratio on B.

It also verifies the relative Jacobi complementary formula for each source
projection.  The second layer checks the causal identification of the base
shorted covariance with Gamma = (E A B)* (E A B).  The third layer checks the
four-channel random-unitary dilation.  The unilateral-shift layer retains the
central trace-anomaly guard from Proof 264.

Finite matrices certify algebra only.  They do not prove the continuous
relative determinant theorem or the S-uniform compact-support estimate.
"""

from __future__ import annotations

import argparse
import math

import numpy as np


def projection(columns: np.ndarray) -> np.ndarray:
    return columns @ columns.conj().T


def coordinate_basis(
    size: int, start: int, stop: int
) -> np.ndarray:
    basis = np.zeros((size, stop - start), dtype=complex)
    basis[np.arange(start, stop), np.arange(stop - start)] = 1.0
    return basis


def coordinate_projection(size: int, start: int, stop: int) -> np.ndarray:
    return projection(coordinate_basis(size, start, stop))


def relative_error(
    actual: complex | np.ndarray, expected: complex | np.ndarray
) -> float:
    actual_array = np.asarray(actual)
    expected_array = np.asarray(expected)
    scale = max(float(np.linalg.norm(expected_array)), 1.0)
    return float(np.linalg.norm(actual_array - expected_array) / scale)


def commutator(left: np.ndarray, right: np.ndarray) -> np.ndarray:
    return left @ right - right @ left


def cyclic_shift(size: int, amount: int) -> np.ndarray:
    return np.roll(np.eye(size, dtype=complex), amount, axis=0)


def hermitian_exponential(matrix: np.ndarray, parameter: float) -> np.ndarray:
    eigenvalues, eigenvectors = np.linalg.eigh(
        (matrix + matrix.conj().T) / 2.0
    )
    return (
        eigenvectors
        @ np.diag(np.exp(parameter * eigenvalues))
        @ eigenvectors.conj().T
    )


def extended_compression(
    source: np.ndarray, operator: np.ndarray
) -> np.ndarray:
    identity = np.eye(source.shape[0], dtype=complex)
    return source @ operator @ source + identity - source


def metric_projection(
    source: np.ndarray, transport: np.ndarray, metric: np.ndarray
) -> np.ndarray:
    inverse = np.linalg.inv(extended_compression(source, metric))
    return transport @ source @ inverse @ source @ transport.conj().T


def relative_tau_operator(
    source: np.ndarray,
    metric: np.ndarray,
    detector_exponential: np.ndarray,
) -> np.ndarray:
    deformed_metric = extended_compression(
        source, detector_exponential @ metric
    )
    base_inverse = np.linalg.inv(extended_compression(source, metric))
    reference_inverse = np.linalg.inv(
        extended_compression(source, detector_exponential)
    )
    return deformed_metric @ base_inverse @ reference_inverse


def complement_tau_operator(
    source: np.ndarray,
    inverse_metric: np.ndarray,
    inverse_detector_exponential: np.ndarray,
) -> np.ndarray:
    identity = np.eye(source.shape[0], dtype=complex)
    complement = identity - source
    deformed_covariance = extended_compression(
        complement, inverse_metric @ inverse_detector_exponential
    )
    base_inverse = np.linalg.inv(
        extended_compression(complement, inverse_metric)
    )
    reference_inverse = np.linalg.inv(
        extended_compression(complement, inverse_detector_exponential)
    )
    return deformed_covariance @ base_inverse @ reference_inverse


def shorted_on_band(
    operator: np.ndarray,
    outer_complement: np.ndarray,
    band_basis: np.ndarray,
) -> np.ndarray:
    complement_inverse = np.linalg.inv(
        extended_compression(outer_complement, operator)
    )
    shorted = (
        operator
        - operator
        @ outer_complement
        @ complement_inverse
        @ outer_complement
        @ operator
    )
    return band_basis.conj().T @ shorted @ band_basis


def circulant_detector(size: int) -> np.ndarray:
    root = (
        np.eye(size, dtype=complex)
        + (0.23 - 0.09j) * cyclic_shift(size, 1)
        + (-0.17 + 0.06j) * cyclic_shift(size, 3)
    )
    return root.conj().T @ root


def nested_jacobi_certificate(
    size: int, detector_parameter: float, derivative_step: float
) -> dict[str, float]:
    if size < 12 or size % 4 != 0:
        raise ValueError("nested certificate size must be divisible by four")

    identity = np.eye(size, dtype=complex)
    transport = (
        identity - 0.31 * cyclic_shift(size, 1)
    ) @ (
        identity - 0.19 * cyclic_shift(size, 3)
    )
    metric = transport.conj().T @ transport
    inverse_metric = np.linalg.inv(metric)
    detector = circulant_detector(size)

    r_rank = size // 4
    e_rank = 3 * size // 4
    inner = coordinate_projection(size, 0, r_rank)
    outer = coordinate_projection(size, 0, e_rank)
    band = outer - inner
    outer_complement = identity - outer
    band_basis = coordinate_basis(size, r_rank, e_rank)

    transported_outer = metric_projection(outer, transport, metric)
    transported_inner = metric_projection(inner, transport, metric)
    direct_response = np.trace(
        detector
        @ (transported_outer - transported_inner - band)
    )

    def tau(source: np.ndarray, parameter: float) -> complex:
        exponential = hermitian_exponential(detector, parameter)
        operator = relative_tau_operator(source, metric, exponential)
        return np.linalg.det(operator)

    def complement_tau(source: np.ndarray, parameter: float) -> complex:
        inverse_exponential = hermitian_exponential(detector, -parameter)
        operator = complement_tau_operator(
            source, inverse_metric, inverse_exponential
        )
        return np.linalg.det(operator)

    exponential = hermitian_exponential(detector, detector_parameter)
    inverse_exponential = hermitian_exponential(
        detector, -detector_parameter
    )
    tau_outer = tau(outer, detector_parameter)
    tau_inner = tau(inner, detector_parameter)
    complement_outer = complement_tau(outer, detector_parameter)
    complement_inner = complement_tau(inner, detector_parameter)
    quotient = tau_outer / tau_inner

    covariance_s = inverse_metric @ inverse_exponential
    shorted_covariance_0 = shorted_on_band(
        inverse_metric, outer_complement, band_basis
    )
    shorted_covariance_s = shorted_on_band(
        covariance_s, outer_complement, band_basis
    )
    shorted_reference_s = shorted_on_band(
        inverse_exponential, outer_complement, band_basis
    )
    shorted_ratio = (
        shorted_covariance_0
        @ np.linalg.inv(shorted_covariance_s)
        @ shorted_reference_s
    )
    shorted_determinant = np.linalg.det(shorted_ratio)

    def log_quotient(parameter: float) -> complex:
        return np.log(tau(outer, parameter) / tau(inner, parameter))

    derivative = (
        log_quotient(derivative_step)
        - log_quotient(-derivative_step)
    ) / (2.0 * derivative_step)

    relative_outer = relative_tau_operator(outer, metric, exponential)
    relative_inner = relative_tau_operator(inner, metric, exponential)
    complement_outer_operator = complement_tau_operator(
        outer, inverse_metric, inverse_exponential
    )
    complement_inner_operator = complement_tau_operator(
        inner, inverse_metric, inverse_exponential
    )

    return {
        "detector_metric_commutator": float(
            np.linalg.norm(commutator(detector, metric))
        ),
        "outer_relative_jacobi_error": relative_error(
            np.linalg.det(relative_outer),
            np.linalg.det(complement_outer_operator),
        ),
        "inner_relative_jacobi_error": relative_error(
            np.linalg.det(relative_inner),
            np.linalg.det(complement_inner_operator),
        ),
        "nested_complement_quotient_error": relative_error(
            quotient, complement_outer / complement_inner
        ),
        "shorted_determinant_error": relative_error(
            shorted_determinant, quotient
        ),
        "determinant_derivative_error": relative_error(
            derivative, direct_response
        ),
        "tau_operator_base_error": max(
            relative_error(
                relative_tau_operator(outer, metric, identity), identity
            ),
            relative_error(
                relative_tau_operator(inner, metric, identity), identity
            ),
        ),
    }


def stable_invertible(
    rng: np.random.Generator, size: int, scale: float
) -> np.ndarray:
    random = rng.normal(size=(size, size)) + 1j * rng.normal(
        size=(size, size)
    )
    random /= max(float(np.linalg.norm(random, ord=2)), 1.0)
    return np.eye(size, dtype=complex) + scale * random


def causal_shorted_certificate(size: int, seed: int) -> dict[str, float]:
    if size < 12:
        raise ValueError("causal certificate size must be at least twelve")

    rng = np.random.default_rng(seed)
    c_rank = size // 3
    e_rank = size - c_rank
    r_rank = e_rank // 3
    c_basis = coordinate_basis(size, 0, c_rank)
    e_basis = coordinate_basis(size, c_rank, size)
    b_basis = e_basis[:, r_rank:]
    c_projection = projection(c_basis)
    e_projection = projection(e_basis)

    a_c = stable_invertible(rng, c_rank, 0.16)
    a_e = stable_invertible(rng, e_rank, 0.14)
    crossing = rng.normal(size=(c_rank, e_rank)) + 1j * rng.normal(
        size=(c_rank, e_rank)
    )
    crossing *= 0.1 / max(float(np.linalg.norm(crossing, ord=2)), 1.0)
    causal_inverse = np.block(
        [
            [a_c, crossing],
            [np.zeros((e_rank, c_rank), dtype=complex), a_e],
        ]
    )
    inverse_metric = causal_inverse.conj().T @ causal_inverse
    shorted_covariance = shorted_on_band(
        inverse_metric, c_projection, b_basis
    )
    killed_band = e_projection @ causal_inverse @ b_basis
    gamma = killed_band.conj().T @ killed_band

    return {
        "causal_orientation_error": float(
            np.linalg.norm(e_projection @ causal_inverse @ c_projection)
        ),
        "shorted_gamma_error": relative_error(shorted_covariance, gamma),
    }


def random_unitary_dilation_certificate(size: int) -> dict[str, float]:
    if size < 8 or size % 4 != 0:
        raise ValueError("dilation size must be divisible by four")

    identity = np.eye(size, dtype=complex)
    probabilities = np.array([0.58, 0.29, 0.13], dtype=float)
    unitaries = [
        cyclic_shift(size, 0),
        cyclic_shift(size, 1),
        cyclic_shift(size, 3),
    ]
    causal_inverse = sum(
        probability * unitary
        for probability, unitary in zip(probabilities, unitaries)
    )
    dilation = np.vstack(
        [
            math.sqrt(probability) * unitary
            for probability, unitary in zip(probabilities, unitaries)
        ]
    )
    constants = np.vstack(
        [
            math.sqrt(probability) * identity
            for probability in probabilities
        ]
    )
    constant_projection = constants @ constants.conj().T
    detector = circulant_detector(size)
    inverse_detector_exponential = hermitian_exponential(detector, -0.17)
    lifted_detector_exponential = np.kron(
        np.eye(len(probabilities), dtype=complex),
        inverse_detector_exponential,
    )

    c_rank = size // 4
    r_rank = size // 4
    b_start = c_rank + r_rank
    c_projection = coordinate_projection(size, 0, c_rank)
    r_projection = coordinate_projection(size, c_rank, b_start)
    b_basis = coordinate_basis(size, b_start, size)
    b_projection = projection(b_basis)
    e_projection = r_projection + b_projection

    random_channel = (
        np.eye(3 * size, dtype=complex) - constant_projection
    ) @ dilation @ b_basis
    c_channel = c_projection @ causal_inverse @ b_basis
    r_channel = r_projection @ causal_inverse @ b_basis
    b_channel = b_projection @ causal_inverse @ b_basis
    channel_gram = sum(
        channel.conj().T @ channel
        for channel in (random_channel, c_channel, r_channel, b_channel)
    )
    gamma = (
        r_channel.conj().T @ r_channel
        + b_channel.conj().T @ b_channel
    )
    killed_band = e_projection @ causal_inverse @ b_basis
    delta = (
        random_channel.conj().T @ random_channel
        + c_channel.conj().T @ c_channel
    )

    return {
        "dilation_isometry_error": relative_error(
            dilation.conj().T @ dilation, identity
        ),
        "constant_embedding_error": relative_error(
            constants.conj().T @ constants, identity
        ),
        "average_factor_error": relative_error(
            constants.conj().T @ dilation, causal_inverse
        ),
        "inverse_metric_lift_error": relative_error(
            dilation.conj().T
            @ constant_projection
            @ dilation,
            causal_inverse.conj().T @ causal_inverse,
        ),
        "reference_detector_lift_error": relative_error(
            dilation.conj().T
            @ lifted_detector_exponential
            @ dilation,
            inverse_detector_exponential,
        ),
        "markov_detector_lift_error": relative_error(
            dilation.conj().T
            @ constant_projection
            @ lifted_detector_exponential
            @ dilation,
            causal_inverse.conj().T
            @ causal_inverse
            @ inverse_detector_exponential,
        ),
        "conservative_channel_error": relative_error(
            channel_gram, np.eye(b_basis.shape[1], dtype=complex)
        ),
        "gamma_channel_error": relative_error(
            gamma, killed_band.conj().T @ killed_band
        ),
        "delta_channel_error": relative_error(
            delta,
            np.eye(b_basis.shape[1], dtype=complex) - gamma,
        ),
    }


def anomaly_guard(size: int, time: float) -> dict[str, float]:
    shift = np.zeros((size, size), dtype=complex)
    shift[1:, :-1] = np.eye(size - 1)
    real_part = (shift + shift.conj().T) / 2.0
    imaginary_part = (shift - shift.conj().T) / (2.0j)
    detector = imaginary_part + 2.0 * np.eye(size)
    similarity = hermitian_exponential(real_part, time)
    inverse_similarity = hermitian_exponential(real_part, -time)
    difference = similarity @ detector @ inverse_similarity - detector
    third = size // 3
    target = -0.5j * time
    left = np.trace(difference[:third, :third])
    middle = np.trace(difference[third:-third, third:-third])
    right = np.trace(difference[-third:, -third:])

    return {
        "left_boundary_error": float(abs(left - target)),
        "middle_boundary_error": float(abs(middle)),
        "right_boundary_error": float(abs(right + target)),
        "finite_total_trace": float(abs(np.trace(difference))),
        "detector_positivity_violation": max(
            0.0, float(1.0 - np.linalg.eigvalsh(detector).min())
        ),
    }


def print_table(title: str, values: dict[str, float]) -> None:
    print(title)
    print("+--------------------------------------+---------------+")
    print("| check                                | value         |")
    print("+--------------------------------------+---------------+")
    for label, value in values.items():
        print(f"| {label:<36} | {value:>13.6e} |")
    print("+--------------------------------------+---------------+")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--size", type=int, default=16)
    parser.add_argument("--seed", type=int, default=267)
    parser.add_argument("--detector-parameter", type=float, default=0.17)
    parser.add_argument("--derivative-step", type=float, default=1e-6)
    parser.add_argument("--anomaly-size", type=int, default=96)
    parser.add_argument("--anomaly-time", type=float, default=0.7)
    parser.add_argument("--tolerance", type=float, default=1e-7)
    args = parser.parse_args()

    nested = nested_jacobi_certificate(
        args.size, args.detector_parameter, args.derivative_step
    )
    causal = causal_shorted_certificate(args.size, args.seed)
    dilation = random_unitary_dilation_certificate(args.size)
    anomaly = anomaly_guard(args.anomaly_size, args.anomaly_time)

    print_table("nested relative Jacobi cocycle", nested)
    print()
    print_table("causal shorted covariance", causal)
    print()
    print_table("random-unitary conservative channels", dilation)
    print()
    print_table("central trace-anomaly boundary guard", anomaly)

    maximum_error = max(
        *nested.values(), *causal.values(), *dilation.values(), *anomaly.values()
    )
    print(f"maximum checked error: {maximum_error:.6e}")
    if maximum_error > args.tolerance:
        raise SystemExit(
            f"certificate failed: {maximum_error:.6e} > {args.tolerance:.6e}"
        )


if __name__ == "__main__":
    main()
