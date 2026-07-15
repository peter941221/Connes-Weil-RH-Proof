#!/usr/bin/env python3
"""Certificate for the Schur envelope and common-history guards.

The script checks four independent facts used by Proof 268:

  * the derivative of a Schur shorting is Z* X' Z;
  * the lifted constant/full covariance first jet equals the derivative of the
    relative shorted determinant;
  * compact support removes relative crossing traces after common translation
    history is cancelled, not raw paths one by one;
  * a raw one-prime innovation defect has size 4a/(1+a)^2 = O(a), so prime
    martingale orthogonality before the detector/Sonin cancellation retains the
    forbidden p^(-1/2) scale.

The finite models certify algebra and explicit guards only.  They do not prove
the source compact-support stopping theorem.
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


def relative_error(
    actual: complex | np.ndarray, expected: complex | np.ndarray
) -> float:
    actual_array = np.asarray(actual)
    expected_array = np.asarray(expected)
    scale = max(float(np.linalg.norm(expected_array)), 1.0)
    return float(np.linalg.norm(actual_array - expected_array) / scale)


def cyclic_shift(size: int, amount: int) -> np.ndarray:
    return np.roll(np.eye(size, dtype=complex), amount, axis=0)


def zero_fill_shift(size: int, amount: int) -> np.ndarray:
    shift = np.zeros((size, size), dtype=complex)
    if amount >= 0:
        shift[amount:, : size - amount] = np.eye(size - amount)
    else:
        positive = -amount
        shift[: size - positive, positive:] = np.eye(size - positive)
    return shift


def hermitian_exponential(matrix: np.ndarray, parameter: float) -> np.ndarray:
    eigenvalues, eigenvectors = np.linalg.eigh(
        (matrix + matrix.conj().T) / 2.0
    )
    return (
        eigenvectors
        @ np.diag(np.exp(parameter * eigenvalues))
        @ eigenvectors.conj().T
    )


def schur_data(
    operator: np.ndarray,
    complement_basis: np.ndarray,
    band_basis: np.ndarray,
) -> tuple[np.ndarray, np.ndarray]:
    complement_block = complement_basis.conj().T @ operator @ complement_basis
    complement_band = complement_basis.conj().T @ operator @ band_basis
    graph = band_basis - complement_basis @ np.linalg.solve(
        complement_block, complement_band
    )
    shorted = graph.conj().T @ operator @ graph
    return graph, shorted


def schur_envelope_certificate(
    size: int, seed: int, derivative_step: float
) -> dict[str, float]:
    if size < 12:
        raise ValueError("Schur envelope size must be at least twelve")

    rng = np.random.default_rng(seed)
    c_rank = size // 3
    b_rank = size - c_rank
    c_basis = coordinate_basis(size, 0, c_rank)
    b_basis = coordinate_basis(size, c_rank, size)

    random = rng.normal(size=(size, size)) + 1j * rng.normal(
        size=(size, size)
    )
    operator = random.conj().T @ random / size + 1.2 * np.eye(size)
    tangent_random = rng.normal(size=(size, size)) + 1j * rng.normal(
        size=(size, size)
    )
    tangent = (tangent_random + tangent_random.conj().T) / 2.0
    tangent *= 0.15 / max(float(np.linalg.norm(tangent, ord=2)), 1.0)

    graph, shorted = schur_data(operator, c_basis, b_basis)
    expected_derivative = graph.conj().T @ tangent @ graph
    _, shorted_plus = schur_data(
        operator + derivative_step * tangent, c_basis, b_basis
    )
    _, shorted_minus = schur_data(
        operator - derivative_step * tangent, c_basis, b_basis
    )
    finite_difference = (shorted_plus - shorted_minus) / (
        2.0 * derivative_step
    )

    return {
        "schur_factorization_error": relative_error(
            shorted, graph.conj().T @ operator @ graph
        ),
        "schur_orthogonality_error": float(
            np.linalg.norm(c_basis.conj().T @ operator @ graph)
        ),
        "schur_envelope_derivative_error": relative_error(
            finite_difference, expected_derivative
        ),
    }


def circulant_detector(size: int) -> np.ndarray:
    root = (
        np.eye(size, dtype=complex)
        + (0.21 - 0.08j) * cyclic_shift(size, 1)
        - (0.13 + 0.04j) * cyclic_shift(size, 2)
    )
    return root.conj().T @ root


def lifted_first_jet_certificate(
    size: int, derivative_step: float
) -> dict[str, float]:
    if size < 8 or size % 4 != 0:
        raise ValueError("lifted first-jet size must be divisible by four")

    identity = np.eye(size, dtype=complex)
    probabilities = np.array([0.57, 0.28, 0.15], dtype=float)
    unitaries = [
        cyclic_shift(size, 0),
        cyclic_shift(size, 1),
        cyclic_shift(size, 3),
    ]
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
    inverse_metric = dilation.conj().T @ constant_projection @ dilation

    c_rank = size // 4
    c_basis = coordinate_basis(size, 0, c_rank)
    b_basis = coordinate_basis(size, c_rank, size)
    graph, gamma = schur_data(inverse_metric, c_basis, b_basis)
    detector = circulant_detector(size)
    lifted_detector = np.kron(
        np.eye(len(probabilities), dtype=complex), detector
    )
    constant_frame = constant_projection @ dilation @ graph
    full_frame = dilation @ b_basis
    lifted_response = np.trace(
        constant_frame.conj().T
        @ lifted_detector
        @ constant_frame
        @ np.linalg.inv(gamma)
        - full_frame.conj().T @ lifted_detector @ full_frame
    )

    def log_shorted_ratio(parameter: float) -> complex:
        inverse_exponential = hermitian_exponential(detector, -parameter)
        markov_deformation = inverse_metric @ inverse_exponential
        _, markov_shorted = schur_data(
            markov_deformation, c_basis, b_basis
        )
        _, reference_shorted = schur_data(
            inverse_exponential, c_basis, b_basis
        )
        ratio = gamma @ np.linalg.inv(markov_shorted) @ reference_shorted
        return np.log(np.linalg.det(ratio))

    determinant_derivative = (
        log_shorted_ratio(derivative_step)
        - log_shorted_ratio(-derivative_step)
    ) / (2.0 * derivative_step)

    return {
        "constant_frame_gram_error": relative_error(
            constant_frame.conj().T @ constant_frame, gamma
        ),
        "full_frame_isometry_error": relative_error(
            full_frame.conj().T @ full_frame,
            np.eye(b_basis.shape[1], dtype=complex),
        ),
        "lifted_first_jet_error": relative_error(
            determinant_derivative, lifted_response
        ),
    }


def path_defect(
    outer: np.ndarray,
    detector: np.ndarray,
    first_shift: np.ndarray,
    second_shift: np.ndarray,
) -> np.ndarray:
    first = (
        outer
        @ first_shift.conj().T
        @ outer
        @ detector
        @ outer
        @ second_shift
        @ outer
    )
    covariance = (
        outer
        @ first_shift.conj().T
        @ outer
        @ second_shift
        @ outer
    )
    return first - outer @ detector @ outer @ covariance


def common_history_certificate(size: int) -> tuple[dict[str, float], float]:
    if size < 120 or size % 2 != 0:
        raise ValueError("common-history size must be even and at least 120")

    origin = size // 2
    identity = np.eye(size, dtype=complex)
    outer = np.zeros((size, size), dtype=complex)
    outer[np.arange(origin, size), np.arange(origin, size)] = 1.0
    detector = (
        identity
        + 0.31 * zero_fill_shift(size, 1)
        + 0.31 * zero_fill_shift(size, -1)
    )
    local_basis = coordinate_basis(size, origin, origin + 24)

    forward = path_defect(
        outer,
        detector,
        zero_fill_shift(size, 7),
        zero_fill_shift(size, 8),
    )
    backward = path_defect(
        outer,
        detector,
        zero_fill_shift(size, 8),
        zero_fill_shift(size, 7),
    )
    shifted_backward = path_defect(
        outer,
        detector,
        zero_fill_shift(size, 18),
        zero_fill_shift(size, 17),
    )
    far_backward = path_defect(
        outer,
        detector,
        zero_fill_shift(size, 14),
        zero_fill_shift(size, 7),
    )

    forward_local = local_basis.conj().T @ forward @ local_basis
    backward_local = local_basis.conj().T @ backward @ local_basis
    shifted_local = local_basis.conj().T @ shifted_backward @ local_basis
    far_local = local_basis.conj().T @ far_backward @ local_basis
    near_trace_mass = float(abs(np.trace(backward_local)))

    checks = {
        "forward_common_history_error": float(np.linalg.norm(forward_local)),
        "common_translation_error": relative_error(
            shifted_local, backward_local
        ),
        "far_relative_trace_error": float(abs(np.trace(far_local))),
    }
    return checks, near_trace_mass


def innovation_half_power_certificate() -> tuple[dict[str, float], float]:
    grid = np.linspace(-math.pi, math.pi, 20001)
    maximum_error = 0.0
    minimum_ratio = float("inf")
    checks: dict[str, float] = {}
    for index, coefficient in enumerate((0.08, 0.16, 0.32, 0.48), start=1):
        multiplier = (1.0 - coefficient) / (
            1.0 - coefficient * np.exp(1j * grid)
        )
        measured = float(np.max(1.0 - np.abs(multiplier) ** 2))
        expected = 4.0 * coefficient / (1.0 + coefficient) ** 2
        error = abs(measured - expected)
        maximum_error = max(maximum_error, error)
        minimum_ratio = min(minimum_ratio, measured / coefficient)
        checks[f"one_prime_defect_error_{index}"] = error
    return checks, minimum_ratio


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
    parser.add_argument("--seed", type=int, default=268)
    parser.add_argument("--derivative-step", type=float, default=1e-6)
    parser.add_argument("--history-size", type=int, default=160)
    parser.add_argument("--tolerance", type=float, default=1e-7)
    parser.add_argument("--minimum-near-trace", type=float, default=0.1)
    parser.add_argument("--minimum-defect-ratio", type=float, default=1.0)
    args = parser.parse_args()

    envelope = schur_envelope_certificate(
        args.size, args.seed, args.derivative_step
    )
    lifted = lifted_first_jet_certificate(
        args.size, args.derivative_step
    )
    history, near_trace_mass = common_history_certificate(args.history_size)
    innovation, minimum_defect_ratio = innovation_half_power_certificate()

    print_table("Schur envelope derivative", envelope)
    print()
    print_table("lifted constant/full first jet", lifted)
    print()
    print_table("common-history crossing guard", history)
    print(f"near relative trace mass: {near_trace_mass:.6e}")
    print()
    print_table("raw one-prime innovation guard", innovation)
    print(f"minimum defect/coefficient ratio: {minimum_defect_ratio:.6e}")

    maximum_error = max(
        *envelope.values(), *lifted.values(), *history.values(), *innovation.values()
    )
    print(f"maximum checked error: {maximum_error:.6e}")
    if near_trace_mass < args.minimum_near_trace:
        raise SystemExit("guard failed: near relative crossing vanished")
    if minimum_defect_ratio < args.minimum_defect_ratio:
        raise SystemExit("guard failed: raw innovation gained a square")
    if maximum_error > args.tolerance:
        raise SystemExit(
            f"certificate failed: {maximum_error:.6e} > {args.tolerance:.6e}"
        )


if __name__ == "__main__":
    main()
