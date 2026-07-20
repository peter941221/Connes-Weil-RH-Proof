#!/usr/bin/env python3
"""Finite certificate for Proof 420's relative log-partition cocycle."""

from __future__ import annotations

import argparse
import math

import numpy as np


def random_frame(
    ambient: int, rank: int, rng: np.random.Generator
) -> np.ndarray:
    raw = rng.normal(size=(ambient, rank)) + 1j * rng.normal(
        size=(ambient, rank)
    )
    frame, _ = np.linalg.qr(raw, mode="reduced")
    return frame


def random_invertible(
    dimension: int, scale: float, rng: np.random.Generator
) -> np.ndarray:
    raw = rng.normal(size=(dimension, dimension)) + 1j * rng.normal(
        size=(dimension, dimension)
    )
    raw /= np.linalg.norm(raw, ord=2)
    return np.eye(dimension, dtype=complex) + scale * raw


def positive_logdet(matrix: np.ndarray) -> float:
    hermitian = (matrix + matrix.conj().T) / 2.0
    eigenvalues = np.linalg.eigvalsh(hermitian)
    if float(np.min(eigenvalues)) <= 1.0e-12:
        raise ValueError("Gram matrix is not numerically positive definite")
    return float(np.sum(np.log(eigenvalues)))


def positive_exponential(detector: np.ndarray, parameter: float) -> np.ndarray:
    eigenvalues, eigenvectors = np.linalg.eigh(detector)
    return (eigenvectors * np.exp(parameter * eigenvalues)) @ eigenvectors.conj().T


def projection(frame: np.ndarray) -> np.ndarray:
    gram = frame.conj().T @ frame
    return frame @ np.linalg.solve(gram, frame.conj().T)


def log_partition(
    frame: np.ndarray,
    multiplier: np.ndarray,
    detector: np.ndarray,
    parameter: float,
) -> float:
    moved = multiplier @ frame
    detector_exponential = positive_exponential(detector, parameter)
    tilted_gram = moved.conj().T @ detector_exponential @ moved
    gram = moved.conj().T @ moved
    return positive_logdet(tilted_gram) - positive_logdet(gram)


def relative_log_partition(
    frame: np.ndarray,
    multiplier: np.ndarray,
    detector: np.ndarray,
    parameter: float,
) -> float:
    identity = np.eye(multiplier.shape[0], dtype=complex)
    return log_partition(frame, multiplier, detector, parameter) - log_partition(
        frame, identity, detector, parameter
    )


def matrix_certificate(
    ambient: int,
    rank: int,
    seed: int,
    derivative_step: float,
) -> dict[str, float]:
    rng = np.random.default_rng(seed)
    frame = random_frame(ambient, rank, rng)

    detector_root = rng.normal(size=(ambient, ambient)) + 1j * rng.normal(
        size=(ambient, ambient)
    )
    detector = detector_root.conj().T @ detector_root / ambient
    detector += 0.15 * np.eye(ambient, dtype=complex)

    first = random_invertible(ambient, 0.31, rng)
    second = random_invertible(ambient, 0.27, rng)
    total = second @ first

    coordinate_change = random_invertible(rank, 0.38, rng)
    changed_frame = frame @ coordinate_change

    maximum_frame_error = 0.0
    maximum_chain_error = 0.0
    for parameter in (-0.35, -0.08, 0.19, 0.42):
        direct = relative_log_partition(frame, total, detector, parameter)
        local_first = relative_log_partition(frame, first, detector, parameter)
        local_second = relative_log_partition(
            first @ frame, second, detector, parameter
        )
        changed = relative_log_partition(
            changed_frame, total, detector, parameter
        )
        maximum_frame_error = max(maximum_frame_error, abs(direct - changed))
        maximum_chain_error = max(
            maximum_chain_error, abs(direct - local_first - local_second)
        )

    plus = relative_log_partition(
        frame, total, detector, derivative_step
    )
    minus = relative_log_partition(
        frame, total, detector, -derivative_step
    )
    finite_derivative = (plus - minus) / (2.0 * derivative_step)
    expected_derivative = float(
        np.trace(detector @ (projection(total @ frame) - projection(frame))).real
    )

    first_plus = relative_log_partition(
        frame, first, detector, derivative_step
    )
    first_minus = relative_log_partition(
        frame, first, detector, -derivative_step
    )
    second_plus = relative_log_partition(
        first @ frame, second, detector, derivative_step
    )
    second_minus = relative_log_partition(
        first @ frame, second, detector, -derivative_step
    )
    local_derivative_sum = (
        first_plus - first_minus + second_plus - second_minus
    ) / (2.0 * derivative_step)

    zero_value = relative_log_partition(frame, total, detector, 0.0)

    return {
        "frame_invariance_error": maximum_frame_error,
        "product_chain_error": maximum_chain_error,
        "detector_derivative_error": abs(finite_derivative - expected_derivative),
        "derivative_chain_error": abs(finite_derivative - local_derivative_sum),
        "zero_normalization_error": abs(zero_value),
        "response_magnitude": abs(expected_derivative),
        "first_condition_number": float(np.linalg.cond(first)),
        "second_condition_number": float(np.linalg.cond(second)),
    }


def hardy_terms(
    amplitude: float,
    detector_coupling: float,
    detector_parameter: float,
    nodes: np.ndarray,
) -> dict[str, float]:
    detector_values = 2.0 * detector_coupling * nodes.real
    detector_weight = np.exp(detector_parameter * detector_values)
    inverse_multiplier = 1.0 / (1.0 - amplitude * nodes)
    raw_weight = np.abs(inverse_multiplier) ** 2
    poisson_weight = (1.0 - amplitude**2) * raw_weight

    base_partition = float(np.mean(detector_weight))
    tilted_log = math.log(float(np.mean(raw_weight * detector_weight))) - math.log(
        base_partition
    )
    gram_log = math.log(float(np.mean(raw_weight)))
    completed = tilted_log - gram_log
    poisson_completed = math.log(
        float(np.mean(poisson_weight * detector_weight)) / base_partition
    )

    linear_coefficient = 2.0 * float(
        np.mean(nodes.real * detector_weight)
    ) / base_partition

    derivative_step = 1.0e-6

    def completed_at(parameter: float) -> float:
        weight = np.exp(parameter * detector_values)
        return math.log(
            float(np.mean(poisson_weight * weight)) / float(np.mean(weight))
        )

    detector_derivative = (
        completed_at(derivative_step) - completed_at(-derivative_step)
    ) / (2.0 * derivative_step)

    return {
        "amplitude": amplitude,
        "gram_log": gram_log,
        "tilted_log": tilted_log,
        "completed": completed,
        "poisson_completed": poisson_completed,
        "decomposition_error": abs(completed - poisson_completed),
        "gram_exact_error": abs(gram_log + math.log(1.0 - amplitude**2)),
        "detector_derivative_error": abs(
            detector_derivative - 2.0 * detector_coupling * amplitude
        ),
        "gram_over_a2": gram_log / amplitude**2,
        "tilted_over_a": tilted_log / amplitude,
        "completed_over_a": completed / amplitude,
        "linear_coefficient": linear_coefficient,
    }


def parse_amplitudes(value: str) -> list[float]:
    amplitudes = [float(part.strip()) for part in value.split(",") if part.strip()]
    if not amplitudes or any(not 0.0 < amplitude < 1.0 for amplitude in amplitudes):
        raise argparse.ArgumentTypeError("amplitudes must lie strictly between 0 and 1")
    return amplitudes


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--ambient", type=int, default=14)
    parser.add_argument("--rank", type=int, default=5)
    parser.add_argument("--seed", type=int, default=420)
    parser.add_argument("--derivative-step", type=float, default=2.0e-6)
    parser.add_argument("--circle-nodes", type=int, default=32768)
    parser.add_argument("--detector-coupling", type=float, default=0.35)
    parser.add_argument("--detector-parameter", type=float, default=0.7)
    parser.add_argument(
        "--amplitudes",
        type=parse_amplitudes,
        default=parse_amplitudes("0.2,0.1,0.05,0.025,0.0125,0.00625"),
    )
    parser.add_argument("--tolerance", type=float, default=5.0e-8)
    args = parser.parse_args()

    if not 2 <= args.rank < args.ambient:
        raise SystemExit("rank must satisfy 2 <= rank < ambient")
    if args.circle_nodes < 1024:
        raise SystemExit("circle-nodes must be at least 1024")
    if not 0.0 < args.detector_coupling < 0.5:
        raise SystemExit("detector-coupling must lie between 0 and 1/2")

    matrix_checks = matrix_certificate(
        args.ambient, args.rank, args.seed, args.derivative_step
    )

    nodes = np.exp(
        2j * np.pi * np.arange(args.circle_nodes, dtype=np.float64)
        / args.circle_nodes
    )
    hardy_rows = [
        hardy_terms(
            amplitude,
            args.detector_coupling,
            args.detector_parameter,
            nodes,
        )
        for amplitude in args.amplitudes
    ]

    print("Proof 420 relative log-partition cocycle certificate")
    for label, value in matrix_checks.items():
        print(f"{label}={value:.12e}")

    print(
        "+----------+---------------+---------------+---------------+---------------+"
    )
    print(
        "| a        | Gram / a^2    | tilted / a   | Psi / a      | linear coeff  |"
    )
    print(
        "+----------+---------------+---------------+---------------+---------------+"
    )
    for row in hardy_rows:
        print(
            f"| {row['amplitude']:8.5f} | {row['gram_over_a2']:13.6e} | "
            f"{row['tilted_over_a']:13.6e} | {row['completed_over_a']:13.6e} | "
            f"{row['linear_coefficient']:13.6e} |"
        )
    print(
        "+----------+---------------+---------------+---------------+---------------+"
    )

    exact_matrix_labels = [
        "frame_invariance_error",
        "product_chain_error",
        "detector_derivative_error",
        "derivative_chain_error",
        "zero_normalization_error",
    ]
    maximum_matrix_error = max(matrix_checks[label] for label in exact_matrix_labels)
    maximum_hardy_error = max(
        max(
            row["decomposition_error"],
            row["gram_exact_error"],
            row["detector_derivative_error"],
        )
        for row in hardy_rows
    )

    smallest = min(hardy_rows, key=lambda row: row["amplitude"])
    gram_scale_error = abs(smallest["gram_over_a2"] - 1.0)
    completed_scale_error = abs(
        smallest["completed_over_a"] - smallest["linear_coefficient"]
    )
    tilted_scale_error = abs(
        smallest["tilted_over_a"] - smallest["linear_coefficient"]
    )

    print(f"maximum_matrix_error={maximum_matrix_error:.12e}")
    print(f"maximum_hardy_identity_error={maximum_hardy_error:.12e}")
    print(f"smallest_amplitude_gram_scale_error={gram_scale_error:.12e}")
    print(f"smallest_amplitude_completed_scale_error={completed_scale_error:.12e}")
    print(f"smallest_amplitude_tilted_scale_error={tilted_scale_error:.12e}")

    if maximum_matrix_error > args.tolerance:
        raise SystemExit("finite determinant cocycle identity failed")
    if maximum_hardy_error > args.tolerance:
        raise SystemExit("Hardy Poisson identity failed")
    if gram_scale_error > 2.0e-3:
        raise SystemExit("Gram counterterm did not exhibit quadratic scale")
    if completed_scale_error > 5.0e-3 or tilted_scale_error > 1.0e-2:
        raise SystemExit("detector terms did not retain the linear scale")

    print("relative_log_partition=FRAME_INVARIANT")
    print("multiplicative_chain_rule=EXACT_FINITE")
    print("detector_derivative=ORDERED_PROJECTION_COCYCLE")
    print("gram_counterterm_scale=QUADRATIC")
    print("completed_local_response_scale=LINEAR")
    print("termwise_energy_bound=REJECTED")
    print("global_burnol_square_estimate=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
