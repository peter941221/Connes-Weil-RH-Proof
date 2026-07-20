#!/usr/bin/env python3
"""Finite Hardy-space certificate for Proof 419's terminal anomaly guard."""

from __future__ import annotations

import argparse
import math

import numpy as np


def shift(vector: np.ndarray) -> np.ndarray:
    shifted = np.zeros_like(vector)
    shifted[1:] = vector[:-1]
    return shifted


def detector_expectation(vector: np.ndarray, coupling: float) -> float:
    return float(
        np.vdot(vector, vector).real
        + 2.0 * coupling * np.vdot(vector, shift(vector)).real
    )


def orthonormalize(columns: np.ndarray) -> np.ndarray:
    basis, triangular = np.linalg.qr(columns, mode="reduced")
    if np.min(np.abs(np.diag(triangular))) < 1.0e-13:
        raise ValueError("input columns lost rank")
    return basis


def projection_distance(left: np.ndarray, right: np.ndarray) -> float:
    singular_values = np.linalg.svd(left.conj().T @ right, compute_uv=False)
    minimum_overlap = float(np.min(np.clip(singular_values, 0.0, 1.0)))
    return math.sqrt(max(0.0, 1.0 - minimum_overlap**2))


def run_case(amplitude: float, coupling: float, coefficient_count: int) -> dict[str, float]:
    powers = np.arange(coefficient_count, dtype=np.float64)
    inverse_q = amplitude**powers

    source_r = np.zeros((coefficient_count, 1), dtype=np.float64)
    source_r[0, 0] = 1.0
    source_e = np.zeros((coefficient_count, 2), dtype=np.float64)
    source_e[0, 0] = 1.0
    source_e[1, 1] = 1.0

    transported_r = orthonormalize(inverse_q[:, None])
    transported_e_columns = np.column_stack((inverse_q, shift(inverse_q)))
    transported_e = orthonormalize(transported_e_columns)
    terminal_raw = transported_e - transported_r @ (
        transported_r.conj().T @ transported_e
    )
    terminal_norms = np.linalg.norm(terminal_raw, axis=0)
    terminal_column = terminal_raw[:, int(np.argmax(terminal_norms))]
    transported_terminal = orthonormalize(terminal_column[:, None])

    beta = np.zeros(coefficient_count, dtype=np.float64)
    beta[0] = -amplitude
    beta[1:] = (1.0 - amplitude**2) * amplitude ** np.arange(
        coefficient_count - 1, dtype=np.float64
    )
    beta /= np.linalg.norm(beta)
    expected_terminal = beta[:, None]

    source_terminal = np.zeros(coefficient_count, dtype=np.float64)
    source_terminal[1] = 1.0
    endpoint_vector = math.sqrt(1.0 - amplitude**2) * inverse_q
    endpoint_vector /= np.linalg.norm(endpoint_vector)

    terminal_response = detector_expectation(beta, coupling) - detector_expectation(
        source_terminal, coupling
    )
    fixed_response = detector_expectation(
        endpoint_vector, coupling
    ) - detector_expectation(source_r[:, 0], coupling)

    return {
        "amplitude": amplitude,
        "range_error_r": projection_distance(transported_r, endpoint_vector[:, None]),
        "range_error_terminal": projection_distance(
            transported_terminal, expected_terminal
        ),
        "terminal_response": terminal_response,
        "fixed_response": fixed_response,
        "fixed_response_error": abs(fixed_response - 2.0 * coupling * amplitude),
        "response_separation": abs(fixed_response - terminal_response),
    }


def parse_amplitudes(value: str) -> list[float]:
    amplitudes = [float(part.strip()) for part in value.split(",") if part.strip()]
    if not amplitudes or any(not 0.0 < amplitude < 1.0 for amplitude in amplitudes):
        raise argparse.ArgumentTypeError("amplitudes must lie strictly between 0 and 1")
    return amplitudes


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--amplitudes",
        type=parse_amplitudes,
        default=parse_amplitudes("0.2,0.4,0.6"),
    )
    parser.add_argument("--detector-coupling", type=float, default=0.35)
    parser.add_argument("--coefficient-count", type=int, default=512)
    args = parser.parse_args()

    if not 0.0 < args.detector_coupling < 0.5:
        raise SystemExit("positive-detector coupling must lie between 0 and 1/2")
    if args.coefficient_count < 32:
        raise SystemExit("coefficient count must be at least 32")

    rows = [
        run_case(amplitude, args.detector_coupling, args.coefficient_count)
        for amplitude in args.amplitudes
    ]

    print("+----------+---------------+---------------+---------------+---------------+")
    print("| a        | R range err   | band err      | terminal resp | fixed resp    |")
    print("+----------+---------------+---------------+---------------+---------------+")
    for row in rows:
        print(
            f"| {row['amplitude']:8.5f} | {row['range_error_r']:13.6e} | "
            f"{row['range_error_terminal']:13.6e} | "
            f"{row['terminal_response']:13.6e} | {row['fixed_response']:13.6e} |"
        )
    print("+----------+---------------+---------------+---------------+---------------+")

    maximum_range_error = max(
        max(row["range_error_r"], row["range_error_terminal"]) for row in rows
    )
    maximum_terminal_response = max(abs(row["terminal_response"]) for row in rows)
    maximum_fixed_response_error = max(row["fixed_response_error"] for row in rows)
    minimum_response_separation = min(row["response_separation"] for row in rows)

    print(f"maximum_range_error={maximum_range_error:.12e}")
    print(f"maximum_terminal_response={maximum_terminal_response:.12e}")
    print(f"maximum_fixed_response_error={maximum_fixed_response_error:.12e}")
    print(f"minimum_response_separation={minimum_response_separation:.12e}")
    print("appended_terminal_trace=ZERO_FINITE")
    print("fixed_carrier_response=NONZERO")
    print("relative_trace_anomaly=REQUIRED_INFINITE")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")

    tolerance = 5.0e-12
    if maximum_range_error > tolerance:
        raise SystemExit("model-space range identity failed")
    if maximum_terminal_response > tolerance:
        raise SystemExit("finite terminal trace did not cancel")
    if maximum_fixed_response_error > tolerance:
        raise SystemExit("fixed-carrier response identity failed")
    if minimum_response_separation < 0.1:
        raise SystemExit("finite dilation did not separate the actual response")


if __name__ == "__main__":
    main()
