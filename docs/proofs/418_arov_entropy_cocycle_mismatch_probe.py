#!/usr/bin/env python3
"""Finite certificate for Proof 418's Arov/cocycle mismatch."""

from __future__ import annotations

import argparse
import math

import numpy as np


def projection(vector: np.ndarray) -> np.ndarray:
    normalized = vector / np.linalg.norm(vector)
    return np.outer(normalized, normalized.conj())


def run_amplitude(amplitude: float, detector_coupling: float) -> dict[str, float]:
    unitary = np.array([[0.0, 1.0], [1.0, 0.0]])
    source_projection = np.diag([1.0, 0.0])
    detector = np.eye(2) + detector_coupling * unitary
    transport = np.eye(2) - amplitude * unitary

    frame = np.array([1.0, amplitude]) / math.sqrt(1.0 + amplitude**2)
    transported_projection = projection(frame)
    response = float(
        np.trace(detector @ (transported_projection - source_projection)).real
    )
    expected_response = 2.0 * detector_coupling * amplitude / (1.0 + amplitude**2)

    schur_frame = float((transport @ frame)[0])
    forward = schur_frame / (1.0 + amplitude)
    inverse = (1.0 - amplitude) / schur_frame
    scalar_gauge = (1.0 - amplitude) / (1.0 + amplitude)

    alpha_zero = float(detector[0, 0])
    alpha_one = float(frame @ detector @ frame)
    local_defect = forward * alpha_one * inverse - scalar_gauge * alpha_zero
    normalized_cocycle = local_defect / scalar_gauge

    entropy = -math.log1p(-(amplitude**2))
    expected_node_gap = (
        4.0
        * amplitude**2
        / ((1.0 + amplitude) ** 2 * (1.0 + amplitude**2))
    )
    node_gap = inverse**2 - forward**2

    return {
        "amplitude": amplitude,
        "response": response,
        "response_error": abs(response - expected_response),
        "pair_error": abs(forward * inverse - scalar_gauge),
        "cocycle_error": abs(normalized_cocycle - response),
        "entropy": entropy,
        "response_over_entropy": response / entropy,
        "response_over_sqrt_entropy": response / math.sqrt(entropy),
        "node_gap": node_gap,
        "node_gap_error": abs(node_gap - expected_node_gap),
        "forward_defect": 1.0 - forward**2,
        "inverse_defect": 1.0 - inverse**2,
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
        default=parse_amplitudes("0.2,0.1,0.05,0.025,0.0125"),
    )
    parser.add_argument("--detector-coupling", type=float, default=0.4)
    args = parser.parse_args()

    if not 0.0 < args.detector_coupling < 1.0:
        raise SystemExit("detector coupling must lie strictly between 0 and 1")

    rows = [
        run_amplitude(amplitude, args.detector_coupling)
        for amplitude in args.amplitudes
    ]

    print("+----------+---------------+---------------+---------------+---------------+")
    print("| a        | response      | entropy       | q / entropy   | q / sqrt(E)   |")
    print("+----------+---------------+---------------+---------------+---------------+")
    for row in rows:
        print(
            f"| {row['amplitude']:8.5f} | {row['response']:13.6e} | "
            f"{row['entropy']:13.6e} | {row['response_over_entropy']:13.6e} | "
            f"{row['response_over_sqrt_entropy']:13.6e} |"
        )
    print("+----------+---------------+---------------+---------------+---------------+")

    maximum_response_error = max(row["response_error"] for row in rows)
    maximum_pair_error = max(row["pair_error"] for row in rows)
    maximum_cocycle_error = max(row["cocycle_error"] for row in rows)
    maximum_node_gap_error = max(row["node_gap_error"] for row in rows)
    minimum_node_gap = min(row["node_gap"] for row in rows)
    minimum_forward_defect = min(row["forward_defect"] for row in rows)
    minimum_inverse_defect = min(row["inverse_defect"] for row in rows)
    energy_ratio_growth = (
        rows[-1]["response_over_entropy"] / rows[0]["response_over_entropy"]
    )
    square_root_limit_error = abs(
        rows[-1]["response_over_sqrt_entropy"]
        - 2.0 * args.detector_coupling
    )

    print(f"maximum_response_error={maximum_response_error:.12e}")
    print(f"maximum_pair_error={maximum_pair_error:.12e}")
    print(f"maximum_cocycle_error={maximum_cocycle_error:.12e}")
    print(f"maximum_node_gap_error={maximum_node_gap_error:.12e}")
    print(f"minimum_node_gap={minimum_node_gap:.12e}")
    print(f"minimum_forward_defect={minimum_forward_defect:.12e}")
    print(f"minimum_inverse_defect={minimum_inverse_defect:.12e}")
    print(f"energy_ratio_growth={energy_ratio_growth:.12e}")
    print(f"square_root_limit_error={square_root_limit_error:.12e}")
    print("direct_arov_energy_to_cocycle=REJECTED_ANALYTICALLY")
    print("paired_odd_term=NONZERO")
    print("scalar_lossless_diagonal=IMPOSSIBLE")
    print("burnol_localized_entropy=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")

    tolerance = 5.0e-13
    if maximum_response_error > tolerance:
        raise SystemExit("projection response identity failed")
    if maximum_pair_error > tolerance or maximum_cocycle_error > tolerance:
        raise SystemExit("paired cocycle identity failed")
    if maximum_node_gap_error > tolerance or minimum_node_gap <= 0.0:
        raise SystemExit("lossless-node diagonal obstruction failed")
    if minimum_forward_defect <= 0.0 or minimum_inverse_defect <= 0.0:
        raise SystemExit("Schur/Markov contractions were not strict")
    if energy_ratio_growth < 10.0:
        raise SystemExit("entropy mismatch cohort did not expose 1/a growth")
    if square_root_limit_error > 0.02:
        raise SystemExit("square-root entropy scale did not approach 2c")


if __name__ == "__main__":
    main()
