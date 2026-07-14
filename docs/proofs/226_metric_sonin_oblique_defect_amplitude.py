#!/usr/bin/env python3
"""Finite-matrix certificate for Proof 226's amplitude identities.

The exact proof is operator algebra.  This script independently checks the
common-range oblique/orthogonal projection identities, the positive defect
square, its Schur-complement factorization, the trace penalty, and the
uniformly convergent compressed-metric Neumann expansion.

It does not test the infinite-dimensional smoothed-commutator theorem, a
bounded pre-root completion, or the final route sign.
"""

from __future__ import annotations

import argparse
import math

import numpy as np


def deterministic_unitary(size: int) -> np.ndarray:
    frequencies = np.fft.fft(np.eye(size), axis=0) / math.sqrt(size)
    phases = np.exp(
        2j * np.pi * (np.arange(size, dtype=float) ** 2 + 5) / size
    )
    return frequencies.conj().T @ (phases[:, None] * frequencies)


def orthogonal_projection(columns: np.ndarray) -> np.ndarray:
    gram = columns.conj().T @ columns
    return columns @ np.linalg.solve(gram, columns.conj().T)


def operator_norm(matrix: np.ndarray) -> float:
    return float(np.linalg.norm(matrix, ord=2))


def nested_amplitude_order_counterexample() -> tuple[float, float, float]:
    identity = np.eye(3, dtype=float)
    unitary = identity[:, [1, 2, 0]]
    transfer = identity - 0.25 * unitary
    transfer_inverse = np.linalg.inv(transfer)
    amplitudes = []
    for rank in (1, 2):
        basis = identity[:, :rank]
        projection = basis @ basis.T
        metric_projection = orthogonal_projection(transfer @ basis)
        oblique = transfer @ projection @ transfer_inverse
        amplitudes.append(oblique @ oblique.T - metric_projection)

    difference = amplitudes[1] - amplitudes[0]
    difference = (difference + difference.T) / 2
    return (
        float(difference[0, 0]),
        float(difference[1, 1]),
        float(np.trace(difference)),
    )


def certificate(parameter: float, neumann_terms: int) -> dict[str, float]:
    size = 22
    rank = 9
    identity = np.eye(size, dtype=complex)

    mixing = deterministic_unitary(size)
    basis = mixing[:, :rank]
    complement_basis = mixing[:, rank:]
    projection = basis @ basis.conj().T

    unitary = deterministic_unitary(size) @ np.diag(
        np.exp(2j * np.pi * np.arange(size) / (size + 1))
    )
    transfer = identity - parameter * unitary
    transfer_inverse = np.linalg.inv(transfer)
    metric = transfer.conj().T @ transfer

    block_a = basis.conj().T @ metric @ basis
    block_a_inverse = np.linalg.inv(block_a)
    metric_projection = (
        transfer @ basis @ block_a_inverse @ basis.conj().T @ transfer.conj().T
    )
    oblique = transfer @ projection @ transfer_inverse
    defect = oblique - metric_projection

    common_range_left = metric_projection @ oblique - oblique
    common_range_right = oblique @ metric_projection - metric_projection
    defect_square = defect @ defect.conj().T
    amplitude = oblique @ oblique.conj().T - metric_projection

    block_c = basis.conj().T @ metric @ complement_basis
    block_d = complement_basis.conj().T @ metric @ complement_basis
    schur = block_d - block_c.conj().T @ block_a_inverse @ block_c
    schur_term = (
        transfer
        @ basis
        @ block_a_inverse
        @ block_c
        @ np.linalg.solve(schur, block_c.conj().T)
        @ block_a_inverse
        @ basis.conj().T
        @ transfer.conj().T
    )
    inverse_block = basis.conj().T @ np.linalg.inv(metric) @ basis
    woodbury = (
        block_a_inverse
        + block_a_inverse
        @ block_c
        @ np.linalg.solve(schur, block_c.conj().T)
        @ block_a_inverse
    )

    smoother = 0.4 * identity + 0.3 * unitary + 0.2 * unitary.conj().T
    positive_test = smoother.conj().T @ smoother
    exact_trace = np.trace(positive_test @ metric_projection)
    principal_trace = np.trace(
        positive_test @ oblique @ oblique.conj().T
    )
    penalty = float(np.vdot(smoother @ defect, smoother @ defect).real)
    trace_penalty_error = abs(exact_trace - (principal_trace - penalty))

    compressed_unitary = basis.conj().T @ (
        unitary + unitary.conj().T
    ) @ basis
    ratio = parameter / (1 + parameter**2)
    neumann = np.zeros((rank, rank), dtype=complex)
    power = np.eye(rank, dtype=complex)
    for _ in range(neumann_terms):
        neumann += power
        power = ratio * compressed_unitary @ power
    neumann /= 1 + parameter**2

    return {
        "oblique_idempotence_error": operator_norm(oblique @ oblique - oblique),
        "common_range_left_error": operator_norm(common_range_left),
        "common_range_right_error": operator_norm(common_range_right),
        "defect_nilpotence_error": operator_norm(defect @ defect),
        "positive_square_error": operator_norm(amplitude - defect_square),
        "schur_amplitude_error": operator_norm(amplitude - schur_term),
        "woodbury_error": operator_norm(inverse_block - woodbury),
        "trace_penalty_error": float(trace_penalty_error),
        "amplitude_min_eigenvalue": float(
            np.linalg.eigvalsh((amplitude + amplitude.conj().T) / 2)[0]
        ),
        "neumann_error": operator_norm(neumann - block_a_inverse),
        "neumann_norm_ratio": float(2 * parameter / (1 + parameter**2)),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--prime", type=int, default=2)
    parser.add_argument("--neumann-terms", type=int, default=512)
    parser.add_argument("--max-error", type=float, default=2e-10)
    parser.add_argument("--min-eigenvalue", type=float, default=-2e-12)
    args = parser.parse_args()

    if args.prime < 2:
        raise ValueError("prime must be at least 2")
    if args.neumann_terms < 16:
        raise ValueError("neumann-terms must be at least 16")

    parameter = 1 / math.sqrt(args.prime)
    values = certificate(parameter, args.neumann_terms)
    nested_e1, nested_e2, nested_trace = nested_amplitude_order_counterexample()

    print("identity=metric-Sonin oblique-defect amplitude")
    print(f"prime={args.prime} alpha={parameter:.12f}")
    for name, value in values.items():
        print(f"{name}={value:.3e}")
    print(f"nested_amplitude_e1={nested_e1:.12f}")
    print(f"nested_amplitude_e2={nested_e2:.12f}")
    print(f"nested_amplitude_trace={nested_trace:.3e}")

    errors = [
        value
        for name, value in values.items()
        if name.endswith("_error")
    ]
    if max(errors) > args.max_error:
        raise RuntimeError("oblique-defect identity failed")
    if values["amplitude_min_eigenvalue"] < args.min_eigenvalue:
        raise RuntimeError("amplitude defect is not positive semidefinite")
    if values["neumann_norm_ratio"] >= 1:
        raise RuntimeError("compressed-metric Neumann ratio is not contractive")
    if not nested_e1 < 0 < nested_e2:
        raise RuntimeError("nested amplitude ordering counterexample failed")

    print("certificate=PASS")
    print("amplitude_owner_verdict=PASS")
    print("amplitude_trace_sign_verdict=PASS")
    print("nested_amplitude_order_verdict=REJECTED")
    print("smooth_q_root_amplitude_trace_verdict=PASS")
    print("bounded_pre_root_amplitude_operator_verdict=OPEN")
    print("full_metric_compactness_verdict=OPEN")
    print("nested_sign_verdict=OPEN")


if __name__ == "__main__":
    main()
