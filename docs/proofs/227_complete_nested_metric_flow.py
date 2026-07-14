#!/usr/bin/env python3
"""Finite-matrix certificate for Proof 227's complete nested metric flow.

The mathematical proof is projection algebra.  This script independently
checks the moving-projection derivative, the exact nested cancellation, its
Kato commutator owner, the Euler resolvent, and the cancellation between the
separated oblique-phase and defect-square diagonal blocks.

It does not test the infinite-dimensional Q-root ideal estimate or the final
three-row sign.
"""

from __future__ import annotations

import argparse
import math

import numpy as np


def deterministic_unitary(size: int, offset: int) -> np.ndarray:
    fourier = np.fft.fft(np.eye(size), axis=0) / math.sqrt(size)
    indices = np.arange(size, dtype=float)
    phases = np.exp(2j * np.pi * (indices**2 + offset * indices + 3) / size)
    return fourier.conj().T @ (phases[:, None] * fourier)


def orthogonal_projection(columns: np.ndarray) -> np.ndarray:
    gram = columns.conj().T @ columns
    return columns @ np.linalg.solve(gram, columns.conj().T)


def operator_norm(matrix: np.ndarray) -> float:
    return float(np.linalg.norm(matrix, ord=2))


def moved_projection(
    transfer: np.ndarray, basis: np.ndarray
) -> np.ndarray:
    return orthogonal_projection(transfer @ basis)


def projection_flow(
    projection: np.ndarray, logarithmic_derivative: np.ndarray
) -> np.ndarray:
    identity = np.eye(projection.shape[0], dtype=complex)
    complement = identity - projection
    return (
        complement @ logarithmic_derivative @ projection
        + projection @ logarithmic_derivative.conj().T @ complement
    )


def phase_and_defect_derivatives(
    fixed_projection: np.ndarray,
    metric_projection: np.ndarray,
    transfer: np.ndarray,
    transfer_inverse: np.ndarray,
    logarithmic_derivative: np.ndarray,
) -> tuple[np.ndarray, np.ndarray]:
    oblique = transfer @ fixed_projection @ transfer_inverse
    oblique_derivative = (
        logarithmic_derivative @ oblique
        - oblique @ logarithmic_derivative
    )
    metric_derivative = projection_flow(
        metric_projection, logarithmic_derivative
    )
    defect = oblique - metric_projection
    defect_derivative = oblique_derivative - metric_derivative
    phase_derivative = (
        oblique_derivative @ oblique.conj().T
        + oblique @ oblique_derivative.conj().T
    )
    amplitude_derivative = (
        defect_derivative @ defect.conj().T
        + defect @ defect_derivative.conj().T
    )
    return phase_derivative, amplitude_derivative


def certificate(
    parameter: float, finite_difference_step: float, resolvent_terms: int
) -> dict[str, float]:
    size = 26
    outer_rank = 16
    inner_rank = 9
    identity = np.eye(size, dtype=complex)

    mixing = deterministic_unitary(size, 5)
    outer_basis = mixing[:, :outer_rank]
    inner_basis = outer_basis[:, :inner_rank]
    fixed_outer = outer_basis @ outer_basis.conj().T
    fixed_inner = inner_basis @ inner_basis.conj().T

    unitary = deterministic_unitary(size, 9) @ np.diag(
        np.exp(2j * np.pi * np.arange(size) / (size + 3))
    )
    transfer = identity - parameter * unitary
    transfer_inverse = np.linalg.inv(transfer)
    logarithmic_derivative = -unitary @ transfer_inverse

    moved_outer = moved_projection(transfer, outer_basis)
    moved_inner = moved_projection(transfer, inner_basis)
    complement_projection = moved_outer - moved_inner
    exterior_projection = identity - moved_outer

    outer_derivative = projection_flow(
        moved_outer, logarithmic_derivative
    )
    inner_derivative = projection_flow(
        moved_inner, logarithmic_derivative
    )
    nested_derivative = outer_derivative - inner_derivative

    complete_derivative = (
        exterior_projection
        @ logarithmic_derivative
        @ complement_projection
        + complement_projection
        @ logarithmic_derivative.conj().T
        @ exterior_projection
        - complement_projection
        @ logarithmic_derivative
        @ moved_inner
        - moved_inner
        @ logarithmic_derivative.conj().T
        @ complement_projection
    )

    crossing = (
        exterior_projection
        @ logarithmic_derivative
        @ complement_projection
        - moved_inner
        @ logarithmic_derivative.conj().T
        @ complement_projection
    )
    kato_generator = crossing - crossing.conj().T
    kato_commutator = (
        kato_generator @ complement_projection
        - complement_projection @ kato_generator
    )

    plus_transfer = identity - (
        parameter + finite_difference_step
    ) * unitary
    minus_transfer = identity - (
        parameter - finite_difference_step
    ) * unitary
    plus_complement = (
        moved_projection(plus_transfer, outer_basis)
        - moved_projection(plus_transfer, inner_basis)
    )
    minus_complement = (
        moved_projection(minus_transfer, outer_basis)
        - moved_projection(minus_transfer, inner_basis)
    )
    finite_difference = (
        plus_complement - minus_complement
    ) / (2 * finite_difference_step)

    resolvent_sum = np.zeros((size, size), dtype=complex)
    power = unitary.copy()
    coefficient = 1.0
    for _ in range(resolvent_terms):
        resolvent_sum -= coefficient * power
        power = power @ unitary
        coefficient *= parameter

    outer_phase, outer_amplitude = phase_and_defect_derivatives(
        fixed_outer,
        moved_outer,
        transfer,
        transfer_inverse,
        logarithmic_derivative,
    )
    inner_phase, inner_amplitude = phase_and_defect_derivatives(
        fixed_inner,
        moved_inner,
        transfer,
        transfer_inverse,
        logarithmic_derivative,
    )
    phase_nested = outer_phase - inner_phase
    amplitude_nested = outer_amplitude - inner_amplitude
    recombined = phase_nested - amplitude_nested

    diagonal_phase = (
        complement_projection @ phase_nested @ complement_projection
    )
    diagonal_amplitude = (
        complement_projection @ amplitude_nested @ complement_projection
    )
    diagonal_complete = (
        complement_projection @ recombined @ complement_projection
    )
    exterior_complete = (
        (identity - complement_projection)
        @ recombined
        @ (identity - complement_projection)
    )

    eigenvalues = np.linalg.eigvalsh(
        (complete_derivative + complete_derivative.conj().T) / 2
    )

    return {
        "finite_difference_error": operator_norm(
            finite_difference - nested_derivative
        ),
        "complete_flow_error": operator_norm(
            complete_derivative - nested_derivative
        ),
        "kato_commutator_error": operator_norm(
            kato_commutator - nested_derivative
        ),
        "resolvent_error": operator_norm(
            resolvent_sum - logarithmic_derivative
        ),
        "recombination_error": operator_norm(
            recombined - nested_derivative
        ),
        "complete_range_diagonal_error": operator_norm(
            diagonal_complete
        ),
        "complete_exterior_diagonal_error": operator_norm(
            exterior_complete
        ),
        "separated_phase_diagonal_norm": operator_norm(diagonal_phase),
        "separated_amplitude_diagonal_norm": operator_norm(
            diagonal_amplitude
        ),
        "flow_min_eigenvalue": float(eigenvalues[0]),
        "flow_max_eigenvalue": float(eigenvalues[-1]),
        "logarithmic_derivative_norm": operator_norm(
            logarithmic_derivative
        ),
        "resolvent_norm_bound": float(1 / (1 - parameter)),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--prime", type=int, default=2)
    parser.add_argument("--finite-difference-step", type=float, default=1e-6)
    parser.add_argument("--resolvent-terms", type=int, default=256)
    parser.add_argument("--max-error", type=float, default=2e-8)
    parser.add_argument("--min-separated-diagonal", type=float, default=1e-4)
    args = parser.parse_args()

    if args.prime < 2:
        raise ValueError("prime must be at least 2")
    if not 0 < args.finite_difference_step < 1e-3:
        raise ValueError("finite-difference-step must be in (0, 1e-3)")
    if args.resolvent_terms < 32:
        raise ValueError("resolvent-terms must be at least 32")

    parameter = 1 / math.sqrt(args.prime)
    values = certificate(
        parameter, args.finite_difference_step, args.resolvent_terms
    )

    print("identity=complete nested metric flow")
    print(f"prime={args.prime} alpha={parameter:.12f}")
    for name, value in values.items():
        print(f"{name}={value:.3e}")

    errors = [
        value for name, value in values.items() if name.endswith("_error")
    ]
    if max(errors) > args.max_error:
        raise RuntimeError("complete nested flow identity failed")
    if not (
        values["separated_phase_diagonal_norm"]
        > args.min_separated_diagonal
        and values["separated_amplitude_diagonal_norm"]
        > args.min_separated_diagonal
    ):
        raise RuntimeError("separated diagonal cancellation is not visible")
    if not values["flow_min_eigenvalue"] < 0 < values[
        "flow_max_eigenvalue"
    ]:
        raise RuntimeError("nonzero projection flow is not indefinite")
    if (
        values["logarithmic_derivative_norm"]
        > values["resolvent_norm_bound"] + args.max_error
    ):
        raise RuntimeError("Euler resolvent norm bound failed")

    print("certificate=PASS")
    print("complete_flow_owner_verdict=PASS")
    print("separated_mode_gate_verdict=REMOVED")
    print("abstract_monotonicity_sign_verdict=REJECTED")
    print("complete_q_root_ideal_verdict=OPEN")
    print("integrated_three_row_sign_verdict=OPEN")


if __name__ == "__main__":
    main()
