#!/usr/bin/env python3
"""Certificate for the Gate 3U endpoint two-commutator reduction.

The first layer checks three equivalent formulas for the nested metric endpoint
response: the difference of transported projections, the dual-frame intrinsic
response, and the new two-source-commutator formula.

The second layer builds a direct sum of exact two-state Markov blocks.  The
detector kills the Markov fixed mode, the second support is invariant, and the
base prolate eigenvalues decay super-exponentially.  The detector commutator
trace norms remain bounded while the endpoint responses grow linearly.  This
guards against deriving Gate 3U from those abstract properties without the
actual compact-support half-line geometry.
"""

from __future__ import annotations

import argparse
import math

import numpy as np


def commutator(left: np.ndarray, right: np.ndarray) -> np.ndarray:
    return left @ right - right @ left


def relative_error(actual: complex | np.ndarray, expected: complex | np.ndarray) -> float:
    actual_array = np.asarray(actual)
    expected_array = np.asarray(expected)
    denominator = max(float(np.linalg.norm(expected_array)), 1e-15)
    return float(np.linalg.norm(actual_array - expected_array) / denominator)


def cyclic_shift(size: int, amount: int) -> np.ndarray:
    return np.roll(np.eye(size, dtype=complex), amount, axis=0)


def coordinate_projection(size: int, rank: int) -> np.ndarray:
    projection = np.zeros((size, size), dtype=complex)
    indices = np.arange(rank)
    projection[indices, indices] = 1.0
    return projection


def circulant_root(size: int) -> np.ndarray:
    kernel = np.zeros(size, dtype=complex)
    kernel[0] = 1.0
    kernel[1] = 0.3 - 0.1j
    kernel[-1] = -0.2 + 0.15j
    return np.column_stack([np.roll(kernel, column) for column in range(size)])


def extended_compressed_inverse(
    projection: np.ndarray, operator: np.ndarray
) -> np.ndarray:
    identity = np.eye(projection.shape[0], dtype=complex)
    return np.linalg.inv(
        projection @ operator @ projection + identity - projection
    )


def metric_projection(
    source_projection: np.ndarray,
    transport: np.ndarray,
    metric: np.ndarray,
) -> np.ndarray:
    inverse = extended_compressed_inverse(source_projection, metric)
    return (
        transport
        @ source_projection
        @ inverse
        @ source_projection
        @ transport.conj().T
    )


def endpoint_identity_certificate(size: int, time: float) -> dict[str, float]:
    if size < 8 or size % 4:
        raise ValueError("size must be divisible by four and at least eight")
    if not 0.0 <= time <= 1.0:
        raise ValueError("time must lie in [0,1]")

    identity = np.eye(size, dtype=complex)
    shifts = (cyclic_shift(size, 1), cyclic_shift(size, 3))
    weights = (1.0 / math.sqrt(2.0), 1.0 / math.sqrt(3.0))
    transport = (
        identity - time * weights[0] * shifts[0]
    ) @ (
        identity - time * weights[1] * shifts[1]
    )
    metric = transport.conj().T @ transport
    inverse_metric = np.linalg.inv(metric)

    outer = coordinate_projection(size, 3 * size // 4)
    inner = coordinate_projection(size, size // 4)
    band = outer - inner
    complement = identity - outer

    root = circulant_root(size)
    detector = root.conj().T @ root

    transported_outer = metric_projection(outer, transport, metric)
    transported_inner = metric_projection(inner, transport, metric)
    transported_band = transported_outer - transported_inner

    def relative_projection_formula(projection: np.ndarray) -> complex:
        inverse = extended_compressed_inverse(projection, metric)
        return np.trace(
            commutator(projection, detector)
            @ (identity - projection)
            @ metric
            @ projection
            @ inverse
        )

    direct_outer = np.trace(detector @ (transported_outer - outer))
    direct_inner = np.trace(detector @ (transported_inner - inner))
    formula_outer = relative_projection_formula(outer)
    formula_inner = relative_projection_formula(inner)

    inner_inverse = extended_compressed_inverse(inner, metric)
    graph = inner_inverse @ inner @ metric @ band
    source_frame = band - inner @ graph
    schur = source_frame.conj().T @ metric @ source_frame
    schur_inverse = extended_compressed_inverse(band, schur)
    coframe = metric @ source_frame @ schur_inverse @ band

    complement_inverse = extended_compressed_inverse(
        complement, inverse_metric
    )
    shorted_coframe = (
        band
        - complement
        @ complement_inverse
        @ complement
        @ inverse_metric
        @ band
    )

    detector_band = band @ detector @ band
    intrinsic_defect = detector @ source_frame - source_frame @ detector_band
    intrinsic_response = np.trace(coframe.conj().T @ intrinsic_defect)
    two_commutator_response = np.trace(
        coframe.conj().T
        @ (
            complement @ commutator(detector, outer) @ band
            - commutator(detector, inner) @ inner @ graph
        )
    )
    direct_band = np.trace(detector @ (transported_band - band))

    return {
        "detector_transport_commutator": float(
            np.linalg.norm(commutator(detector, transport), ord="fro")
        ),
        "outer_relative_trace_error": relative_error(
            formula_outer, direct_outer
        ),
        "inner_relative_trace_error": relative_error(
            formula_inner, direct_inner
        ),
        "band_difference_error": relative_error(
            direct_outer - direct_inner, direct_band
        ),
        "coframe_shorting_error": relative_error(
            shorted_coframe, coframe
        ),
        "coframe_inner_orthogonality": float(
            np.linalg.norm(coframe.conj().T @ inner, ord="fro")
        ),
        "coframe_band_pairing_error": relative_error(
            coframe.conj().T @ band, band
        ),
        "intrinsic_endpoint_error": relative_error(
            intrinsic_response, direct_band
        ),
        "two_commutator_endpoint_error": relative_error(
            two_commutator_response, direct_band
        ),
    }


def markov_prolate_guard(modes: int) -> tuple[list[dict[str, float]], float]:
    if modes < 1:
        raise ValueError("modes must be positive")

    identity = np.eye(2, dtype=complex)
    swap = np.array([[0.0, 1.0], [1.0, 0.0]], dtype=complex)
    hadamard = np.array([[1.0, 1.0], [1.0, -1.0]], dtype=complex) / math.sqrt(2.0)
    fixed = np.array([[1.0], [0.0]], dtype=complex)
    crossing = np.array([[0.0], [1.0]], dtype=complex)
    detector = crossing @ crossing.conj().T

    rows: list[dict[str, float]] = []
    maximum_error = 0.0
    cumulative_response = 0.0
    cumulative_commutator = 0.0
    cumulative_prolate = 0.0

    for mode in range(1, modes + 1):
        prolate_eigenvalue = 2.0 ** (-4.0 * mode * mode)
        root_eigenvalue = math.sqrt(prolate_eigenvalue)
        inverse_metric = np.diag([1.0, prolate_eigenvalue]).astype(complex)
        metric = np.diag([1.0, 1.0 / prolate_eigenvalue]).astype(complex)
        transport = np.diag([1.0, 1.0 / root_eigenvalue]).astype(complex)

        source_vector = (
            math.sqrt(1.0 - prolate_eigenvalue) * fixed
            + root_eigenvalue * crossing
        )
        source_projection = source_vector @ source_vector.conj().T
        second_support = detector
        transported = metric_projection(source_projection, transport, metric)

        endpoint_response = float(
            np.trace(detector @ (transported - source_projection)).real
        )
        expected_response = (
            1.0 / (2.0 - prolate_eigenvalue) - prolate_eigenvalue
        )
        commutator_mass = float(
            np.linalg.svd(
                commutator(detector, source_projection), compute_uv=False
            ).sum()
        )
        expected_commutator = 2.0 * math.sqrt(
            prolate_eigenvalue * (1.0 - prolate_eigenvalue)
        )

        markov_physical = hadamard @ inverse_metric @ hadamard.conj().T
        markov_expected = (
            0.5 * (1.0 + prolate_eigenvalue) * identity
            + 0.5 * (1.0 - prolate_eigenvalue) * swap
        )

        errors = (
            abs(endpoint_response - expected_response),
            abs(commutator_mass - expected_commutator),
            float(
                np.linalg.norm(
                    source_projection @ second_support @ source_projection
                    - prolate_eigenvalue * source_projection,
                    ord="fro",
                )
            ),
            float(np.linalg.norm(markov_physical - markov_expected, ord="fro")),
            float(np.linalg.norm(commutator(second_support, transport), ord="fro")),
            float(np.linalg.norm(detector @ fixed, ord="fro")),
        )
        maximum_error = max(maximum_error, *errors)

        cumulative_response += endpoint_response
        cumulative_commutator += commutator_mass
        cumulative_prolate += prolate_eigenvalue
        rows.append(
            {
                "modes": float(mode),
                "response": cumulative_response,
                "commutator": cumulative_commutator,
                "prolate": cumulative_prolate,
                "condition": 1.0 / prolate_eigenvalue,
            }
        )

    return rows, maximum_error


def print_report(
    endpoint: dict[str, float],
    guard: list[dict[str, float]],
    guard_error: float,
) -> None:
    print("endpoint two-commutator algebra")
    print("+--------------------------------------+---------------+")
    print("| check                                | error         |")
    print("+--------------------------------------+---------------+")
    for label, value in endpoint.items():
        print(f"| {label:<36} | {value:>13.6e} |")
    print("+--------------------------------------+---------------+")

    print()
    print("Markov/prolate direct-sum guard")
    print("+-------+-------------+-------------+-------------+-------------+")
    print("| modes | response    | comm S1     | prolate S1  | condition   |")
    print("+-------+-------------+-------------+-------------+-------------+")
    selected = {1, 2, 4, 8, len(guard)}
    for row in guard:
        if int(row["modes"]) not in selected:
            continue
        print(
            f"| {int(row['modes']):>5} "
            f"| {row['response']:>11.5e} "
            f"| {row['commutator']:>11.5e} "
            f"| {row['prolate']:>11.5e} "
            f"| {row['condition']:>11.5e} |"
        )
    print("+-------+-------------+-------------+-------------+-------------+")
    print(f"maximum guard algebra error: {guard_error:.6e}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--size", type=int, default=12)
    parser.add_argument("--time", type=float, default=0.63)
    parser.add_argument("--modes", type=int, default=8)
    parser.add_argument("--tolerance", type=float, default=1e-10)
    args = parser.parse_args()

    endpoint = endpoint_identity_certificate(args.size, args.time)
    guard, guard_error = markov_prolate_guard(args.modes)
    print_report(endpoint, guard, guard_error)

    maximum_error = max(max(endpoint.values()), guard_error)
    print(f"maximum checked error: {maximum_error:.6e}")
    if maximum_error > args.tolerance:
        raise SystemExit(
            f"certificate failed: {maximum_error:.6e} > {args.tolerance:.6e}"
        )


if __name__ == "__main__":
    main()
