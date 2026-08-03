#!/usr/bin/env python3
"""Check the local finite-window realization of Proof 776's lattice guard."""

from __future__ import annotations

import numpy as np


def shift_right(size: int) -> np.ndarray:
    result = np.zeros((size, size), dtype=np.complex128)
    for column in range(size - 1):
        result[column + 1, column] = 1.0
    return result


def run_case(count: int, a: float, b: float) -> tuple[float, float, float, float, float]:
    padding = 6
    coordinates = np.arange(-padding, 3 * count + padding + 1)
    size = coordinates.size
    index = {coordinate: position for position, coordinate in enumerate(coordinates)}
    identity = np.eye(size, dtype=np.complex128)
    shift = shift_right(size)
    transport = identity - a * shift
    root = (identity + b * shift) / (1.0 + b)
    metric = transport.conj().T @ transport
    detector = root.conj().T @ root

    source_coordinates = [3 * j for j in range(1, count + 1)]
    source_positions = [index[coordinate] for coordinate in source_coordinates]
    inclusion = identity[:, source_positions]
    source_projection = inclusion @ inclusion.conj().T
    source_gram = inclusion.conj().T @ metric @ inclusion
    target = np.linalg.inv(source_gram) @ inclusion.conj().T @ metric @ (
        identity - source_projection
    ) @ detector @ inclusion

    expected_scalar = -2.0 * a * b / ((1.0 + a * a) * (1.0 + b) ** 2)
    expected = expected_scalar * np.eye(count, dtype=np.complex128)

    half_line = np.diag((coordinates >= 0).astype(np.complex128))
    complement = identity - half_line
    inverse_transport = np.linalg.inv(transport)
    causal_error = max(
        np.linalg.norm(complement @ transport @ half_line),
        np.linalg.norm(complement @ inverse_transport @ half_line),
    )
    local_commutator_error = np.linalg.norm((metric @ detector - detector @ metric) @ inclusion)
    formula_error = np.linalg.norm(target - expected)
    gram_inverse_norm = np.linalg.norm(np.linalg.inv(source_gram), ord=2)
    detector_norm = np.linalg.norm(detector, ord=2)
    return formula_error, causal_error, local_commutator_error, gram_inverse_norm, detector_norm


def main() -> None:
    a = 0.5
    b = 0.5
    maximum_formula_error = 0.0
    maximum_causal_error = 0.0
    maximum_local_commutator_error = 0.0
    maximum_inverse_gram_norm = 0.0
    maximum_detector_norm = 0.0
    trace_ratios: list[float] = []

    for count in (1, 2, 4, 8, 16, 32):
        formula_error, causal_error, local_commutator_error, inverse_gram_norm, detector_norm = run_case(
            count, a, b
        )
        maximum_formula_error = max(maximum_formula_error, formula_error)
        maximum_causal_error = max(maximum_causal_error, causal_error)
        maximum_local_commutator_error = max(
            maximum_local_commutator_error, local_commutator_error
        )
        maximum_inverse_gram_norm = max(maximum_inverse_gram_norm, inverse_gram_norm)
        maximum_detector_norm = max(maximum_detector_norm, detector_norm)
        trace_ratios.append(abs(-2.0 * a * b / ((1.0 + a * a) * (1.0 + b) ** 2)))

    if maximum_formula_error > 1e-11:
        raise AssertionError(f"corner formula error: {maximum_formula_error}")
    if maximum_causal_error > 1e-11:
        raise AssertionError(f"causal half-line error: {maximum_causal_error}")
    if maximum_local_commutator_error > 1e-11:
        raise AssertionError(f"local metric/detector commutator error: {maximum_local_commutator_error}")
    if maximum_inverse_gram_norm > 1.0 + 1e-11:
        raise AssertionError(f"inverse Gram is not contractive: {maximum_inverse_gram_norm}")
    if maximum_detector_norm > 1.0 + 1e-11:
        raise AssertionError(f"detector is not contractive: {maximum_detector_norm}")
    if max(trace_ratios) - min(trace_ratios) > 1e-15:
        raise AssertionError("trace ratio changed with the number of source cells")

    print(f"maximum corner formula error      {maximum_formula_error:.2e}")
    print(f"maximum causal support error      {maximum_causal_error:.2e}")
    print(f"maximum local commutator error    {maximum_local_commutator_error:.2e}")
    print(f"maximum inverse-Gram norm         {maximum_inverse_gram_norm:.6f}")
    print(f"maximum detector norm             {maximum_detector_norm:.6f}")
    print(f"absolute trace per source cell    {trace_ratios[0]:.6f}")


if __name__ == "__main__":
    main()
