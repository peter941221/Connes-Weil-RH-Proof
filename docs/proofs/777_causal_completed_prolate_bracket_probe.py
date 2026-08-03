#!/usr/bin/env python3
"""Exact finite-block guard for Proof 777's completed-prolate bracket."""

from __future__ import annotations

import numpy as np


def direct_sum(blocks: list[np.ndarray]) -> np.ndarray:
    size = sum(block.shape[0] for block in blocks)
    result = np.zeros((size, size), dtype=np.complex128)
    offset = 0
    for block in blocks:
        width = block.shape[0]
        result[offset : offset + width, offset : offset + width] = block
        offset += width
    return result


def certify_case(count: int, a: float, b: float) -> tuple[float, ...]:
    identity3 = np.eye(3, dtype=np.complex128)
    support_block = np.diag([1.0, 1.0, 0.0]).astype(np.complex128)
    source_block = np.diag([1.0, 0.0, 0.0]).astype(np.complex128)
    swap_block = np.array(
        [[0.0, 1.0, 0.0], [1.0, 0.0, 0.0], [0.0, 0.0, 1.0]],
        dtype=np.complex128,
    )

    q_blocks: list[np.ndarray] = []
    prolate_blocks: list[np.ndarray] = []
    angles: list[float] = []
    for index in range(count):
        mu = 2.0 ** (-4 * (index + 1) ** 2)
        q_vector = np.array([0.0, np.sqrt(mu), np.sqrt(1.0 - mu)])
        q_blocks.append(source_block + np.outer(q_vector, q_vector))
        prolate_blocks.append(np.diag([0.0, mu, 0.0]).astype(np.complex128))
        angles.append(np.sqrt(mu))

    support = np.kron(np.eye(count), support_block)
    source = np.kron(np.eye(count), source_block)
    band = support - source
    second_support = direct_sum(q_blocks)
    prolate = direct_sum(prolate_blocks)
    identity = np.eye(3 * count, dtype=np.complex128)
    unitary = np.kron(np.eye(count), swap_block)
    transport = identity - a * unitary
    root = (identity + b * unitary) / (1.0 + b)
    metric = transport.conj().T @ transport
    detector = root.conj().T @ root

    inclusion = np.zeros((3 * count, count), dtype=np.complex128)
    for index in range(count):
        inclusion[3 * index, index] = 1.0

    gram = inclusion.conj().T @ metric @ inclusion
    target = np.linalg.inv(gram) @ inclusion.conj().T @ metric @ (
        identity - source
    ) @ detector @ inclusion
    expected_scalar = -4.0 * a * b / ((1.0 + a * a) * (1.0 + b) ** 2)
    expected_target = expected_scalar * np.eye(count, dtype=np.complex128)

    inverse_transport = np.linalg.inv(transport)
    causal_complement = identity - support
    completion_error = max(
        np.linalg.norm(second_support @ second_support - second_support),
        np.linalg.norm(second_support.conj().T - second_support),
        np.linalg.norm(support @ second_support @ support - prolate - source),
        np.linalg.norm(prolate - band @ second_support @ band),
        np.linalg.norm(source @ support - source),
        np.linalg.norm(second_support @ source - source),
    )
    causal_error = max(
        np.linalg.norm(causal_complement @ transport @ support),
        np.linalg.norm(causal_complement @ inverse_transport @ support),
    )
    formula_error = np.linalg.norm(target - expected_target)
    commute_error = np.linalg.norm(metric @ detector - detector @ metric)
    gram_inverse_norm = np.linalg.norm(np.linalg.inv(gram), ord=2)
    root_norm = np.linalg.norm(root, ord=2)
    detector_norm = np.linalg.norm(detector, ord=2)
    prolate_trace = float(np.trace(prolate).real)
    prolate_factor_norm = np.linalg.norm(second_support @ band, ord=2)
    prolate_defect_energy = float(
        np.linalg.norm((identity - band) @ second_support @ band, ord="fro") ** 2
    )
    return (
        completion_error,
        causal_error,
        formula_error,
        commute_error,
        gram_inverse_norm,
        root_norm,
        detector_norm,
        prolate_trace,
        prolate_factor_norm,
        prolate_defect_energy,
        abs(expected_scalar),
    )


def main() -> None:
    a = 0.5
    b = 0.5
    maximum_completion_error = 0.0
    maximum_causal_error = 0.0
    maximum_formula_error = 0.0
    maximum_commute_error = 0.0
    maximum_inverse_gram_norm = 0.0
    maximum_root_norm = 0.0
    maximum_detector_norm = 0.0
    maximum_prolate_trace = 0.0
    maximum_prolate_angle = 0.0
    maximum_prolate_defect_energy = 0.0
    trace_per_source: list[float] = []

    for count in (1, 2, 4, 8, 16, 32):
        (
            completion_error,
            causal_error,
            formula_error,
            commute_error,
            inverse_gram_norm,
            root_norm,
            detector_norm,
            prolate_trace,
            prolate_angle,
            prolate_defect_energy,
            scalar,
        ) = certify_case(count, a, b)
        maximum_completion_error = max(maximum_completion_error, completion_error)
        maximum_causal_error = max(maximum_causal_error, causal_error)
        maximum_formula_error = max(maximum_formula_error, formula_error)
        maximum_commute_error = max(maximum_commute_error, commute_error)
        maximum_inverse_gram_norm = max(maximum_inverse_gram_norm, inverse_gram_norm)
        maximum_root_norm = max(maximum_root_norm, root_norm)
        maximum_detector_norm = max(maximum_detector_norm, detector_norm)
        maximum_prolate_trace = max(maximum_prolate_trace, prolate_trace)
        maximum_prolate_angle = max(maximum_prolate_angle, prolate_angle)
        maximum_prolate_defect_energy = max(
            maximum_prolate_defect_energy, prolate_defect_energy
        )
        trace_per_source.append(scalar)

    if maximum_completion_error > 1e-11:
        raise AssertionError(f"completion algebra error: {maximum_completion_error}")
    if maximum_causal_error > 1e-11:
        raise AssertionError(f"causal support error: {maximum_causal_error}")
    if maximum_formula_error > 1e-11:
        raise AssertionError(f"corner formula error: {maximum_formula_error}")
    if maximum_commute_error > 1e-11:
        raise AssertionError(f"metric/detector commutator error: {maximum_commute_error}")
    if maximum_inverse_gram_norm > 1.0 + 1e-11:
        raise AssertionError(f"inverse Gram is not contractive: {maximum_inverse_gram_norm}")
    if maximum_root_norm > 1.0 + 1e-11:
        raise AssertionError(f"root is not contractive: {maximum_root_norm}")
    if maximum_detector_norm > 1.0 + 1e-11:
        raise AssertionError(f"detector is not contractive: {maximum_detector_norm}")
    if maximum_prolate_trace > 0.063:
        raise AssertionError(f"prolate trace is not uniformly small: {maximum_prolate_trace}")
    if maximum_prolate_angle >= 0.25 + 1e-11:
        raise AssertionError(f"strict prolate angle failed: {maximum_prolate_angle}")
    if max(trace_per_source) - min(trace_per_source) > 1e-15:
        raise AssertionError("corner trace per source cell changed with block count")

    print(f"maximum completion algebra error  {maximum_completion_error:.2e}")
    print(f"maximum causal support error      {maximum_causal_error:.2e}")
    print(f"maximum corner formula error      {maximum_formula_error:.2e}")
    print(f"maximum metric/detector error     {maximum_commute_error:.2e}")
    print(f"maximum inverse-Gram norm         {maximum_inverse_gram_norm:.6f}")
    print(f"maximum root norm                 {maximum_root_norm:.6f}")
    print(f"maximum detector norm             {maximum_detector_norm:.6f}")
    print(f"maximum prolate trace             {maximum_prolate_trace:.6f}")
    print(f"maximum strict prolate angle      {maximum_prolate_angle:.6f}")
    print(f"maximum prolate defect energy     {maximum_prolate_defect_energy:.6f}")
    print(f"absolute trace per source cell    {trace_per_source[0]:.6f}")


if __name__ == "__main__":
    main()
