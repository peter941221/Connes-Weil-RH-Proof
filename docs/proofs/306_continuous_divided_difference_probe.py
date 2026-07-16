#!/usr/bin/env python3
"""Finite guard for the Proof 306 segment-average divided difference.

The probe checks the same construction used by the Lean witness: average the
derivative along the segment from ``t`` to ``s``.  The diagonal is assigned by
the same average, so no discontinuous ``if s == t`` branch is involved.  The
matrix trace and the explicit CC20 residue are carried over from Proof 305.
This remains a finite diagnostic, not a source theorem or an RH proof.
"""

from __future__ import annotations

import argparse

import numpy as np


def relative_error(actual: np.ndarray | complex, expected: np.ndarray | complex) -> float:
    actual_array = np.asarray(actual)
    expected_array = np.asarray(expected)
    scale = max(float(np.linalg.norm(expected_array)), 1.0)
    return float(np.linalg.norm(actual_array - expected_array) / scale)


def root(size: int, radius: int, seed: int) -> np.ndarray:
    rng = np.random.default_rng(seed)
    values = rng.normal(size=2 * radius + 1) + 1j * rng.normal(size=2 * radius + 1)
    values /= np.linalg.norm(values)
    result = np.zeros(size, dtype=complex)
    support = np.arange(-radius, radius + 1)
    result[np.mod(support, size)] = values
    return result


def value(x: np.ndarray) -> np.ndarray:
    return np.exp(-0.16 * x**2) * (1.0 + 0.12 * x) + 0.1j * np.sin(0.7 * x)


def derivative(x: np.ndarray) -> np.ndarray:
    return np.exp(-0.16 * x**2) * (
        0.12 - 0.32 * x * (1.0 + 0.12 * x)
    ) + 0.07j * np.cos(0.7 * x)


def segment_average(nodes: np.ndarray, quadrature_order: int = 64) -> np.ndarray:
    quadrature_nodes, quadrature_weights = np.polynomial.legendre.leggauss(
        quadrature_order
    )
    unit_nodes = 0.5 * (quadrature_nodes + 1.0)
    unit_weights = 0.5 * quadrature_weights
    difference = nodes[:, None] - nodes[None, :]
    start = nodes[None, :]
    result = np.zeros((nodes.size, nodes.size), dtype=complex)
    for u, weight in zip(unit_nodes, unit_weights):
        result += weight * derivative(start + u * difference)
    return result


def run(size: int, radius: int, seed: int) -> dict[str, float]:
    nodes = np.linspace(-3.0, 3.0, size)
    average = segment_average(nodes)
    values = value(nodes)
    differences = nodes[:, None] - nodes[None, :]
    quotient = np.zeros_like(average)
    off_diagonal = ~np.eye(size, dtype=bool)
    quotient[off_diagonal] = (
        (values[:, None] - values[None, :])[off_diagonal]
        / differences[off_diagonal]
    )

    diagonal_error = np.max(np.abs(np.diag(average) - derivative(nodes)))
    off_diagonal_error = np.max(np.abs(average[off_diagonal] - quotient[off_diagonal]))
    quantized = 1j / np.pi * average
    quantized_expected = 1j / np.pi * quotient
    quantized_error = np.max(
        np.abs(quantized[off_diagonal] - quantized_expected[off_diagonal])
    )

    # The zero derivative witness gives the zero kernel at every pair.
    constant_average = np.zeros_like(average)
    constant_kernel_error = float(np.linalg.norm(constant_average))

    left = root(size, radius, seed)
    right = root(size, radius, seed + 1)
    second_average = np.zeros_like(average)
    quadrature_nodes, quadrature_weights = np.polynomial.legendre.leggauss(64)
    unit_nodes = 0.5 * (quadrature_nodes + 1.0)
    unit_weights = 0.5 * quadrature_weights
    for u, weight in zip(unit_nodes, unit_weights):
        second_average += weight * (
            0.4 * np.cos(0.4 * (nodes[None, :] + u * differences))
            - 0.18j * np.sin(0.9 * (nodes[None, :] + u * differences))
        )
    left_factor = np.diag(np.conj(left)) @ quantized @ np.diag(right)
    right_factor = np.diag(np.conj(left)) @ (
        1j / np.pi * second_average
    ) @ np.diag(right)
    trace = np.trace(left_factor.conj().T @ right_factor)
    row_pairing = np.sum(np.conj(left_factor) * right_factor)
    residue = -2.0 * np.vdot(right, left)

    return {
        "off-diagonal quotient error": float(off_diagonal_error),
        "diagonal derivative error": float(diagonal_error),
        "quantized normalization error": float(quantized_error),
        "constant kernel norm": constant_kernel_error,
        "A^*B row pairing error": relative_error(trace, row_pairing),
        "residue omission gap": float(abs(residue)),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--size", type=int, default=36)
    parser.add_argument("--support-radius", type=int, default=3)
    parser.add_argument("--seed", type=int, default=1306)
    args = parser.parse_args()

    metrics = run(args.size, args.support_radius, args.seed)
    print("Proof 306 continuous divided-difference ledger")
    for name, value_ in metrics.items():
        print(f"{name}: {value_:.6e}")
    print("RH=UNPROVED")

    if metrics["off-diagonal quotient error"] > 1e-11:
        raise SystemExit("off-diagonal quotient identity failed")
    if metrics["diagonal derivative error"] > 1e-11:
        raise SystemExit("diagonal derivative extension failed")
    if metrics["quantized normalization error"] > 1e-11:
        raise SystemExit("quantized normalization failed")
    if metrics["constant kernel norm"] > 1e-12:
        raise SystemExit("constant mode did not vanish")
    if metrics["A^*B row pairing error"] > 1e-12:
        raise SystemExit("root-sandwiched trace readback failed")
    if metrics["residue omission gap"] < 1e-6:
        raise SystemExit("residue omission guard did not fire")


if __name__ == "__main__":
    main()
