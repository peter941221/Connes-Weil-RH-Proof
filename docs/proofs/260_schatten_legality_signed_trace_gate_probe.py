#!/usr/bin/env python3
"""Certificate for the Schatten-legality versus signed-trace gate.

The first check uses a compactly supported discrete convolution root and one
finite translation crossing.  The root-sandwiched crossing has trace zero,
but its trace norm and the optimal product of the two canonical
Hilbert--Schmidt factor norms are both strictly positive.

The second check records a sequence of zero-trace crossing blocks whose
operator norms tend to zero while each block has the same trace norm.  Their
orthogonal direct sum is the finite-section model of a compact operator which
is not trace class.

The script checks finite-dimensional algebra only.  The continuous statements
and their support hypotheses are proved in the accompanying note.
"""

from __future__ import annotations

import argparse
import math

import numpy as np


def relative_error(actual: complex | np.ndarray, expected: complex | np.ndarray) -> float:
    actual_array = np.asarray(actual)
    expected_array = np.asarray(expected)
    denominator = max(float(np.linalg.norm(expected_array)), 1e-15)
    return float(np.linalg.norm(actual_array - expected_array) / denominator)


def compact_root(size: int, radius: int) -> np.ndarray:
    if radius < 1 or 4 * radius >= size:
        raise ValueError("root radius must be positive and less than size / 4")

    coordinates = np.arange(-radius, radius + 1, dtype=float)
    scaled = coordinates / float(radius + 1)
    values = np.exp(-1.0 / (1.0 - scaled**2))
    values /= np.linalg.norm(values)

    root = np.zeros(size, dtype=complex)
    for coordinate, value in zip(coordinates.astype(int), values, strict=True):
        root[coordinate % size] = value
    return root


def convolution_matrix(root: np.ndarray) -> np.ndarray:
    size = root.size
    return np.column_stack([np.roll(root, column) for column in range(size)])


def translation_matrix(size: int, shift: int) -> np.ndarray:
    return np.roll(np.eye(size, dtype=complex), -shift, axis=0)


def interval_projection(size: int, length: int) -> np.ndarray:
    if not 0 < length < size:
        raise ValueError("interval length must lie strictly between zero and size")
    projection = np.zeros((size, size), dtype=complex)
    indices = np.arange(length)
    projection[indices, indices] = 1.0
    return projection


def single_crossing_certificate(
    size: int, radius: int, shift: int
) -> dict[str, float]:
    if shift <= 2 * radius:
        raise ValueError("shift must exceed twice the root radius")
    if 2 * shift + 2 * radius >= size:
        raise ValueError("size is too small for a non-wrapping crossing check")

    root = compact_root(size, radius)
    convolution = convolution_matrix(root)
    translation = translation_matrix(size, shift)
    interval = interval_projection(size, shift)

    crossing = translation @ interval
    sandwiched = convolution @ crossing @ convolution.conj().T
    left_factor = convolution @ translation @ interval
    right_factor = interval @ convolution.conj().T
    autocorrelation = np.vdot(root, np.roll(root, -shift))

    singular_values = np.linalg.svd(sandwiched, compute_uv=False)
    trace_norm = float(singular_values.sum())
    root_mass = float(np.vdot(root, root).real)
    expected_trace_norm = shift * root_mass
    left_hs_sq = float(np.linalg.norm(left_factor, ord="fro") ** 2)
    right_hs_sq = float(np.linalg.norm(right_factor, ord="fro") ** 2)
    holder_product = math.sqrt(left_hs_sq * right_hs_sq)

    return {
        "factorization_error": relative_error(
            left_factor @ right_factor, sandwiched
        ),
        "autocorrelation_magnitude": float(abs(autocorrelation)),
        "trace_magnitude": float(abs(np.trace(sandwiched))),
        "trace_formula_error": relative_error(
            np.trace(sandwiched), shift * autocorrelation
        ),
        "trace_norm": trace_norm,
        "trace_norm_error": relative_error(trace_norm, expected_trace_norm),
        "left_hs_sq_error": relative_error(left_hs_sq, expected_trace_norm),
        "right_hs_sq_error": relative_error(right_hs_sq, expected_trace_norm),
        "holder_product": holder_product,
        "holder_optimality_error": relative_error(
            holder_product, expected_trace_norm
        ),
    }


def crossing_block_ledger(
    modes: int, base_width: int, radius: int
) -> list[dict[str, float]]:
    if modes < 1:
        raise ValueError("modes must be positive")
    if base_width <= 2 * radius:
        raise ValueError("base width must exceed twice the root radius")

    ledger: list[dict[str, float]] = []
    for mode in range(modes):
        width = base_width * 2**mode
        size = 4 * width
        root = compact_root(size, radius)
        convolution = convolution_matrix(root)
        translation = translation_matrix(size, width)
        interval = interval_projection(size, width)
        coefficient = 1.0 / width

        positive_part = convolution @ interval @ convolution.conj().T
        block = coefficient * translation @ positive_part
        root_mass = float(np.vdot(root, root).real)
        trace_norm = coefficient * float(np.trace(positive_part).real)
        operator_norm = coefficient * float(
            np.linalg.norm(convolution @ interval, ord=2) ** 2
        )

        ledger.append(
            {
                "mode": float(mode),
                "width": float(width),
                "coefficient": coefficient,
                "trace_magnitude": float(abs(np.trace(block))),
                "trace_norm": trace_norm,
                "trace_norm_error": relative_error(trace_norm, root_mass),
                "operator_norm": operator_norm,
                "operator_bound": coefficient
                * float(np.linalg.norm(convolution, ord=2) ** 2),
            }
        )
    return ledger


def print_summary(
    single: dict[str, float], ledger: list[dict[str, float]]
) -> None:
    print("single compact-root crossing")
    print("+--------------------------------------+---------------+")
    print("| check                                | value         |")
    print("+--------------------------------------+---------------+")
    for label in (
        "factorization_error",
        "autocorrelation_magnitude",
        "trace_magnitude",
        "trace_formula_error",
        "trace_norm",
        "trace_norm_error",
        "left_hs_sq_error",
        "right_hs_sq_error",
        "holder_product",
        "holder_optimality_error",
    ):
        print(f"| {label:<36} | {single[label]:>13.6e} |")
    print("+--------------------------------------+---------------+")

    print()
    print("orthogonal crossing-block ledger")
    print("+------+-------+-----------+-----------+-----------+-----------+")
    print("| mode | width | coeff     | abs trace | trace norm| op norm   |")
    print("+------+-------+-----------+-----------+-----------+-----------+")
    for row in ledger:
        print(
            f"| {int(row['mode']):>4} | {int(row['width']):>5} "
            f"| {row['coefficient']:>9.3e} "
            f"| {row['trace_magnitude']:>9.3e} "
            f"| {row['trace_norm']:>9.3e} "
            f"| {row['operator_norm']:>9.3e} |"
        )
    print("+------+-------+-----------+-----------+-----------+-----------+")
    print(f"cumulative trace norm: {sum(row['trace_norm'] for row in ledger):.6f}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--size", type=int, default=256)
    parser.add_argument("--radius", type=int, default=6)
    parser.add_argument("--shift", type=int, default=40)
    parser.add_argument("--modes", type=int, default=4)
    parser.add_argument("--base-width", type=int, default=16)
    parser.add_argument("--tolerance", type=float, default=1e-10)
    args = parser.parse_args()

    single = single_crossing_certificate(args.size, args.radius, args.shift)
    ledger = crossing_block_ledger(args.modes, args.base_width, args.radius)
    print_summary(single, ledger)

    checked_errors = [
        single["factorization_error"],
        single["autocorrelation_magnitude"],
        single["trace_magnitude"],
        single["trace_formula_error"],
        single["trace_norm_error"],
        single["left_hs_sq_error"],
        single["right_hs_sq_error"],
        single["holder_optimality_error"],
    ]
    for row in ledger:
        checked_errors.extend(
            [
                row["trace_magnitude"],
                row["trace_norm_error"],
                max(row["operator_norm"] - row["operator_bound"], 0.0),
            ]
        )

    maximum_error = max(checked_errors)
    print(f"maximum checked error: {maximum_error:.6e}")
    if maximum_error > args.tolerance:
        raise SystemExit(
            f"certificate failed: {maximum_error:.6e} > {args.tolerance:.6e}"
        )


if __name__ == "__main__":
    main()
