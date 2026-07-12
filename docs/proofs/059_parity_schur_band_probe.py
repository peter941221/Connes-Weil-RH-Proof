#!/usr/bin/env python3
"""Certify parity Schur pivots for nested cutoff-free Weil matrices.

At fixed prime cutoff c, reflection symmetry splits the band-N matrix into an
even block on frequencies 0..N and an odd block on frequencies 1..N.  Each
band extension adds one coordinate per parity.  The last natural-order LDL
pivot is the exact scalar Schur complement against the previous band.
"""

from __future__ import annotations

import argparse
import importlib.util
from pathlib import Path


def load_module(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load module: {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def parity_blocks(matrix, N: int):
    from flint import arb, arb_mat

    full_dimension = 2 * N + 1
    inverse_sqrt_two = arb(1) / arb(2).sqrt()

    even_embedding = arb_mat(full_dimension, N + 1)
    even_embedding[N, 0] = arb(1)
    odd_embedding = arb_mat(full_dimension, N)
    for frequency in range(1, N + 1):
        negative_index = N - frequency
        positive_index = N + frequency
        even_embedding[negative_index, frequency] = inverse_sqrt_two
        even_embedding[positive_index, frequency] = inverse_sqrt_two
        odd_embedding[negative_index, frequency - 1] = -inverse_sqrt_two
        odd_embedding[positive_index, frequency - 1] = inverse_sqrt_two

    even = even_embedding.transpose() * matrix * even_embedding
    odd = odd_embedding.transpose() * matrix * odd_embedding
    return even, odd


def certified_ldl_pivots(matrix, dimension: int):
    from flint import arb

    lower = [[arb(0)] * dimension for _ in range(dimension)]
    diagonal = [None] * dimension
    for row in range(dimension):
        pivot = matrix[row, row]
        for column in range(row):
            pivot -= lower[row][column] ** 2 * diagonal[column]
        diagonal[row] = pivot
        if not (pivot > 0 or pivot < 0):
            raise RuntimeError(f"undetermined LDL pivot {row}")
        for target in range(row + 1, dimension):
            entry = matrix[target, row]
            for column in range(row):
                entry -= (
                    lower[target][column]
                    * lower[row][column]
                    * diagonal[column]
                )
            lower[target][row] = entry / pivot
    return diagonal


def midpoint(value, digits: int = 16) -> str:
    return value.mid().str(digits, radius=False, more=True)


def report(parity: str, level: int, block, dimension: int) -> None:
    pivots = certified_ldl_pivots(block, dimension)
    pivot = pivots[-1]
    diagonal = block[dimension - 1, dimension - 1]
    correction = diagonal - pivot
    ratio = pivot / diagonal

    if not pivot > 0:
        raise AssertionError(f"{parity} Schur pivot is not positive")
    if not diagonal > 0:
        raise AssertionError(f"{parity} new diagonal is not positive")
    if level > 1 and not correction > 0:
        raise AssertionError(f"{parity} inverse correction is not positive")

    print(
        f"N={level} parity={parity} "
        f"diagonal={midpoint(diagonal)} "
        f"schur={midpoint(pivot)} "
        f"inverse_correction={midpoint(correction)} "
        f"schur_over_diagonal={midpoint(ratio)}"
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--upstream", type=Path, required=True)
    parser.add_argument("--c", type=int, default=13)
    parser.add_argument("--max-N", type=int, default=16)
    parser.add_argument("--prec", type=int, default=3072)
    args = parser.parse_args()

    from flint import ctx

    if args.max_N < 1:
        raise ValueError("--max-N must be positive")
    ctx.prec = args.prec
    upstream = load_module("arb_ldlt_upstream", args.upstream)

    print(f"c={args.c} max_N={args.max_N} Arb_bits={args.prec}")
    for level in range(1, args.max_N + 1):
        matrix, _ = upstream.build_arb_tau(args.c, level, args.prec)
        even, odd = parity_blocks(matrix, level)
        report("even", level, even, level + 1)
        report("odd", level, odd, level)


if __name__ == "__main__":
    main()
