#!/usr/bin/env python3
"""Test whether an exact finite Weil matrix is diagonally gauge-stoquastic.

For a real symmetric matrix with nonzero off-diagonal entries, a diagonal
unitary can make every off-diagonal entry real and nonpositive exactly when
the signed graph is switchable to all-negative edges.  Every triangle must
then have negative edge-sign product.  Arb intervals certify the entry signs.
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


def strict_sign(value) -> int:
    if value > 0:
        return 1
    if value < 0:
        return -1
    return 0


def midpoint_text(value, digits: int = 18) -> str:
    return value.mid().str(digits, radius=False, more=True)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--upstream", type=Path, required=True)
    parser.add_argument("--c", type=int, default=13)
    parser.add_argument("--N", type=int, default=2)
    parser.add_argument("--prec", type=int, default=512)
    parser.add_argument("--max-witnesses", type=int, default=8)
    args = parser.parse_args()

    upstream = load_module("arb_ldlt_upstream", args.upstream)
    matrix, dimension = upstream.build_arb_tau(args.c, args.N, args.prec)

    signs = [[0] * dimension for _ in range(dimension)]
    undetermined: list[tuple[int, int]] = []
    for row in range(dimension):
        for column in range(row + 1, dimension):
            sign = strict_sign(matrix[row, column])
            signs[row][column] = sign
            signs[column][row] = sign
            if sign == 0:
                undetermined.append((row, column))

    witnesses: list[tuple[int, int, int]] = []
    tested_triangles = 0
    for first in range(dimension):
        for second in range(first + 1, dimension):
            for third in range(second + 1, dimension):
                edge_signs = (
                    signs[first][second],
                    signs[second][third],
                    signs[third][first],
                )
                if 0 in edge_signs:
                    continue
                tested_triangles += 1
                if edge_signs[0] * edge_signs[1] * edge_signs[2] > 0:
                    witnesses.append((first, second, third))

    print(
        f"c={args.c} N={args.N} dimension={dimension} Arb_bits={args.prec}"
    )
    print(f"undetermined_offdiagonal_signs={len(undetermined)}")
    print(f"tested_nonzero_triangles={tested_triangles}")
    print(f"frustrated_triangles={len(witnesses)}")

    for first, second, third in witnesses[: args.max_witnesses]:
        print(f"witness=({first},{second},{third})")
        for row, column in (
            (first, second),
            (second, third),
            (third, first),
        ):
            print(
                f"  edge=({row},{column}) sign={signs[row][column]:+d} "
                f"mid={midpoint_text(matrix[row, column])}"
            )

    if undetermined:
        raise RuntimeError(
            "some off-diagonal signs are not certified; increase --prec"
        )
    if not witnesses:
        print("gauge_stoquasticity=not_rejected_by_triangle_test")
        return

    print("gauge_stoquasticity=rejected")


if __name__ == "__main__":
    main()
