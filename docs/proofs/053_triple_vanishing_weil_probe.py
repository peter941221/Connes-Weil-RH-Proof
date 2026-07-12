#!/usr/bin/env python3
"""Certify exact finite Weil matrices on the triple-vanishing even subspace.

For the finite Guinand--Weil dictionary, the even square test has
g_v(0) = log(c) * v_0^2.  The endpoint conditions g_v(+/- i/2)=0 collapse by
evenness to the paper's pole-neutral row.  Hence the relevant coefficient
subspace is v_0=0 together with that one row, not an arbitrary three-row
projection.
"""

from __future__ import annotations

import argparse
import importlib.util
from pathlib import Path

import mpmath as mp


def load_module(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load module: {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def arb_midpoint_to_mpf(value, digits: int) -> mp.mpf:
    return mp.mpf(value.mid().str(digits, radius=False, more=True))


def arb_midpoint_matrix(matrix, rows: int, columns: int, digits: int) -> mp.matrix:
    result = mp.matrix(rows, columns)
    for row in range(rows):
        for column in range(columns):
            result[row, column] = arb_midpoint_to_mpf(
                matrix[row, column], digits
            )
    return result


def certified_ldl_inertia(matrix, dimension: int) -> tuple[int, int, int]:
    from flint import arb

    lower = [[arb(0)] * dimension for _ in range(dimension)]
    diagonal = [None] * dimension
    positive = 0
    negative = 0
    for row in range(dimension):
        pivot = matrix[row, row]
        for column in range(row):
            pivot -= lower[row][column] ** 2 * diagonal[column]
        diagonal[row] = pivot
        if pivot > 0:
            positive += 1
        elif pivot < 0:
            negative += 1
        else:
            return positive, negative, dimension - positive - negative
        for target in range(row + 1, dimension):
            entry = matrix[target, row]
            for column in range(row):
                entry -= (
                    lower[target][column]
                    * lower[row][column]
                    * diagonal[column]
                )
            lower[target][row] = entry / pivot
    return positive, negative, 0


def even_embedding(N: int):
    from flint import arb, arb_mat

    full_dimension = 2 * N + 1
    embedding = arb_mat(full_dimension, N + 1)
    embedding[N, 0] = arb(1)
    inverse_sqrt_two = arb(1) / arb(2).sqrt()
    for frequency in range(1, N + 1):
        embedding[N - frequency, frequency] = inverse_sqrt_two
        embedding[N + frequency, frequency] = inverse_sqrt_two
    return embedding


def triple_vanishing_basis(c: int, N: int):
    from flint import arb, arb_mat

    if N < 2:
        raise ValueError("N must be at least 2 for a nonzero constrained space")
    log_c = arb(c).log()
    beta_squared = (log_c / (4 * arb.pi())) ** 2
    sqrt_two = arb(2).sqrt()
    pole_row = [arb(1) / beta_squared]
    pole_row.extend(
        sqrt_two / (arb(frequency * frequency) + beta_squared)
        for frequency in range(1, N + 1)
    )

    basis = arb_mat(N + 1, N - 1)
    pivot = pole_row[N]
    for column, frequency in enumerate(range(1, N)):
        basis[frequency, column] = arb(1)
        basis[N, column] = -pole_row[frequency] / pivot
    return basis, pole_row


def compress(matrix, left_basis, embedding):
    even_matrix = embedding.transpose() * matrix * embedding
    return left_basis.transpose() * even_matrix * left_basis


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--upstream", type=Path, required=True)
    parser.add_argument("--component-probe", type=Path, required=True)
    parser.add_argument("--c", type=int, default=13)
    parser.add_argument("--N", type=int, default=4)
    parser.add_argument("--prec", type=int, default=1024)
    args = parser.parse_args()

    from flint import arb, ctx

    ctx.prec = args.prec
    upstream = load_module("arb_ldlt_upstream", args.upstream)
    component_probe = load_module("cutoff_free_components", args.component_probe)

    total, full_dimension = upstream.build_arb_tau(args.c, args.N, args.prec)
    pole, gamma, prime, component_dimension = component_probe.build_components(
        upstream, args.c, args.N, args.prec
    )
    if component_dimension != full_dimension:
        raise RuntimeError("component and total dimensions disagree")

    embedding = even_embedding(args.N)
    basis, pole_row = triple_vanishing_basis(args.c, args.N)
    constrained_dimension = args.N - 1

    maximum_constraint_residual = arb(0)
    for column in range(constrained_dimension):
        endpoint_residual = arb(0)
        for row in range(args.N + 1):
            endpoint_residual += pole_row[row] * basis[row, column]
        maximum_constraint_residual = max(
            maximum_constraint_residual, abs(endpoint_residual)
        )
        if not endpoint_residual.contains(0):
            raise AssertionError("basis misses the pole-neutral row")
        if not basis[0, column].contains(0):
            raise AssertionError("basis misses v_0=0")

    compressed = {
        name: compress(matrix, basis, embedding)
        for name, matrix in (
            ("total", total),
            ("pole", pole),
            ("gamma", gamma),
            ("prime", prime),
        )
    }

    print(
        f"c={args.c} N={args.N} full_dimension={full_dimension} "
        f"even_dimension={args.N + 1} constrained_dimension={constrained_dimension} "
        f"Arb_bits={args.prec}"
    )
    print(f"constraint_residual={maximum_constraint_residual.str(8)}")

    digits = max(80, int(args.prec * 0.30103) - 20)
    mp.mp.dps = digits
    for name, matrix in compressed.items():
        inertia = certified_ldl_inertia(matrix, constrained_dimension)
        midpoint = arb_midpoint_matrix(
            matrix, constrained_dimension, constrained_dimension, digits
        )
        eigenvalues = mp.eigsy(midpoint, eigvals_only=True)
        print(
            f"{name}_inertia={inertia} "
            f"lambda_min_mid={mp.nstr(eigenvalues[0], 18)} "
            f"lambda_max_mid={mp.nstr(eigenvalues[constrained_dimension - 1], 18)}"
        )

    pole_matrix = compressed["pole"]
    for row in range(constrained_dimension):
        for column in range(constrained_dimension):
            if not pole_matrix[row, column].contains(0):
                raise AssertionError("pole block did not vanish on the same basis")


if __name__ == "__main__":
    main()
