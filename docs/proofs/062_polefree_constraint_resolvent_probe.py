#!/usr/bin/env python3
"""Certify pole-free constraint inertias and the finite resolvent scalar.

The even pole-free block is Gamma+prime.  The source pole block is
2|C><C|=C_c beta^2 r r^T, fixing the normalization of C.  Arb checks which
vanishing row removes the negative direction and certifies
G(0)=<C,A_tilde^{-1}C>.
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


def coordinate_kernel_basis(row, ambient_dimension: int, pivot_index: int):
    from flint import arb, arb_mat

    basis = arb_mat(ambient_dimension, ambient_dimension - 1)
    pivot = row[pivot_index]
    column = 0
    for index in range(ambient_dimension):
        if index == pivot_index:
            continue
        basis[index, column] = arb(1)
        basis[pivot_index, column] = -row[index] / pivot
        column += 1
    return basis


def compress(matrix, basis):
    return basis.transpose() * matrix * basis


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--upstream", type=Path, required=True)
    parser.add_argument("--component-probe", type=Path, required=True)
    parser.add_argument("--triple-probe", type=Path, required=True)
    parser.add_argument("--c", type=int, default=13)
    parser.add_argument("--N", type=int, default=8)
    parser.add_argument("--prec", type=int, default=2048)
    args = parser.parse_args()

    from flint import arb, arb_mat, ctx

    if args.N < 2:
        raise ValueError("N must be at least 2")
    ctx.prec = args.prec
    upstream = load_module("arb_ldlt_upstream", args.upstream)
    components = load_module("cutoff_free_components", args.component_probe)
    triple = load_module("triple_vanishing_probe", args.triple_probe)

    pole, gamma, prime, _ = components.build_components(
        upstream, args.c, args.N, args.prec
    )
    embedding = triple.even_embedding(args.N)
    pole_free = embedding.transpose() * (gamma + prime) * embedding
    ambient_dimension = args.N + 1

    triple_basis, pole_row = triple.triple_vanishing_basis(args.c, args.N)

    mean_zero_basis = arb_mat(ambient_dimension, args.N)
    for column in range(args.N):
        mean_zero_basis[column + 1, column] = arb(1)

    pole_neutral_basis = coordinate_kernel_basis(
        pole_row, ambient_dimension, args.N
    )

    inertias = {
        "full": triple.certified_ldl_inertia(pole_free, ambient_dimension),
        "mean_zero": triple.certified_ldl_inertia(
            compress(pole_free, mean_zero_basis), args.N
        ),
        "pole_neutral": triple.certified_ldl_inertia(
            compress(pole_free, pole_neutral_basis), args.N
        ),
        "triple": triple.certified_ldl_inertia(
            compress(pole_free, triple_basis), args.N - 1
        ),
    }

    log_c = arb(args.c).log()
    beta_squared = (log_c / (4 * arb.pi())) ** 2
    pole_constant = (
        log_c
        * (arb(args.c).sqrt() + arb(1) / arb(args.c).sqrt() - 2)
        / (2 * arb.pi() ** 2)
    )
    c_scale = (pole_constant * beta_squared / 2).sqrt()
    c_vector = arb_mat(ambient_dimension, 1)
    for row in range(ambient_dimension):
        c_vector[row, 0] = c_scale * pole_row[row]

    solution = pole_free.solve(c_vector)
    resolvent_scalar = (c_vector.transpose() * solution)[0, 0]
    secular_at_zero = 1 + 2 * resolvent_scalar

    print(
        f"c={args.c} N={args.N} even_dimension={ambient_dimension} "
        f"Arb_bits={args.prec}"
    )
    for name, inertia in inertias.items():
        print(f"{name}_inertia={inertia}")
    print(f"G(0)={resolvent_scalar.str(25)}")
    print(f"1+2G(0)={secular_at_zero.str(25)}")

    expected = {
        "full": (args.N, 1, 0),
        "mean_zero": (args.N - 1, 1, 0),
        "pole_neutral": (args.N, 0, 0),
        "triple": (args.N - 1, 0, 0),
    }
    if inertias != expected:
        raise AssertionError(f"unexpected constraint inertia pattern: {inertias}")
    if not resolvent_scalar < 0:
        raise AssertionError("expected the pole resolvent scalar to be negative")
    print("finite_pole_neutral_compression=certified_positive")


if __name__ == "__main__":
    main()
