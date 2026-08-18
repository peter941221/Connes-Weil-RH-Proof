"""Screen finite-prefix choices against an absolute Gamma_R tail budget.

The exact owner is loaded from the 1022 summed-kernel probe.  For each
triple-vanishing sine nullspace, this script compares the largest eigenvalue
of the constant-plus-prefix form with the same-vector finite tail
sum(abs(profile_n)).  The tail is truncated at ``tail_end``; no infinite-tail
claim is made.
"""

from __future__ import annotations

import argparse
import importlib.util
import sys
from pathlib import Path

import numpy as np


def load_summed_profile_probe():
    path = Path(__file__).with_name("1022_lane_r_summed_gamma_kernel_probe.py")
    specification = importlib.util.spec_from_file_location("summed_profile_probe", path)
    if specification is None or specification.loader is None:
        raise RuntimeError(f"cannot load probe at {path}")
    module = importlib.util.module_from_spec(specification)
    sys.modules[specification.name] = module
    specification.loader.exec_module(module)
    return module


def normalized_samples(rng: np.random.Generator, count: int, dimension: int) -> np.ndarray:
    samples = rng.normal(size=(count, dimension))
    return samples / np.linalg.norm(samples, axis=1)[:, None]


def scan_case(
    probe_module,
    radius: float,
    basis_size: int,
    quadrature_size: int,
    prefix_lengths: tuple[int, ...],
    tail_end: int,
    sample_count: int,
    rng: np.random.Generator,
) -> list[dict[str, float]]:
    probe = probe_module.SummedProfileProbe(radius, basis_size, quadrature_size)
    dimension = probe.functions.shape[0]
    profile_stack = np.stack([probe.profile_matrix(n) for n in range(tail_end)])
    identity = np.eye(dimension)
    prefixes: dict[int, np.ndarray] = {}
    cumulative = probe_module.C_ARCH * identity
    for index in range(max(prefix_lengths)):
        cumulative = cumulative + profile_stack[index]
        length = index + 1
        if length in prefix_lengths:
            prefixes[length] = cumulative.copy()

    samples = normalized_samples(rng, sample_count, dimension)
    results: list[dict[str, float]] = []
    for length in prefix_lengths:
        prefix = prefixes[length]
        eigenvalues, eigenvectors = np.linalg.eigh(prefix)
        vectors = np.vstack((eigenvectors[:, -1], samples))
        prefix_values = np.einsum("bi,ij,bj->b", vectors, prefix, vectors)
        tail_values = np.einsum(
            "bi,nij,bj->bn", vectors, profile_stack[length:tail_end], vectors
        )
        tail_absolute = np.sum(np.abs(tail_values), axis=1)
        valid = prefix_values < 0.0
        if not valid[0]:
            raise FloatingPointError(
                "the least-negative prefix direction is nonnegative"
            )
        sample_valid = valid[1:]
        if not np.any(sample_valid):
            raise FloatingPointError("random samples contain no negative prefix direction")
        sample_ratios = tail_absolute[1:][sample_valid] / (
            -prefix_values[1:][sample_valid]
        )
        results.append(
            {
                "radius": radius,
                "basis": float(basis_size),
                "length": float(length),
                "prefix_max": float(eigenvalues[-1]),
                "least_margin_ratio": float(tail_absolute[0] / (-prefix_values[0])),
                "sample_min_ratio": float(np.min(sample_ratios)),
                "sample_max_ratio": float(np.max(sample_ratios)),
                "valid_fraction": float(np.mean(valid)),
                "finite_tail_end": float(tail_end),
            }
        )
    return results


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--radii", type=float, nargs="+", default=(0.20, 0.30, 0.34))
    parser.add_argument("--basis-sizes", type=int, nargs="+", default=(16, 24))
    parser.add_argument("--quadrature-size", type=int, default=1200)
    parser.add_argument("--prefix-lengths", type=int, nargs="+", default=(4, 21))
    parser.add_argument("--tail-end", type=int, default=801)
    parser.add_argument("--samples", type=int, default=3000)
    parser.add_argument("--seed", type=int, default=20260818)
    args = parser.parse_args()
    if min(args.radii) <= 0.0 or max(args.radii) * 2.0 >= np.log(2.0):
        raise ValueError("every square support radius must be below log(2)")
    if min(args.prefix_lengths) <= 0 or args.tail_end <= max(args.prefix_lengths):
        raise ValueError("tail-end must exceed every positive prefix length")

    probe_module = load_summed_profile_probe()
    rng = np.random.default_rng(args.seed)
    results = []
    for radius in args.radii:
        for basis_size in args.basis_sizes:
            results.extend(
                scan_case(
                    probe_module,
                    radius,
                    basis_size,
                    args.quadrature_size,
                    tuple(args.prefix_lengths),
                    args.tail_end,
                    args.samples,
                    rng,
                )
            )

    print("Lane R prefix/tail absolute-budget screen (2026-08-18)")
    print(
        f"quadrature={args.quadrature_size} tail_indices=[N,{args.tail_end}) "
        f"samples={args.samples} seed={args.seed}"
    )
    print(
        "radius basis N prefix_max least_margin_ratio "
        "sample_min_ratio sample_max_ratio valid_fraction"
    )
    print("-" * 105)
    for result in results:
        print(
            f"{result['radius']:6.3f} {int(result['basis']):5d} "
            f"{int(result['length']):2d} {result['prefix_max']:+11.6f} "
            f"{result['least_margin_ratio']:17.6f} "
            f"{result['sample_min_ratio']:16.6f} "
            f"{result['sample_max_ratio']:16.6f} "
            f"{result['valid_fraction']:13.6f}"
        )
    print("-" * 105)
    print(
        "Ratios use only the finite tail N <= n < tail_end.  A ratio below one "
        "is a candidate budget, not an infinite-tail proof; a ratio above one "
        "rejects that finite absolute-budget coupling for the sampled vector."
    )


if __name__ == "__main__":
    main()
