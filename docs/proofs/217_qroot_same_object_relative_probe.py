#!/usr/bin/env python3
"""Same-object Q-root screen for the coarse CC20 relative form.

The source root and the M4 pre-root are related by

    g = (d/dx + 1/2) xi.

The finite-prime translation form acts on ``g``, while the scalar and compact
M4 remainder act on ``xi``.  On the range condition

    integral exp(x/2) g(x) dx = 0,

the inverse is the Volterra operator

    xi(x) = exp(-x/2) integral_(-a)^x exp(t/2) g(t) dt.

This probe screens the correctly owned coarse form

    (1/50) ||g||^2 + 2 ||xi||^2 - <g, K_c g>,

before the ordinary compact kernel is reinserted.  It is a finite-grid death
test, not an interval certificate.
"""

from __future__ import annotations

import argparse
from importlib import import_module

import numpy as np
from scipy.linalg import null_space, toeplitz


principal_probe = import_module("215_all_prime_principal_form_probe")


def volterra_qroot_inverse(points: np.ndarray, mesh: float) -> np.ndarray:
    exponent_difference = (points[None, :] - points[:, None]) / 2
    return mesh * np.tril(np.exp(exponent_difference))


def constrained_minimum(matrix: np.ndarray, rows: np.ndarray) -> float:
    basis = null_space(rows)
    compressed = basis.T @ matrix @ basis
    return float(np.linalg.eigvalsh(compressed)[0])


def single_prime_operator(
    cutoff: int, size: int, prime: int
) -> tuple[np.ndarray, int]:
    interval_length = np.log(cutoff)
    mesh = interval_length / (size + 1)
    diagonals = np.zeros(size)
    prime_power = prime
    term_count = 0
    while prime_power < cutoff:
        grid_shift = np.log(prime_power) / mesh
        lower_diagonal = int(np.floor(grid_shift))
        fraction = grid_shift - lower_diagonal
        weight = np.log(prime) / np.sqrt(prime_power)
        if lower_diagonal < size:
            if lower_diagonal == 0:
                diagonals[0] += 2 * weight * (1 - fraction)
            else:
                diagonals[lower_diagonal] += weight * (1 - fraction)
        if lower_diagonal + 1 < size:
            diagonals[lower_diagonal + 1] += weight * fraction
        prime_power *= prime
        term_count += 1
    return toeplitz(diagonals), term_count


def run_cutoff(cutoff: int, size: int, single_prime: int | None) -> None:
    points, _, _, all_prime_operator, all_term_count = (
        principal_probe.build_principal_form(cutoff, size)
    )
    if single_prime is None:
        prime_operator = all_prime_operator
        term_count = all_term_count
        channel = "all"
    else:
        prime_operator, term_count = single_prime_operator(
            cutoff, size, single_prime
        )
        channel = f"p={single_prime}"
    mesh = np.log(cutoff) / (size + 1)
    inverse = volterra_qroot_inverse(points, mesh)
    coarse_form = (
        np.eye(size) / 50
        + 2 * inverse.T @ inverse
        - prime_operator
    )

    mean = np.ones_like(points)
    exp_positive = np.exp(points / 2)
    exp_negative = np.exp(-points / 2)
    cosh_row = np.cosh(points / 2)
    sinh_row = np.sinh(points / 2)
    cases = {
        "range": exp_positive[None, :],
        "pole": np.vstack((exp_positive, exp_negative)),
        "all": np.vstack((mean, cosh_row, sinh_row)),
    }

    print(
        f"cutoff={cutoff} size={size} channel={channel} "
        f"prime_power_terms={term_count}"
    )
    for name, rows in cases.items():
        print(
            f"  {name:5s} minimum="
            f"{constrained_minimum(coarse_form, rows):.12f}"
        )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--cutoff", type=int, nargs="+", default=[16, 64, 256, 1024]
    )
    parser.add_argument("--size", type=int, default=500)
    parser.add_argument("--single-prime", type=int)
    args = parser.parse_args()
    for cutoff in args.cutoff:
        run_cutoff(cutoff, args.size, args.single_prime)


if __name__ == "__main__":
    main()
