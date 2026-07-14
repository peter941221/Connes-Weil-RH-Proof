#!/usr/bin/env python3
"""Finite-difference screen for the all-prime principal relative form.

The screened matrix is

    (1/50)(-d^2+1/4) + 2 I - K_c,

where K_c is the exact finite von-Mangoldt translation sum, discretized by
linear interpolation on a uniform grid with zero extension.  The translation
sum is assembled as one Toeplitz matrix after aggregating all prime powers.

This is a rejection/feasibility probe, not an interval certificate.
"""

from __future__ import annotations

import argparse
import math

import numpy as np
from scipy.linalg import eigvalsh, null_space, toeplitz


def primes_up_to(limit: int) -> list[int]:
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[:2] = b"\x00\x00"
    for prime in range(2, math.isqrt(limit) + 1):
        if sieve[prime]:
            start = prime * prime
            sieve[start : limit + 1 : prime] = b"\x00" * (
                (limit - start) // prime + 1
            )
    return [value for value in range(2, limit + 1) if sieve[value]]


def translation_diagonals(cutoff: int, size: int) -> tuple[np.ndarray, int]:
    interval_length = math.log(cutoff)
    mesh = interval_length / (size + 1)
    diagonals = np.zeros(size)
    term_count = 0
    for prime in primes_up_to(cutoff):
        prime_power = prime
        while prime_power < cutoff:
            grid_shift = math.log(prime_power) / mesh
            lower_diagonal = int(math.floor(grid_shift))
            fraction = grid_shift - lower_diagonal
            weight = math.log(prime) / math.sqrt(prime_power)
            if lower_diagonal < size:
                if lower_diagonal == 0:
                    diagonals[0] += 2 * weight * (1 - fraction)
                else:
                    diagonals[lower_diagonal] += weight * (1 - fraction)
            if lower_diagonal + 1 < size:
                diagonals[lower_diagonal + 1] += weight * fraction
            term_count += 1
            prime_power *= prime
    return diagonals, term_count


def build_principal_form(cutoff: int, size: int):
    interval_length = math.log(cutoff)
    mesh = interval_length / (size + 1)
    points = -interval_length / 2 + mesh * np.arange(1, size + 1)

    laplacian = (
        np.diag(np.full(size, 2 / mesh**2))
        + np.diag(np.full(size - 1, -1 / mesh**2), 1)
        + np.diag(np.full(size - 1, -1 / mesh**2), -1)
    )
    diagonals, term_count = translation_diagonals(cutoff, size)
    prime_operator = toeplitz(diagonals)
    derivative_part = laplacian / 50 + np.eye(size) / 200
    principal_form = derivative_part + 2 * np.eye(size) - prime_operator
    return points, principal_form, derivative_part, prime_operator, term_count


def constrained_minimum(matrix: np.ndarray, rows: np.ndarray):
    if rows.shape[0] == 0:
        basis = np.eye(matrix.shape[0])
    else:
        basis = null_space(rows)
    compressed = basis.T @ matrix @ basis
    value, vector = np.linalg.eigh(compressed)
    return float(value[0]), basis @ vector[:, 0]


def run_cutoff(cutoff: int, size: int) -> None:
    points, form, derivative, prime, term_count = build_principal_form(
        cutoff, size
    )
    mean = np.ones_like(points)
    cosh_row = np.cosh(points / 2)
    sinh_row = np.sinh(points / 2)
    cases = {
        "none": np.empty((0, size)),
        "mean": mean[None, :],
        "cosh": cosh_row[None, :],
        "sinh": sinh_row[None, :],
        "all": np.vstack((mean, cosh_row, sinh_row)),
    }

    print(f"cutoff={cutoff} size={size} prime_power_terms={term_count}")
    for name, rows in cases.items():
        minimum, vector = constrained_minimum(form, rows)
        if name == "all":
            derivative_value = float(vector @ derivative @ vector)
            prime_value = float(vector @ prime @ vector)
            print(
                f"  {name:5s} minimum={minimum:.12f} "
                f"derivative={derivative_value:.12f} "
                f"prime={prime_value:.12f}"
            )
        else:
            print(f"  {name:5s} minimum={minimum:.12f}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--cutoff",
        type=int,
        nargs="+",
        default=[16, 64, 256, 1024, 10000],
    )
    parser.add_argument("--size", type=int, default=500)
    args = parser.parse_args()
    for cutoff in args.cutoff:
        run_cutoff(cutoff, args.size)


if __name__ == "__main__":
    main()
