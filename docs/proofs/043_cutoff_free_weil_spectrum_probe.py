#!/usr/bin/env python3
"""Probe the certified cutoff-free Weil matrix without a finite T cutoff.

The matrix builder is loaded from the arXiv:2607.02828 reproduction package.
Arb certifies every LDL pivot sign. Mpmath diagonalizes the high-precision Arb
midpoints only to measure scale; midpoint eigenvalues are diagnostic, not the
sign certificate.
"""

from __future__ import annotations

import argparse
import importlib.util
import math
from pathlib import Path

import mpmath as mp


def load_upstream(path: Path):
    spec = importlib.util.spec_from_file_location("arb_ldlt_upstream", path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load upstream module: {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def arb_midpoint_to_mpf(value, digits: int) -> mp.mpf:
    return mp.mpf(value.mid().str(digits, radius=False, more=True))


def certified_pivot_logs(matrix, dimension: int) -> tuple[list[float], int | None]:
    from flint import arb

    pivots = []
    lower = [[arb(0)] * dimension for _ in range(dimension)]
    diagonal = [None] * dimension
    for row in range(dimension):
        pivot = matrix[row, row]
        for column in range(row):
            pivot -= lower[row][column] ** 2 * diagonal[column]
        diagonal[row] = pivot
        if not (pivot > 0 or pivot < 0):
            return pivots, row
        pivots.append(math.log10(abs(float(pivot))))
        for target in range(row + 1, dimension):
            entry = matrix[target, row]
            for column in range(row):
                entry -= (
                    lower[target][column]
                    * lower[row][column]
                    * diagonal[column]
                )
            lower[target][row] = entry / pivot
    return pivots, None


def build_components(upstream, c: int, N: int, prec: int):
    """Reproduce the upstream W02 - WR - Wp assembly block by block."""
    from flint import arb, arb_mat, ctx

    ctx.prec = prec
    source_s, source_cc, source_xc, log_c = upstream.arb_closed_forms(N, c, prec)
    pi = arb.pi()
    sixteen_pi_squared = 16 * pi * pi
    log_c_squared = log_c * log_c
    pole_prefactor = 32 * log_c * (log_c / 4).sinh() ** 2
    kappa = upstream.arb_kappa(log_c)
    source_j = upstream.arb_J(log_c)

    prime_data = upstream.prime_powers_up_to(c)
    prime_weights = [
        arb(prime).log() * (arb(power) ** arb("-0.5"))
        for power, prime in prime_data
    ]
    prime_positions = [arb(power).log() for power, _ in prime_data]

    def signed_s(index: int):
        return source_s[index] if index >= 0 else -source_s[-index]

    dimension = 2 * N + 1
    pole = arb_mat(dimension, dimension)
    gamma = arb_mat(dimension, dimension)
    prime = arb_mat(dimension, dimension)
    for row in range(dimension):
        n = row - N
        for column in range(row, dimension):
            m = column - N
            numerator = log_c_squared - sixteen_pi_squared * m * n
            denominator = (
                (log_c_squared + sixteen_pi_squared * m * m)
                * (log_c_squared + sixteen_pi_squared * n * n)
            )
            pole_value = pole_prefactor * numerator / denominator
            if n == m:
                gamma_value = (
                    kappa
                    + 2 * source_cc[abs(n)]
                    + source_j
                    - (2 / log_c) * source_xc[abs(n)]
                )
            else:
                gamma_value = (signed_s(m) - signed_s(n)) / (pi * (n - m))

            prime_value = arb(0)
            for weight, position in zip(prime_weights, prime_positions):
                if n == m:
                    kernel = (
                        2
                        * (1 - position / log_c)
                        * (2 * pi * n * position / log_c).cos()
                    )
                else:
                    kernel = (
                        (2 * pi * m * position / log_c).sin()
                        - (2 * pi * n * position / log_c).sin()
                    ) / (pi * (n - m))
                prime_value += weight * kernel

            # Upstream convention: tau = W02 - WR - Wp.
            for matrix, value in (
                (pole, pole_value),
                (gamma, -gamma_value),
                (prime, -prime_value),
            ):
                matrix[row, column] = value
                matrix[column, row] = value
    return pole, gamma, prime, dimension


def arb_matrix_midpoint(matrix, dimension: int, digits: int) -> mp.matrix:
    midpoint = mp.matrix(dimension)
    for row in range(dimension):
        for column in range(dimension):
            midpoint[row, column] = arb_midpoint_to_mpf(
                matrix[row, column], digits
            )
    return midpoint


def certified_rayleigh_ball(matrix, vector, dimension: int, digits: int):
    """Evaluate one fixed decimal vector with Arb interval arithmetic."""
    from flint import arb

    arb_vector = [
        arb(mp.nstr(vector[index], max(40, digits - 20)))
        for index in range(dimension)
    ]
    norm_squared = arb(0)
    quadratic = arb(0)
    for row in range(dimension):
        norm_squared += arb_vector[row] * arb_vector[row]
        for column in range(dimension):
            quadratic += (
                arb_vector[row]
                * matrix[row, column]
                * arb_vector[column]
            )
    return quadratic / norm_squared


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--upstream", type=Path, required=True)
    parser.add_argument("--c", type=int, required=True)
    parser.add_argument("--N", type=int, required=True)
    parser.add_argument("--prec", type=int, default=2000, help="Arb bits")
    parser.add_argument("--components", action="store_true")
    args = parser.parse_args()

    upstream = load_upstream(args.upstream)
    matrix, dimension = upstream.build_arb_tau(args.c, args.N, args.prec)
    pivot_logs, undetermined = certified_pivot_logs(matrix, dimension)
    if undetermined is not None:
        raise RuntimeError(
            f"Arb pivot {undetermined} is undetermined; increase --prec"
        )

    digits = max(80, int(args.prec * 0.30103) - 20)
    mp.mp.dps = digits
    midpoint = arb_matrix_midpoint(matrix, dimension, digits)

    eigenvalues, eigenvectors = mp.eigsy(midpoint)
    lambda_min = eigenvalues[0]
    lambda_max = eigenvalues[dimension - 1]
    condition = abs(lambda_max / lambda_min)

    print(f"c={args.c} N={args.N} dimension={dimension} Arb_bits={args.prec}")
    print("certified_inertia=positive")
    print(f"min_LDL_pivot_log10={min(pivot_logs):.6f}")
    print(f"lambda_min_midpoint={mp.nstr(lambda_min, 18)}")
    print(f"lambda_max_midpoint={mp.nstr(lambda_max, 18)}")
    print(f"condition_midpoint={mp.nstr(condition, 18)}")

    vector = eigenvectors[:, 0]
    total_rayleigh_ball = certified_rayleigh_ball(
        matrix, vector, dimension, digits
    )
    print(f"certified_total_rayleigh={total_rayleigh_ball.str(18)}")

    if args.components:
        pole, gamma, prime, component_dimension = build_components(
            upstream, args.c, args.N, args.prec
        )
        if component_dimension != dimension:
            raise RuntimeError("component dimension does not match total")
        component_values = {}
        for name, component in (
            ("pole", pole),
            ("gamma", gamma),
            ("prime", prime),
        ):
            component_midpoint = arb_matrix_midpoint(
                component, dimension, digits
            )
            component_values[name] = (vector.T * component_midpoint * vector)[0]
            print(
                f"rayleigh_{name}_midpoint="
                f"{mp.nstr(component_values[name], 18)}"
            )
            print(
                f"certified_rayleigh_{name}="
                f"{certified_rayleigh_ball(component, vector, dimension, digits).str(18)}"
            )
        reconstructed = sum(component_values.values())
        print(f"rayleigh_sum_midpoint={mp.nstr(reconstructed, 18)}")


if __name__ == "__main__":
    main()
