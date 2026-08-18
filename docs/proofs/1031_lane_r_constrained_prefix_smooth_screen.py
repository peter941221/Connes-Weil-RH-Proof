"""Screen the N = 21 Gamma_R prefix on smooth compactly supported roots.

This is an independent numerical check of the fixed constrained-prefix
target.  Unlike the sine basis used by the earlier profile screen, every
basis vector here is a polynomial times a C-infinity bump, so its zero
extension is compatible with the CompactLogTest smoothness requirement.

For real g, the paired n-th Gamma_R profile of g^* * g is the quadratic form

  <g, exp(-a_n |x-y|) g> - 2 / b_n * ||g||_2^2,

where a_n = 2 n + 1/2 and b_n = 2 n + 1.  The script restricts this form to
the three Laplace-moment nullspace and reports the N = 21 prefix spectrum.
It is numerical route-selection evidence only, never a Lean theorem.
"""

from __future__ import annotations

import argparse
import math
from dataclasses import dataclass

import numpy as np
from numpy.polynomial.legendre import legvander
from scipy.signal import fftconvolve


ARCH_CONSTANT = math.log(4.0 * math.pi) + np.euler_gamma
LOG_TWO = math.log(2.0)
VANISH_NODES = (0.0, 0.5, 1.0)


def simpson_weights(count: int, step: float) -> np.ndarray:
    if count % 2 == 0:
        raise ValueError("Simpson quadrature needs an odd grid length")
    weights = np.ones(count)
    weights[1:-1:2] = 4.0
    weights[2:-1:2] = 2.0
    return weights * step / 3.0


def smooth_bump(x: np.ndarray) -> np.ndarray:
    result = np.zeros_like(x)
    interior = np.abs(x) < 1.0
    z = x[interior]
    result[interior] = np.exp(-1.0 / (1.0 - z * z))
    return result


@dataclass(frozen=True)
class ScreenResult:
    radius: float
    basis_size: int
    envelope_power: int
    constraint_count: int
    nullity: int
    prefix_minimum: float
    prefix_maximum: float
    unconstrained_positive_count: int
    unconstrained_maximum: float
    moment_residual: float
    orthonormality_error: float
    direct_difference: float


class SmoothPrefixScreen:
    def __init__(
        self,
        radius: float,
        basis_size: int,
        grid_size: int,
        envelope_power: int,
        constraint_nodes: tuple[float, ...],
    ):
        if radius <= 0.0 or 2.0 * radius >= LOG_TWO:
            raise ValueError("the convolution square must remain prime-free")
        if basis_size < 4:
            raise ValueError("at least four basis functions are required")
        if grid_size < 101:
            raise ValueError("the grid must contain at least 101 points")
        if envelope_power < 1:
            raise ValueError("the bump power must be positive")
        if not constraint_nodes:
            raise ValueError("at least one Laplace constraint is required")

        count = grid_size if grid_size % 2 == 1 else grid_size + 1
        self.radius = radius
        self.constraint_nodes = constraint_nodes
        self.grid, self.step = np.linspace(-radius, radius, count, retstep=True)
        self.moment_weights = simpson_weights(count, self.step)
        self.mass_weights = np.full(count, self.step)
        scaled = self.grid / radius
        envelope = smooth_bump(scaled) ** envelope_power
        self.base = legvander(scaled, basis_size - 1) * envelope[:, None]
        self.full_functions = self._orthonormalize(self.base)
        self.functions, self.moment_residual, self.orthonormality_error = (
            self._orthonormal_nullspace()
        )

    def _orthonormalize(self, functions: np.ndarray) -> np.ndarray:
        weighted = functions * np.sqrt(self.mass_weights)[:, None]
        _, triangular = np.linalg.qr(weighted, mode="reduced")
        if np.min(np.abs(np.diag(triangular))) < 1e-13:
            raise FloatingPointError("the sampled function family is rank deficient")
        return functions @ np.linalg.solve(
            triangular, np.eye(triangular.shape[0])
        )

    def _orthonormal_nullspace(self) -> tuple[np.ndarray, float, float]:
        moments = np.stack(
            [
                self.base.T @ (self.moment_weights * np.exp(node * self.grid))
                for node in self.constraint_nodes
            ]
        )
        _, singular_values, right_vectors = np.linalg.svd(moments, full_matrices=True)
        threshold = 1e-12 * max(float(singular_values[0]), 1.0)
        rank = int(np.sum(singular_values > threshold))
        raw_null = right_vectors[rank:].T
        raw_functions = self.base @ raw_null
        functions = self._orthonormalize(raw_functions)
        residual = float(
            np.max(
                np.abs(
                    np.stack(
                        [
                            functions.T
                            @ (self.moment_weights * np.exp(node * self.grid))
                            for node in self.constraint_nodes
                        ]
                    )
                )
            )
        )
        gram = functions.T @ (self.mass_weights[:, None] * functions)
        orthonormality_error = float(np.max(np.abs(gram - np.eye(gram.shape[0]))))
        return functions, residual, orthonormality_error

    def resolvent_matrix(self, functions: np.ndarray, exponent: float) -> np.ndarray:
        count = self.grid.size
        lags = self.step * np.arange(-(count - 1), count)
        kernel = np.exp(-exponent * np.abs(lags))
        full = fftconvolve(functions.T, kernel[None, :], mode="full", axes=1)
        action = full[:, count - 1 : count - 1 + count] * self.step
        matrix = functions.T @ (self.mass_weights[:, None] * action.T)
        return (matrix + matrix.T) / 2.0

    def prefix_matrix(self, functions: np.ndarray, prefix_length: int) -> np.ndarray:
        if prefix_length <= 0:
            raise ValueError("the prefix length must be positive")
        dimension = functions.shape[1]
        identity = np.eye(dimension)
        result = ARCH_CONSTANT * identity
        for index in range(prefix_length):
            exponent = 2.0 * index + 0.5
            mass_coefficient = 2.0 / (2.0 * index + 1.0)
            result += self.resolvent_matrix(functions, exponent) - mass_coefficient * identity
        return (result + result.T) / 2.0

    def direct_prefix_value(self, coefficients: np.ndarray, prefix_length: int) -> float:
        function = self.functions @ coefficients
        correlation = fftconvolve(function[::-1], function, mode="full") * self.step
        center = function.size - 1
        nonnegative_lags = self.step * np.arange(function.size)
        positive_correlation = correlation[center:]
        mass = float(correlation[center])
        value = ARCH_CONSTANT * mass
        for index in range(prefix_length):
            exponent = 2.0 * index + 0.5
            profile = 2.0 * np.trapezoid(
                np.exp(-exponent * nonnegative_lags) * positive_correlation,
                nonnegative_lags,
            )
            value += profile - 2.0 * mass / (2.0 * index + 1.0)
        return float(value)

    def solve(self, prefix_length: int, envelope_power: int) -> ScreenResult:
        matrix = self.prefix_matrix(self.functions, prefix_length)
        eigenvalues, eigenvectors = np.linalg.eigh(matrix)
        unconstrained = np.linalg.eigvalsh(
            self.prefix_matrix(self.full_functions, prefix_length)
        )
        least_negative = eigenvectors[:, -1]
        direct_difference = abs(
            self.direct_prefix_value(least_negative, prefix_length)
            - float(eigenvalues[-1])
        )
        return ScreenResult(
            radius=self.radius,
            basis_size=self.base.shape[1],
            envelope_power=envelope_power,
            constraint_count=len(self.constraint_nodes),
            nullity=self.functions.shape[1],
            prefix_minimum=float(eigenvalues[0]),
            prefix_maximum=float(eigenvalues[-1]),
            unconstrained_positive_count=int(np.sum(unconstrained > 1e-8)),
            unconstrained_maximum=float(unconstrained[-1]),
            moment_residual=self.moment_residual,
            orthonormality_error=self.orthonormality_error,
            direct_difference=direct_difference,
        )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--prefix-length", type=int, default=21)
    parser.add_argument("--grid-size", type=int, default=6001)
    parser.add_argument("--radii", type=float, nargs="+", default=(0.20, 0.30, 0.34, 0.3464))
    parser.add_argument("--basis-sizes", type=int, nargs="+", default=(8, 12, 16, 24, 32))
    parser.add_argument("--envelope-powers", type=int, nargs="+", default=(1, 2))
    parser.add_argument(
        "--constraint-nodes",
        type=float,
        nargs="+",
        default=VANISH_NODES,
        help="real Laplace nodes imposed on the sampled test functions",
    )
    args = parser.parse_args()

    if args.prefix_length <= 0:
        raise ValueError("the prefix length must be positive")
    if min(args.radii) <= 0.0 or 2.0 * max(args.radii) >= LOG_TWO:
        raise ValueError("every square support radius must be strictly below log(2)")

    print("Lane R smooth constrained-prefix screen (2026-08-19)")
    print(
        f"N={args.prefix_length} grid={args.grid_size} "
        f"prime-free square bound log(2)={LOG_TWO:.12f} "
        f"constraint_nodes={tuple(args.constraint_nodes)}"
    )
    print(
        "radius basis bump nodes nullity prefix_min prefix_max full_pos full_max "
        "moment_residual orth_error direct_diff"
    )
    print("-" * 118)
    for envelope_power in args.envelope_powers:
        for radius in args.radii:
            for basis_size in args.basis_sizes:
                screen = SmoothPrefixScreen(
                    radius,
                    basis_size,
                    args.grid_size,
                    envelope_power,
                    tuple(args.constraint_nodes),
                )
                result = screen.solve(args.prefix_length, envelope_power)
                print(
                    f"{result.radius:6.4f} {result.basis_size:5d} "
                    f"{result.envelope_power:4d} {result.constraint_count:5d} "
                    f"{result.nullity:7d} "
                    f"{result.prefix_minimum:+11.7f} {result.prefix_maximum:+11.7f} "
                    f"{result.unconstrained_positive_count:8d} {result.unconstrained_maximum:+10.6f} "
                    f"{result.moment_residual:.2e} {result.orthonormality_error:.2e} "
                    f"{result.direct_difference:.2e}"
                )
    print("-" * 118)
    print(
        "Negative maxima support the proposed finite-prefix inequality only "
        "on these finite sampled smooth subspaces.  They do not prove the "
        "universal constrained-prefix proposition or any RH-level statement."
    )


if __name__ == "__main__":
    main()
