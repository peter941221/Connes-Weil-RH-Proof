"""Screen the summed Gamma_R profile kernel on the Lane R nullspace.

The Lean owner decomposes the archimedean term into its constant, a finite
prefix of paired Gamma_R profiles, and a shifted profile tail.  This script
checks the numerical shape of that exact decomposition on a real sine basis
with the three Laplace constraints imposed exactly at the quadrature level.

It deliberately does not sign individual profiles or the tail.  Large
individual profiles can have positive directions.  The useful object is the
constant plus a finite prefix, with the remaining tail controlled in norm.
"""

from __future__ import annotations

import argparse
import math
from dataclasses import dataclass

import numpy as np
from numpy.polynomial.legendre import leggauss
from scipy.signal import fftconvolve


C_ARCH = math.log(4.0 * math.pi) + np.euler_gamma
LOG_TWO = math.log(2.0)
VANISH_S = (0.0, 0.5, 1.0)


@dataclass(frozen=True)
class Spectrum:
    minimum: float
    maximum: float


def spectrum(matrix: np.ndarray) -> Spectrum:
    eigenvalues = np.linalg.eigvalsh((matrix + matrix.T) / 2.0)
    return Spectrum(float(eigenvalues[0]), float(eigenvalues[-1]))


class SummedProfileProbe:
    """One L2-orthonormal sine nullspace and its paired profile matrices."""

    def __init__(self, radius: float, basis_size: int, quadrature_size: int):
        if radius <= 0.0 or 2.0 * radius >= LOG_TWO:
            raise ValueError("the convolution square must remain prime-free")
        if basis_size < 4:
            raise ValueError("at least four sine basis functions are required")
        if quadrature_size < 64:
            raise ValueError("quadrature_size must be at least 64")

        nodes, weights = leggauss(quadrature_size)
        self.radius = radius
        self.nodes = radius * nodes
        self.weights = radius * weights
        phase = math.pi * (nodes + 1.0) / 2.0
        frequencies = np.arange(1, basis_size + 1)[:, None]
        self.base_functions = np.sin(frequencies * phase[None, :]).T

        moments = np.stack(
            [
                self.base_functions.T
                @ (self.weights * np.exp(s * self.nodes))
                for s in VANISH_S
            ]
        )
        _, singular_values, vh = np.linalg.svd(moments, full_matrices=True)
        rank = int(np.sum(singular_values > 1e-12 * singular_values[0]))
        null_coefficients = vh[rank:].T

        weighted_base = self.base_functions * np.sqrt(self.weights)[:, None]
        weighted_null = weighted_base @ null_coefficients
        _, triangular = np.linalg.qr(weighted_null, mode="reduced")
        coefficients = null_coefficients @ np.linalg.solve(
            triangular, np.eye(triangular.shape[0])
        )
        self.coefficients = coefficients
        self.functions = (self.base_functions @ coefficients).T
        self.moment_residual = float(np.max(np.abs(moments @ coefficients)))
        gram = (self.functions * self.weights[None, :]) @ self.functions.T
        self.orthonormality_error = float(
            np.max(np.abs(gram - np.eye(gram.shape[0])))
        )

    def profile_matrix(self, index: int) -> np.ndarray:
        """The exact-inner-integral matrix for one paired profile J_index."""
        if index < 0:
            raise ValueError("profile index must be nonnegative")
        a = 2.0 * index + 0.5
        b = 2.0 * index + 1.0
        basis_size = self.coefficients.shape[0]
        frequencies = np.arange(1, basis_size + 1, dtype=float)
        omega = frequencies * math.pi / (2.0 * self.radius)
        theta = (self.nodes[:, None] + self.radius) * omega[None, :]
        denominator = a * a + omega * omega
        inner_action = (
            2.0 * a * np.sin(theta)
            + omega[None, :] * np.exp(-a * (self.nodes[:, None] + self.radius))
            - omega[None, :]
            * ((-1.0) ** frequencies)[None, :]
            * np.exp(-a * (self.radius - self.nodes[:, None]))
        ) / denominator[None, :]
        action = inner_action @ self.coefficients
        gram = (self.functions * self.weights[None, :]) @ self.functions.T
        resolvent = self.functions @ (self.weights[:, None] * action)
        result = resolvent - (2.0 / b) * gram
        return (result + result.T) / 2.0

    def functions_on_uniform_grid(self, grid_size: int) -> tuple[np.ndarray, float]:
        if grid_size < 5:
            raise ValueError("direct grid must have at least five points")
        count = grid_size if grid_size % 2 == 1 else grid_size + 1
        grid, step = np.linspace(-self.radius, self.radius, count, retstep=True)
        phase = math.pi * (grid + self.radius) / (2.0 * self.radius)
        frequencies = np.arange(1, self.coefficients.shape[0] + 1)[:, None]
        base = np.sin(frequencies * phase[None, :])
        return self.coefficients.T @ base, float(step)

    @staticmethod
    def direct_arch(function: np.ndarray, step: float) -> float:
        """The direct compact-support arch integral plus its analytic tail."""
        correlation = fftconvolve(function[::-1], function, mode="full") * step
        center = function.size - 1
        f_zero = float(correlation[center])
        if f_zero <= 0.0:
            raise FloatingPointError(f"non-positive convolution mass: {f_zero}")
        lags = step * np.arange(-center, center + 1)
        positive = lags > 1e-12
        y = lags[positive]
        f_y = correlation[positive]
        numerator = np.expm1(y / 2.0) * f_y + (f_y - f_zero)
        body = float(np.trapezoid(numerator / np.sinh(y), y))
        tail = f_zero * math.log(math.tanh(abs(lags[-1]) / 2.0))
        return C_ARCH * f_zero + body + tail

    def direct_arch_matrix(self, grid_size: int) -> np.ndarray:
        functions, step = self.functions_on_uniform_grid(grid_size)
        dimension = functions.shape[0]
        diagonal = np.array(
            [self.direct_arch(functions[i], step) for i in range(dimension)]
        )
        matrix = np.diag(diagonal)
        for i in range(dimension):
            for j in range(i):
                combined = self.direct_arch(functions[i] + functions[j], step)
                matrix[i, j] = (combined - diagonal[i] - diagonal[j]) / 2.0
                matrix[j, i] = matrix[i, j]
        return (matrix + matrix.T) / 2.0


def format_spectrum(value: Spectrum) -> str:
    return f"[{value.minimum:+.8e}, {value.maximum:+.8e}]"


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--radius", type=float, default=0.345)
    parser.add_argument("--basis-size", type=int, default=16)
    parser.add_argument("--quadrature-size", type=int, default=1800)
    parser.add_argument("--reference-length", type=int, default=3201)
    parser.add_argument("--direct-grid", type=int, default=6001)
    parser.add_argument(
        "--prefix-lengths",
        type=int,
        nargs="+",
        default=(1, 2, 3, 4, 5, 6, 11, 21, 41, 81, 161, 321, 641, 1281),
    )
    args = parser.parse_args()
    if args.reference_length < max(args.prefix_lengths):
        raise ValueError("reference-length must cover every requested prefix")

    probe = SummedProfileProbe(
        radius=args.radius,
        basis_size=args.basis_size,
        quadrature_size=args.quadrature_size,
    )
    dimension = probe.functions.shape[0]
    identity = np.eye(dimension)
    cumulative = C_ARCH * identity
    prefixes: dict[int, np.ndarray] = {}
    for index in range(args.reference_length):
        profile = probe.profile_matrix(index)
        cumulative = cumulative + profile
        length = index + 1
        if length in args.prefix_lengths:
            prefixes[length] = cumulative.copy()

    direct = probe.direct_arch_matrix(args.direct_grid)
    difference = cumulative - direct
    print("Lane R summed Gamma_R profile-kernel screen (2026-08-18)")
    print(
        f"radius={args.radius:.6f} square_radius={2 * args.radius:.6f} "
        f"log(2)={LOG_TWO:.12f} basis={args.basis_size} "
        f"nullity={dimension} quadrature={args.quadrature_size}"
    )
    print(
        f"moment_residual={probe.moment_residual:.3e} "
        f"orthonormality_error={probe.orthonormality_error:.3e}"
    )
    print(f"constant_only={C_ARCH:+.10e}")
    print("prefix length N        prefix spectrum              tail to reference")
    print("-" * 82)
    for length in args.prefix_lengths:
        prefix = prefixes[length]
        tail = cumulative - prefix
        print(
            f"{length:14d} {format_spectrum(spectrum(prefix)):>31} "
            f"{format_spectrum(spectrum(tail)):>31}"
        )
    print("-" * 82)
    print(
        f"reference length={args.reference_length}: "
        f"{format_spectrum(spectrum(cumulative))}"
    )
    print(f"direct grid={args.direct_grid}: {format_spectrum(spectrum(direct))}")
    print(f"max abs(reference-direct)={np.max(np.abs(difference)):.3e}")
    print(
        "The tail column is only the finite remainder through the reference "
        "index.  Its high-index positive directions do not license a termwise "
        "or tailwise sign claim."
    )


if __name__ == "__main__":
    main()
