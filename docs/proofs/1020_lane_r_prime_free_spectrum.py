"""Lane R prime-free archimedean spectrum scan.

This is a deterministic follow-up to 1017. It forms floating-point
moment-constrained compression matrices in two sampled basis families and
reports their extremal eigenvalues after L2 normalization. The enveloped
Legendre family has smooth compactly supported profiles. The sine family is an
L2 cross-check whose zero extensions are not C-infinity at the endpoints.

For a base support [-r, r], the square is supported in [-2r, 2r].  The
prime-free regime is therefore 2r < log(2).  The three rows of the moment
matrix impose laplaceAt(g, s) = 0 at s = 0, 1/2, 1.

The scan is numerical evidence only.  It does not transfer a sign to a Lean
owner and it does not address the prime-inclusive Lane R problem.
"""

from __future__ import annotations

import argparse
import math
from dataclasses import dataclass

import numpy as np
from numpy.polynomial.legendre import legvander
from scipy.linalg import eigh
from scipy.signal import fftconvolve


C_ARCH = math.log(4.0 * math.pi) + np.euler_gamma
LOG_TWO = math.log(2.0)
VANISH_S = (0.0, 0.5, 1.0)


def simpson_weights(n: int, step: float) -> np.ndarray:
    """Composite Simpson weights on an odd, uniformly spaced grid."""
    if n % 2 == 0:
        raise ValueError("the grid must have an odd number of points")
    weights = np.ones(n)
    weights[1:-1:2] = 4.0
    weights[2:-1:2] = 2.0
    return weights * step / 3.0


def smooth_bump(x: np.ndarray) -> np.ndarray:
    """A C-infinity bump on (-1, 1), with value zero at the endpoints."""
    out = np.zeros_like(x)
    inside = np.abs(x) < 1.0
    z = x[inside]
    out[inside] = np.exp(-1.0 / (1.0 - z * z))
    return out


@dataclass
class SpectrumResult:
    radius: float
    basis_size: int
    envelope_power: int
    basis_family: str
    nullity: int
    singular_values: np.ndarray
    eigenvalues: np.ndarray
    max_constraint_residual: float
    gram_condition: float
    orthonormality_error: float


class PrimeFreeProbe:
    """Numerical owner for one compact support and one basis size."""

    def __init__(
        self,
        radius: float,
        basis_size: int,
        grid_size: int = 6001,
        envelope_power: int = 1,
        basis_family: str = "legendre",
    ):
        if radius <= 0.0:
            raise ValueError("radius must be positive")
        if 2.0 * radius >= LOG_TWO:
            raise ValueError("the requested square is not prime-free")
        if basis_size < 4:
            raise ValueError("at least four basis functions are needed")
        if envelope_power < 1:
            raise ValueError("the envelope power must be positive")
        if basis_family not in ("legendre", "sine"):
            raise ValueError("basis_family must be 'legendre' or 'sine'")
        self.radius = radius
        self.basis_size = basis_size
        self.envelope_power = envelope_power
        self.basis_family = basis_family
        self.n = grid_size if grid_size % 2 == 1 else grid_size + 1
        self.t, self.step = np.linspace(
            -radius, radius, self.n, retstep=True
        )
        self.quad = simpson_weights(self.n, self.step)
        # The correlation routine uses a rectangle rule.  Endpoints vanish,
        # so these weights agree with the corresponding trapezoid mass.
        self.mass = np.full(self.n, self.step)

        scaled = self.t / radius
        if basis_family == "legendre":
            # Legendre profiles keep the moment matrix much better
            # conditioned than raw exponentials as the basis grows.
            vandermonde = legvander(scaled, basis_size - 1)
            envelope = smooth_bump(scaled) ** envelope_power
            self.basis = (vandermonde.T * envelope).astype(float)
        else:
            # Sine profiles are an independent L2 basis check.  They vanish
            # at the support endpoints and avoid any bump-envelope choice.
            phase = math.pi * (scaled + 1.0) / 2.0
            frequencies = np.arange(1, basis_size + 1)[:, None]
            self.basis = np.sin(frequencies * phase[None, :])

    def laplace_matrix(self) -> np.ndarray:
        return np.stack(
            [
                np.sum(
                    self.quad[None, :] * self.basis
                    * np.exp(s * self.t)[None, :],
                    axis=1,
                )
                for s in VANISH_S
            ]
        )

    def l2_gram(self) -> np.ndarray:
        return (self.basis * self.mass[None, :]) @ self.basis.T

    def nullspace(self) -> tuple[np.ndarray, np.ndarray]:
        moments = self.laplace_matrix()
        _, singular_values, vh = np.linalg.svd(
            moments, full_matrices=True
        )
        threshold = 1e-11 * max(float(singular_values[0]), 1.0)
        rank = int(np.sum(singular_values > threshold))
        return vh[rank:].T.copy(), singular_values

    @staticmethod
    def _arch_of_function(
        function: np.ndarray, step: float
    ) -> tuple[float, float]:
        """Evaluate the exact-support integral plus its analytic tail."""
        n = function.size
        correlation = fftconvolve(function[::-1], function, mode="full") * step
        lags = step * np.arange(-(n - 1), n)
        f0 = float(correlation[n - 1])
        if f0 <= 0.0:
            raise FloatingPointError(f"non-positive F(0): {f0}")

        positive = lags > 1e-12
        y = lags[positive]
        fy = correlation[positive]
        # exp(y/2) * F(y) - F(0), written this way to reduce cancellation
        # near y = 0 where the archimedean kernel has a removable singularity.
        numerator = np.expm1(y / 2.0) * fy + (fy - f0)
        integrand = numerator / np.sinh(y)
        body = float(np.trapezoid(integrand, y))
        tail = f0 * math.log(math.tanh(abs(lags[-1]) / 2.0))
        return C_ARCH * f0 + body + tail, f0

    def _orthonormal_null_functions(
        self,
    ) -> tuple[np.ndarray, np.ndarray, np.ndarray, float, float]:
        null_coefficients, singular_values = self.nullspace()
        # Orthonormalize sampled functions directly.  Diagonalizing the
        # coefficient-space Gram matrix loses precision for larger bases even
        # though the underlying functions remain well-conditioned.
        weighted_basis = self.basis.T * np.sqrt(self.mass)[:, None]
        weighted_null = weighted_basis @ null_coefficients
        orthonormal_weighted, triangular = np.linalg.qr(
            weighted_null, mode="reduced"
        )
        if np.min(np.abs(np.diag(triangular))) <= 1e-14:
            raise FloatingPointError("weighted null basis is rank deficient")
        inverse_triangular = np.linalg.solve(
            triangular, np.eye(triangular.shape[0])
        )
        coefficients = null_coefficients @ inverse_triangular
        functions = coefficients.T @ self.basis
        gram_condition = float(np.linalg.cond(triangular) ** 2)
        orth_error = float(
            np.max(np.abs(
                (functions * self.mass[None, :]) @ functions.T
                - np.eye(functions.shape[0])
            ))
        )
        return functions, singular_values, coefficients, gram_condition, orth_error

    def arch_matrix(self, functions: np.ndarray) -> np.ndarray:
        dimension = functions.shape[0]
        diagonal = np.empty(dimension)
        for i in range(dimension):
            diagonal[i] = self._arch_of_function(
                functions[i], self.step
            )[0]

        matrix = np.zeros((dimension, dimension))
        np.fill_diagonal(matrix, diagonal)
        for i in range(dimension):
            for j in range(i):
                combined = functions[i] + functions[j]
                combined_value = self._arch_of_function(
                    combined, self.step
                )[0]
                value = 0.5 * (combined_value - diagonal[i] - diagonal[j])
                matrix[i, j] = value
                matrix[j, i] = value
        return (matrix + matrix.T) / 2.0

    def solve(self) -> SpectrumResult:
        functions, singular_values, coefficients, gram_condition, orth_error = (
            self._orthonormal_null_functions()
        )
        arch_matrix = self.arch_matrix(functions)
        eigenvalues = eigh(
            (arch_matrix + arch_matrix.T) / 2.0,
            np.eye(arch_matrix.shape[0]),
            check_finite=True,
            eigvals_only=True,
        )
        moment_residual = self.laplace_matrix() @ coefficients
        return SpectrumResult(
            radius=self.radius,
            basis_size=self.basis_size,
            envelope_power=self.envelope_power,
            basis_family=self.basis_family,
            nullity=functions.shape[0],
            singular_values=singular_values,
            eigenvalues=eigenvalues,
            max_constraint_residual=float(np.max(np.abs(moment_residual))),
            gram_condition=gram_condition,
            orthonormality_error=orth_error,
        )


def print_result(result: SpectrumResult) -> None:
    eigenvalues = result.eigenvalues
    square_radius = 2.0 * result.radius
    verdict = (
        "MATRIX TOP EIGENVALUE NEGATIVE"
        if eigenvalues[-1] < -1e-7
        else "BORDERLINE"
        if eigenvalues[-1] <= 1e-7
        else "FAIL positive direction"
    )
    print(
        f"r={result.radius:.5f} square={square_radius:.5f} "
        f"{result.basis_family[:3]} K={result.basis_size:2d} "
        f"p={result.envelope_power} "
        f"null={result.nullity:2d} "
        f"eig=[{eigenvalues[0]:+.8f}, {eigenvalues[-1]:+.8f}] "
        f"condG={result.gram_condition:.2e} "
        f"resid={result.max_constraint_residual:.2e} "
        f"orth={result.orthonormality_error:.2e} {verdict}"
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--grid", type=int, default=6001)
    parser.add_argument(
        "--radii",
        type=float,
        nargs="+",
        default=(0.10, 0.15, 0.20, 0.25, 0.30, 0.33, 0.345),
    )
    parser.add_argument(
        "--basis-sizes",
        type=int,
        nargs="+",
        default=(6, 8, 10, 12, 16),
    )
    parser.add_argument(
        "--envelope-powers",
        type=int,
        nargs="+",
        default=(1,),
    )
    parser.add_argument(
        "--basis-families",
        choices=("legendre", "sine"),
        nargs="+",
        default=("legendre",),
    )
    args = parser.parse_args()

    print("Lane R prime-free archimedean spectrum scan (2026-08-18)")
    print(f"C = log(4*pi) + gamma = {C_ARCH:.12f}")
    print(f"prime-free boundary: square radius < log(2) = {LOG_TWO:.12f}")
    print()
    print(
        "radius / basis-size scan; computed eigenvalues come from "
        "floating-point moment-constrained arch compressions"
    )
    print("-" * 132)
    for basis_family in args.basis_families:
        powers = args.envelope_powers if basis_family == "legendre" else (1,)
        for envelope_power in powers:
            for radius in args.radii:
                for basis_size in args.basis_sizes:
                    result = PrimeFreeProbe(
                        radius=radius,
                        basis_size=basis_size,
                        grid_size=args.grid,
                        envelope_power=envelope_power,
                        basis_family=basis_family,
                    ).solve()
                    print_result(result)
    print("-" * 132)
    print(
        "Interpretation: a positive top eigenvalue is a sampled numerical "
        "direction. A negative top eigenvalue describes only this matrix; "
        "it is not a continuum or Lean sign theorem."
    )


if __name__ == "__main__":
    main()
