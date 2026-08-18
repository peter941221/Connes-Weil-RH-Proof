"""Screen individual Gamma_R paired-profile summands.

The total archimedean quadratic form in 1020 is negative on the tested
three-moment subspace.  This probe asks the stronger, tempting question
whether each paired-profile summand is already nonpositive.  It evaluates the
kernel action analytically in the inner variable and uses Gauss-Legendre
quadrature only for the smooth outer integral, avoiding both cusp quadrature
error and small-difference cancellation in a lag-grid convolution at large n.

The expected outcome is a diagnostic rejection: sufficiently large profile
indices can have a positive direction even after the three Laplace constraints.
"""

from __future__ import annotations

import argparse
import math

import numpy as np
from numpy.polynomial.legendre import leggauss


VANISH_S = (0.0, 0.5, 1.0)
LOG_TWO = math.log(2.0)


class ProfileProbe:
    """L2-orthonormal sine basis restricted to the three moment nullspace."""

    def __init__(
        self,
        radius: float,
        basis_size: int,
        quadrature_size: int,
    ) -> None:
        if radius <= 0.0 or 2.0 * radius >= LOG_TWO:
            raise ValueError("the requested square must be prime-free")
        if basis_size < 4:
            raise ValueError("at least four basis functions are required")
        if quadrature_size < 32:
            raise ValueError("quadrature_size is too small")

        nodes, weights = leggauss(quadrature_size)
        self.radius = radius
        self.nodes = radius * nodes
        self.weights = radius * weights
        phase = math.pi * (nodes + 1.0) / 2.0
        frequencies = np.arange(1, basis_size + 1)[:, None]
        basis = np.sin(frequencies * phase[None, :]).T

        moments = np.stack(
            [basis.T @ (self.weights * np.exp(s * self.nodes)) for s in VANISH_S]
        )
        _, singular_values, vh = np.linalg.svd(moments, full_matrices=True)
        rank = int(np.sum(singular_values > 1e-12 * singular_values[0]))
        null_coefficients = vh[rank:].T

        weighted_basis = basis * np.sqrt(self.weights)[:, None]
        weighted_null = weighted_basis @ null_coefficients
        _, triangular = np.linalg.qr(weighted_null, mode="reduced")
        coefficients = null_coefficients @ np.linalg.solve(
            triangular, np.eye(triangular.shape[0])
        )
        self.coefficients = coefficients
        self.functions = (basis @ coefficients).T
        self.moment_residual = float(
            np.max(np.abs(moments @ coefficients))
        )
        gram = (self.functions * self.weights[None, :]) @ self.functions.T
        self.orthonormality_error = float(
            np.max(np.abs(gram - np.eye(gram.shape[0])))
        )

    def profile_matrix(self, n: int) -> np.ndarray:
        """Return the n-th real paired-profile quadratic form."""
        if n < 0:
            raise ValueError("profile index must be nonnegative")
        a = 2.0 * n + 0.5
        b = 2.0 * n + 1.0
        # For basis_k(x) = sin(omega_k * (x + radius)), integrate the inner
        # variable exactly.  This removes the derivative cusp of abs(x-y)
        # before the remaining smooth outer Gauss rule is applied.
        base_count = self.coefficients.shape[0]
        inner_action = np.empty((self.nodes.size, base_count))
        for index in range(base_count):
            k = index + 1
            omega = k * math.pi / (2.0 * self.radius)
            theta = omega * (self.nodes + self.radius)
            denominator = a * a + omega * omega
            inner_action[:, index] = (
                2.0 * a * np.sin(theta)
                + omega * np.exp(-a * (self.nodes + self.radius))
                - omega * ((-1.0) ** k)
                * np.exp(-a * (self.radius - self.nodes))
            ) / denominator
        action = inner_action @ self.coefficients
        gram = (self.functions * self.weights[None, :]) @ self.functions.T
        resolvent = self.functions @ (self.weights[:, None] * action)
        return (resolvent - (2.0 / b) * gram +
                (resolvent - (2.0 / b) * gram).T) / 2.0

    def eigenvalues(self, n: int) -> np.ndarray:
        return np.linalg.eigvalsh(self.profile_matrix(n))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--radius", type=float, default=0.345)
    parser.add_argument("--basis-size", type=int, default=16)
    parser.add_argument("--quadrature-size", type=int, default=1200)
    parser.add_argument(
        "--indices",
        type=int,
        nargs="+",
        default=(0, 1, 2, 5, 10, 20, 40, 80, 120, 200, 400),
    )
    args = parser.parse_args()

    probe = ProfileProbe(
        radius=args.radius,
        basis_size=args.basis_size,
        quadrature_size=args.quadrature_size,
    )
    print("Lane R Gamma_R paired-profile term screen (2026-08-18)")
    print(
        f"radius={args.radius:.6f} square_radius={2 * args.radius:.6f} "
        f"log(2)={LOG_TWO:.12f} basis={args.basis_size} "
        f"quadrature={args.quadrature_size} nullity={probe.functions.shape[0]}"
    )
    print(
        f"constraint_residual={probe.moment_residual:.3e} "
        f"orthonormality_error={probe.orthonormality_error:.3e}"
    )
    print("index       lambda_min          lambda_max       verdict")
    print("-" * 68)
    for n in args.indices:
        eigenvalues = probe.eigenvalues(n)
        verdict = "POSITIVE DIRECTION" if eigenvalues[-1] > 0.0 else "nonpositive"
        print(
            f"{n:5d} {eigenvalues[0]:+18.10e} {eigenvalues[-1]:+18.10e}"
            f"   {verdict}"
        )
    print("-" * 68)
    print(
        "A positive individual term does not contradict the negative total "
        "archimedean form; it rules out a termwise-sign proof."
    )


if __name__ == "__main__":
    main()
