"""Stress-test the N=21 rank-three Laplace penalty on a sine basis.

The smooth Legendre screen in proof 1031 is useful but has a basis-envelope
choice.  This probe uses an L2-orthonormal sine basis and evaluates the same
finite Gamma_R prefix by the analytic inner resolvent integral.  It compares

    P_21 - (|L(g,0)|^2 + |L(g,1/2)|^2 + |L(g,1)|^2)

on the full sampled space, and P_21 on its exact sampled three-moment
nullspace.  The result is numerical route-selection evidence only; no sampled
eigenvalue is a Lean theorem.
"""

from __future__ import annotations

import argparse
import math
from dataclasses import dataclass

import numpy as np
from numpy.polynomial.legendre import leggauss


ARCH_CONSTANT = math.log(4.0 * math.pi) + np.euler_gamma
LOG_TWO = math.log(2.0)
NODES = (0.0, 0.5, 1.0)


@dataclass(frozen=True)
class Result:
    center: float
    radius: float
    basis_size: int
    nullity: int
    constrained_max: float
    certificate_max: float
    certificate_threshold: float
    moment_residual: float
    orthonormality_error: float


class SinePrefixProbe:
    def __init__(self, center: float, radius: float, basis_size: int, quadrature: int):
        if radius <= 0.0 or 2.0 * radius >= LOG_TWO:
            raise ValueError("the convolution square must remain prime-free")
        if basis_size < 4:
            raise ValueError("at least four basis functions are required")
        nodes, weights = leggauss(quadrature)
        self.center = center
        self.radius = radius
        self.nodes = center + radius * nodes
        self.weights = radius * weights
        local = radius * nodes
        phase = math.pi * (local + radius) / (2.0 * radius)
        frequencies = np.arange(1, basis_size + 1, dtype=float)
        raw = np.sin(frequencies[:, None] * phase[None, :]).T

        weighted = raw * np.sqrt(self.weights)[:, None]
        _, triangular = np.linalg.qr(weighted, mode="reduced")
        self.transform = np.linalg.solve(triangular, np.eye(basis_size))
        self.functions = raw @ self.transform
        gram = self.functions.T @ (self.weights[:, None] * self.functions)
        self.orthonormality_error = float(np.max(np.abs(gram - np.eye(basis_size))))

        self.moments = np.stack(
            [self.functions.T @ (self.weights * np.exp(s * self.nodes)) for s in NODES]
        )

    def resolvent_matrix(self, index: int) -> np.ndarray:
        a = 2.0 * index + 0.5
        b = 2.0 * index + 1.0
        local = self.nodes - self.center
        frequencies = np.arange(1, self.functions.shape[1] + 1, dtype=float)
        omega = frequencies * math.pi / (2.0 * self.radius)
        theta = (local[:, None] + self.radius) * omega[None, :]
        denominator = a * a + omega * omega
        inner = (
            2.0 * a * np.sin(theta)
            + omega[None, :] * np.exp(-a * (local[:, None] + self.radius))
            - omega[None, :]
            * ((-1.0) ** frequencies)[None, :]
            * np.exp(-a * (self.radius - local[:, None]))
        ) / denominator[None, :]
        action = inner @ self.transform
        resolvent = self.functions.T @ (self.weights[:, None] * action)
        return (resolvent + resolvent.T) / 2.0 - (2.0 / b) * np.eye(
            self.functions.shape[1]
        )

    def prefix_matrix(self, length: int) -> np.ndarray:
        result = ARCH_CONSTANT * np.eye(self.functions.shape[1])
        for index in range(length):
            result += self.resolvent_matrix(index)
        return (result + result.T) / 2.0

    def solve(self, length: int, coefficient: float) -> Result:
        prefix = self.prefix_matrix(length)
        constrained = np.linalg.svd(self.moments, full_matrices=True)[2]
        singular_values = np.linalg.svd(self.moments, compute_uv=False)
        rank = int(np.sum(singular_values > 1e-12 * max(singular_values[0], 1.0)))
        null_basis = constrained[rank:].T
        constrained_matrix = null_basis.T @ prefix @ null_basis

        penalty = self.moments.T @ self.moments
        certificate_matrix = prefix - coefficient * penalty

        def top(value: float) -> float:
            return float(np.linalg.eigvalsh(prefix - value * penalty)[-1])

        low, high = 0.0, 1.0
        while top(high) > 0.0 and high < 1e12:
            high *= 2.0
        for _ in range(60):
            middle = (low + high) / 2.0
            if top(middle) > 0.0:
                low = middle
            else:
                high = middle

        residual = float(np.max(np.abs(self.moments @ null_basis)))
        return Result(
            center=self.center,
            radius=self.radius,
            basis_size=self.functions.shape[1],
            nullity=null_basis.shape[1],
            constrained_max=float(np.linalg.eigvalsh(constrained_matrix)[-1]),
            certificate_max=float(np.linalg.eigvalsh(certificate_matrix)[-1]),
            certificate_threshold=high,
            moment_residual=residual,
            orthonormality_error=self.orthonormality_error,
        )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--length", type=int, default=21)
    parser.add_argument("--quadrature", type=int, default=900)
    parser.add_argument("--radii", type=float, nargs="+", default=(0.30, 0.345, 0.3464))
    parser.add_argument("--centers", type=float, nargs="+", default=(0.0, 1.0, -1.0))
    parser.add_argument("--basis-sizes", type=int, nargs="+", default=(8, 16, 24, 32, 48))
    args = parser.parse_args()

    print("Lane R N=21 rank-three penalty sine screen (2026-08-19)")
    print(
        f"N={args.length} quadrature={args.quadrature} log(2)={LOG_TWO:.12f} "
        f"penalty=|L(0)|^2+|L(1/2)|^2+|L(1)|^2"
    )
    print("center radius K nullity constrained_max certificate_max lambda_star residual orth_error")
    print("-" * 112)
    for center in args.centers:
        for radius in args.radii:
            for basis_size in args.basis_sizes:
                result = SinePrefixProbe(
                    center, radius, basis_size, args.quadrature
                ).solve(args.length, 1.0)
                print(
                    f"{result.center:+6.2f} {result.radius:6.4f} {result.basis_size:2d} "
                    f"{result.nullity:7d} {result.constrained_max:+15.8f} "
                    f"{result.certificate_max:+15.8f} {result.certificate_threshold:10.7f} "
                    f"{result.moment_residual:.2e} {result.orthonormality_error:.2e}"
                )
    print("-" * 112)
    print(
        "Negative rows support the proposed certificate only on these sampled "
        "sine spaces; they do not prove the universal Lean proposition."
    )


if __name__ == "__main__":
    main()
