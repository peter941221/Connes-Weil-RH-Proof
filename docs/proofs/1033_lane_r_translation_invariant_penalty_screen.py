"""Screen a translation-invariant rank-three penalty for the Lane R prefix.

The one-sided penalty ``sum |L(g,s)|^2`` is incompatible with translating a
root: the finite Gamma_R prefix is translation invariant, while the three
positive Laplace values acquire different exponential factors.  This screen
tests the repaired penalty

    |L(g,0)|^2 + |L(g,-1/2)L(g,1/2)|
                   + |L(g,-1)L(g,1)|.

For the real sine basis used here, each product is a real quadratic form on a
fixed sign sector.  The reported value is the largest value found by sector
eigenvectors, deterministic random directions, and BFGS refinement.  It is
route-selection evidence only; no sampled optimization result is a Lean
certificate.
"""

from __future__ import annotations

import argparse
import math
from dataclasses import dataclass

import numpy as np
from numpy.polynomial.legendre import leggauss
from scipy.optimize import minimize


ARCH_CONSTANT = math.log(4.0 * math.pi) + np.euler_gamma
LOG_TWO = math.log(2.0)


@dataclass(frozen=True)
class Result:
    center: float
    radius: float
    basis_size: int
    sampled_max: float
    sampled_min: float
    sector_eigen_max: float
    sampled_direction_norm: float
    moment_max: float
    orthonormality_error: float


class TranslationInvariantProbe:
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

        self.moments = {
            s: self.functions.T @ (self.weights * np.exp(s * self.nodes))
            for s in (-1.0, -0.5, 0.0, 0.5, 1.0)
        }
        self.moment_max = float(
            max(np.max(np.abs(self.moments[s])) for s in self.moments)
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

    def pair_matrix(self, radius: float) -> np.ndarray:
        negative = self.moments[-radius]
        positive = self.moments[radius]
        return (np.outer(negative, positive) + np.outer(positive, negative)) / 2.0

    def penalty_value(self, vector: np.ndarray) -> float:
        zero = float(self.moments[0.0] @ vector)
        half_negative = float(self.moments[-0.5] @ vector)
        half_positive = float(self.moments[0.5] @ vector)
        one_negative = float(self.moments[-1.0] @ vector)
        one_positive = float(self.moments[1.0] @ vector)
        return (
            zero * zero
            + abs(half_negative * half_positive)
            + abs(one_negative * one_positive)
        )

    def certificate_value(self, prefix: np.ndarray, vector: np.ndarray) -> float:
        return float(vector @ prefix @ vector) - self.penalty_value(vector)

    def solve(self, length: int, random_directions: int, seed: int) -> Result:
        prefix = self.prefix_matrix(length)
        zero_matrix = np.outer(self.moments[0.0], self.moments[0.0])
        half_matrix = self.pair_matrix(0.5)
        one_matrix = self.pair_matrix(1.0)

        # The absolute values split the search into four sign sectors.  The
        # unrestricted eigenvalues are only candidate directions; each one is
        # checked against its actual product signs before it is accepted.
        sector_eigen_max = -math.inf
        candidates: list[np.ndarray] = []
        for half_sign in (-1.0, 1.0):
            for one_sign in (-1.0, 1.0):
                matrix = prefix - zero_matrix - half_sign * half_matrix - one_sign * one_matrix
                eigenvalues, eigenvectors = np.linalg.eigh(matrix)
                sector_eigen_max = max(sector_eigen_max, float(eigenvalues[-1]))
                candidates.extend(eigenvectors[:, -min(4, eigenvectors.shape[1]) :].T)

        rng = np.random.default_rng(seed)
        for _ in range(random_directions):
            candidates.append(rng.normal(size=self.functions.shape[1]))

        normalized = []
        values = []
        for vector in candidates:
            norm = np.linalg.norm(vector)
            if norm <= 1e-14:
                continue
            vector = vector / norm
            normalized.append(vector)
            values.append(self.certificate_value(prefix, vector))

        best_index = int(np.argmax(values))
        best_vector = normalized[best_index]
        best_value = values[best_index]

        def objective(vector: np.ndarray) -> float:
            norm = np.linalg.norm(vector)
            if norm <= 1e-14:
                return 1e6
            unit = vector / norm
            return -self.certificate_value(prefix, unit)

        for vector in normalized[: min(len(normalized), 40)]:
            result = minimize(objective, vector, method="BFGS", options={"maxiter": 600})
            if result.success or np.isfinite(result.fun):
                norm = np.linalg.norm(result.x)
                if norm > 1e-14:
                    value = self.certificate_value(prefix, result.x / norm)
                    if value > best_value:
                        best_value = value
                        best_vector = result.x / norm

        return Result(
            center=self.center,
            radius=self.radius,
            basis_size=self.functions.shape[1],
            sampled_max=float(best_value),
            sampled_min=float(np.linalg.eigvalsh(prefix)[0]),
            sector_eigen_max=float(sector_eigen_max),
            sampled_direction_norm=float(np.linalg.norm(best_vector)),
            moment_max=self.moment_max,
            orthonormality_error=self.orthonormality_error,
        )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--length", type=int, default=21)
    parser.add_argument("--quadrature", type=int, default=900)
    parser.add_argument("--random-directions", type=int, default=4000)
    parser.add_argument("--seed", type=int, default=1033)
    parser.add_argument("--radii", type=float, nargs="+", default=(0.20, 0.30, 0.345, 0.3464))
    parser.add_argument("--centers", type=float, nargs="+", default=(-4.0, -2.0, -1.0, 0.0, 1.0, 2.0, 4.0))
    parser.add_argument("--basis-sizes", type=int, nargs="+", default=(8, 16, 24, 32, 48))
    args = parser.parse_args()

    print("Lane R N=21 translation-invariant penalty screen (2026-08-19)")
    print(
        f"N={args.length} quadrature={args.quadrature} log(2)={LOG_TWO:.12f} "
        "penalty=|L(0)|^2+|L(-1/2)L(1/2)|+|L(-1)L(1)|"
    )
    print("center radius K sampled_max prefix_min sector_eigen_max norm moment_max orth_error")
    print("-" * 112)
    for center in args.centers:
        for radius in args.radii:
            for basis_size in args.basis_sizes:
                result = TranslationInvariantProbe(
                    center, radius, basis_size, args.quadrature
                ).solve(args.length, args.random_directions, args.seed)
                print(
                    f"{result.center:+6.2f} {result.radius:6.4f} {result.basis_size:2d} "
                    f"{result.sampled_max:+12.8f} {result.sampled_min:+12.8f} "
                    f"{result.sector_eigen_max:+15.8f} {result.sampled_direction_norm:.2e} "
                    f"{result.moment_max:.2e} {result.orthonormality_error:.2e}"
                )
    print("-" * 112)
    print(
        "The sampled maximum is an optimization screen for the repaired "
        "absolute-value penalty, not a universal analytic certificate."
    )


if __name__ == "__main__":
    main()
