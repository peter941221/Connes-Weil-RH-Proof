"""Finite certificate for Proof 375's nearly-invariant Euler transport.

The script checks a disk-polynomial analogue of the exact range argument.  It
does not prove Burnol's de Branges theorem, Gate 3U, or RH.
"""

from __future__ import annotations

import argparse
import math

import numpy as np


def euler_factor(prime: int, delay: int) -> np.ndarray:
    factor = np.zeros(delay + 1, dtype=complex)
    factor[0] = 1.0
    factor[delay] = -(prime**-0.5)
    return factor


def multiplier_frame(
    multiplier: np.ndarray,
    model_dimension: int,
    ambient_size: int,
) -> np.ndarray:
    required = len(multiplier) + model_dimension - 1
    if required > ambient_size:
        raise ValueError("ambient coefficient space is too small")
    frame = np.zeros((ambient_size, model_dimension), dtype=complex)
    for column in range(model_dimension):
        frame[column : column + len(multiplier), column] = multiplier
    return frame


def range_projection(frame: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    orthonormal, triangular = np.linalg.qr(frame, mode="reduced")
    if float(np.min(np.abs(np.diag(triangular)))) <= 1e-12:
        raise ValueError("transported frame lost rank")
    return orthonormal @ orthonormal.conj().T, orthonormal


def backward_shift(vectors: np.ndarray) -> np.ndarray:
    shifted = np.zeros_like(vectors)
    shifted[:-1] = vectors[1:]
    return shifted


def near_invariance_residual(orthonormal: np.ndarray) -> float:
    evaluation = orthonormal[0:1]
    _, singular_values, right = np.linalg.svd(evaluation, full_matrices=True)
    rank = int(np.sum(singular_values > 1e-12))
    vanishing_coordinates = right.conj().T[:, rank:]
    vanishing_vectors = orthonormal @ vanishing_coordinates
    shifted = backward_shift(vanishing_vectors)
    residual = shifted - orthonormal @ (orthonormal.conj().T @ shifted)
    return float(np.linalg.norm(residual))


def certificate(
    ambient_size: int,
    model_dimension: int,
    mesh: float,
) -> dict[str, float]:
    primes = [2, 3, 5, 7, 11, 13, 17]
    multiplier = np.array([1.0 + 0.0j])
    maximum_near_residual = 0.0
    maximum_normalization_error = 0.0
    minimum_boundary_gap = math.inf

    angles = np.linspace(0.0, 2.0 * math.pi, 4096, endpoint=False)
    for prime in primes:
        delay = max(1, round(math.log(prime) / mesh))
        factor = euler_factor(prime, delay)
        multiplier = np.convolve(multiplier, factor)
        frame = multiplier_frame(multiplier, model_dimension, ambient_size)
        projection, orthonormal = range_projection(frame)
        maximum_near_residual = max(
            maximum_near_residual,
            near_invariance_residual(orthonormal),
        )

        scalar = np.prod([1.0 - q**-0.5 for q in primes if q <= prime])
        normalized_projection, _ = range_projection(scalar * frame)
        maximum_normalization_error = max(
            maximum_normalization_error,
            float(np.linalg.norm(projection - normalized_projection)),
        )

        boundary = np.polynomial.polynomial.polyval(np.exp(1j * angles), factor)
        minimum_boundary_gap = min(
            minimum_boundary_gap,
            float(np.min(np.abs(boundary))),
        )

    return {
        "near invariance residual": maximum_near_residual,
        "scalar normalization projection error": maximum_normalization_error,
        "minimum Euler boundary gap": minimum_boundary_gap,
        "final multiplier degree": float(len(multiplier) - 1),
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--ambient-size", type=int, default=160)
    parser.add_argument("--model-dimension", type=int, default=11)
    parser.add_argument("--mesh", type=float, default=0.35)
    parser.add_argument("--tolerance", type=float, default=2e-10)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    checks = certificate(args.ambient_size, args.model_dimension, args.mesh)
    print("Proof 375 Sonin nearly-invariant transport certificate")
    for label, value in checks.items():
        print(f"{label.replace(' ', '_')}={value:.12e}")

    exact_error = max(
        checks["near invariance residual"],
        checks["scalar normalization projection error"],
    )
    if exact_error > args.tolerance:
        raise RuntimeError(f"nearly-invariant transport failed: {exact_error:.3e}")
    if checks["minimum Euler boundary gap"] <= 0.0:
        raise RuntimeError("Euler multiplier was not invertible on the boundary")

    print(f"maximum_exact_error={exact_error:.12e}")
    print("causal_euler_range_transport=PASS")
    print("nearly_invariant_endpoint=PASS")
    print("explicit_semilocal_hb_generator=NOT_USED")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
