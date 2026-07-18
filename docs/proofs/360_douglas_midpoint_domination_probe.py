"""Finite certificate for Proof 360's Douglas domination criterion.

The script verifies factorization/majorization equivalence for matrices and a
kernel-leak obstruction.  It does not prove the route domination, Gate 3U, or
RH.
"""

from __future__ import annotations

import argparse

import numpy as np


def positive_maximum_eigenvalue(matrix: np.ndarray) -> float:
    hermitian = 0.5 * (matrix + matrix.conj().T)
    return max(0.0, float(np.max(np.linalg.eigvalsh(hermitian))))


def relative_error(actual: np.ndarray, expected: np.ndarray) -> float:
    return float(
        np.linalg.norm(actual - expected)
        / max(1.0, float(np.linalg.norm(expected)))
    )


def certificate(
    domain_size: int,
    envelope_size: int,
    target_size: int,
    rank: int,
    seed: int,
) -> dict[str, float]:
    rng = np.random.default_rng(seed)
    left = rng.normal(size=(envelope_size, rank)) + 1j * rng.normal(
        size=(envelope_size, rank)
    )
    right = rng.normal(size=(rank, domain_size)) + 1j * rng.normal(
        size=(rank, domain_size)
    )
    common = left @ right
    factor = rng.normal(size=(target_size, envelope_size)) + 1j * rng.normal(
        size=(target_size, envelope_size)
    )
    factor /= max(1.0, np.linalg.norm(factor, 2))
    detector = factor @ common

    common_covariance = common.conj().T @ common
    detector_covariance = detector.conj().T @ detector
    factor_bound_sq = float(np.linalg.norm(factor, 2) ** 2)
    majorization_violation = positive_maximum_eigenvalue(
        detector_covariance - factor_bound_sq * common_covariance
    )

    reduced_factor = detector @ np.linalg.pinv(common)
    reconstruction_error = relative_error(reduced_factor @ common, detector)

    _, singular_values, right_vectors_adjoint = np.linalg.svd(
        common, full_matrices=False
    )
    threshold = 1e-11 * max(1.0, float(np.max(singular_values)))
    support = singular_values > threshold
    domain_basis = right_vectors_adjoint.conj().T[:, support]
    whitened_detector = (
        detector
        @ domain_basis
        @ np.diag(singular_values[support] ** -1)
    )
    optimal_bound_sq = float(np.linalg.norm(whitened_detector, 2) ** 2)
    reduced_factor_norm_sq = float(np.linalg.norm(reduced_factor, 2) ** 2)

    leaking_common = np.diag([1.0, 0.0]).astype(complex)
    leaking_detector = np.diag([0.0, 1e-4]).astype(complex)
    kernel_vector = np.array([0.0, 1.0], dtype=complex)
    kernel_input_norm = float(np.linalg.norm(leaking_common @ kernel_vector))
    kernel_output_norm = float(np.linalg.norm(leaking_detector @ kernel_vector))
    leaking_reduced_factor = leaking_detector @ np.linalg.pinv(leaking_common)
    leak_factor_error = relative_error(
        leaking_reduced_factor @ leaking_common, leaking_detector
    )

    return {
        "majorization violation": majorization_violation,
        "factor reconstruction error": reconstruction_error,
        "optimal norm-square error": abs(
            reduced_factor_norm_sq - optimal_bound_sq
        ),
        "kernel input norm": kernel_input_norm,
        "kernel output norm": kernel_output_norm,
        "kernel leak factor error": leak_factor_error,
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--domain-size", type=int, default=18)
    parser.add_argument("--envelope-size", type=int, default=14)
    parser.add_argument("--target-size", type=int, default=16)
    parser.add_argument("--rank", type=int, default=9)
    parser.add_argument("--seed", type=int, default=360)
    parser.add_argument("--tolerance", type=float, default=2e-9)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    checks = certificate(
        args.domain_size,
        args.envelope_size,
        args.target_size,
        args.rank,
        args.seed,
    )
    print("Proof 360 Douglas midpoint-domination certificate")
    for label, value in checks.items():
        print(f"{label.replace(' ', '_')}={value:.12e}")
    exact_errors = [
        checks["majorization violation"],
        checks["factor reconstruction error"],
        checks["optimal norm-square error"],
        checks["kernel input norm"],
    ]
    maximum_error = max(exact_errors)
    if maximum_error > args.tolerance:
        raise RuntimeError(f"Douglas certificate failed: {maximum_error:.3e}")
    if checks["kernel output norm"] <= 1e-6:
        raise RuntimeError("kernel-leak output was not detected")
    if checks["kernel leak factor error"] <= 1e-6:
        raise RuntimeError("kernel-leak factorization incorrectly succeeded")
    print(f"maximum_exact_error={maximum_error:.12e}")
    print("douglas_majorization=PASS")
    print("reduced_factor_reconstruction=PASS")
    print("kernel_leak_guard=PASS")
    print("route_domination=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
