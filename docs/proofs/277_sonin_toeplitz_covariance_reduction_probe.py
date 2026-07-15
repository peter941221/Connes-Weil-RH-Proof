#!/usr/bin/env python3
"""Certificate for Proof 277's Toeplitz covariance reduction."""

from __future__ import annotations

import argparse

import numpy as np


def random_isometry(
    ambient_size: int, rank: int, rng: np.random.Generator
) -> np.ndarray:
    matrix = rng.normal(size=(ambient_size, rank)) + 1j * rng.normal(
        size=(ambient_size, rank)
    )
    basis, _ = np.linalg.qr(matrix, mode="reduced")
    return basis


def covariance_identities(
    ambient_size: int, rank: int, seed: int
) -> dict[str, float]:
    rng = np.random.default_rng(seed)
    basis = random_isometry(ambient_size, rank, rng)
    projection = basis @ basis.conj().T
    identity = np.eye(ambient_size, dtype=complex)
    first_values = rng.normal(size=ambient_size)
    second_values = rng.normal(size=ambient_size)
    first = np.diag(first_values.astype(complex))
    second = np.diag(second_values.astype(complex))

    first_commutator = first @ projection - projection @ first
    second_commutator = second @ projection - projection @ second
    dirichlet = np.trace(
        first_commutator.conj().T @ second_commutator
    )

    toeplitz_first = basis.conj().T @ first @ basis
    toeplitz_second = basis.conj().T @ second @ basis
    toeplitz_product = basis.conj().T @ first @ second @ basis
    semicommutator = 2.0 * np.trace(
        toeplitz_product - toeplitz_first @ toeplitz_second
    )
    crossing = 2.0 * np.trace(
        projection
        @ first
        @ (identity - projection)
        @ second
        @ projection
    )

    return {
        "Dirichlet versus Toeplitz error": float(
            abs(dirichlet - semicommutator)
        ),
        "Dirichlet versus crossing error": float(abs(dirichlet - crossing)),
        "commuting multiplier error": float(
            np.linalg.norm(first @ second - second @ first, ord=2)
        ),
        "projection idempotence error": float(
            np.linalg.norm(projection @ projection - projection, ord=2)
        ),
        "Dirichlet magnitude": float(abs(dirichlet)),
    }


def static_ownership_guard() -> dict[str, float]:
    vector = np.ones((3, 1), dtype=complex) / np.sqrt(3.0)
    projection = vector @ vector.conj().T
    first = np.diag(np.array([1.0, 1.0, 2.0], dtype=complex))
    second = np.diag(np.array([1.0, 1.0, -1.0], dtype=complex))

    toeplitz_first = vector.conj().T @ first @ vector
    toeplitz_second = vector.conj().T @ second @ vector
    static_product = vector.conj().T @ first @ second @ vector
    covariance = 2.0 * (
        static_product - toeplitz_first @ toeplitz_second
    )

    first_commutator = first @ projection - projection @ first
    second_commutator = second @ projection - projection @ second
    dirichlet = np.trace(
        first_commutator.conj().T @ second_commutator
    )
    return {
        "minimum detector eigenvalue": float(
            np.min(np.linalg.eigvalsh(first)).real
        ),
        "static product trace magnitude": float(abs(static_product.item())),
        "compressed product trace magnitude": float(
            abs((toeplitz_first @ toeplitz_second).item())
        ),
        "Toeplitz covariance magnitude": float(abs(covariance.item())),
        "guard identity error": float(abs(dirichlet - covariance.item())),
    }


def print_checks(title: str, checks: dict[str, float]) -> None:
    print(title)
    print("+--------------------------------------------+----------------+")
    print("| check                                      | value          |")
    print("+--------------------------------------------+----------------+")
    for label, value in checks.items():
        print(f"| {label:<42} | {value:>14.6e} |")
    print("+--------------------------------------------+----------------+")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--ambient-size", type=int, default=18)
    parser.add_argument("--rank", type=int, default=7)
    parser.add_argument("--seed", type=int, default=1277)
    parser.add_argument("--tolerance", type=float, default=2e-13)
    args = parser.parse_args()

    if not 1 <= args.rank < args.ambient_size:
        raise ValueError("rank must be strictly between zero and ambient size")

    identities = covariance_identities(
        args.ambient_size, args.rank, args.seed
    )
    guard = static_ownership_guard()

    print("identity=Sonin Toeplitz covariance reduction")
    print("status=exact semicommutator identity; compressed tail open")
    print_checks("Toeplitz covariance identities", identities)
    print()
    print_checks("Static-remainder ownership guard", guard)

    maximum_error = max(
        identities["Dirichlet versus Toeplitz error"],
        identities["Dirichlet versus crossing error"],
        identities["commuting multiplier error"],
        identities["projection idempotence error"],
        guard["static product trace magnitude"],
        guard["guard identity error"],
    )
    print(f"maximum exact-certificate error={maximum_error:.12e}")
    if maximum_error > args.tolerance:
        raise SystemExit(f"Toeplitz certificate failed: {maximum_error:.6e}")
    if guard["minimum detector eigenvalue"] <= 0.0:
        raise SystemExit("guard detector is not strictly positive")
    if guard["Toeplitz covariance magnitude"] < 0.5:
        raise SystemExit("static ownership guard lost its covariance")

    print("dirichlet_toeplitz_semicommutator_identity=EXACT")
    print("completed_crossing_identity=EXACT")
    print("static_trace_controls_covariance=REJECTED_BY_THREE_POINT_GUARD")
    print("cc20_static_displacement_exponent=FIXED_SUPPORT_ONLY_PROOF_276")
    print("polynomial_support_width_cost=OPEN")
    print("compressed_toeplitz_half_power_term=OPEN")
    print("relative_jacobi_resummation=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
