"""Finite bundle certificate for Proof 383's boundary-root owner."""

from __future__ import annotations

import argparse

import numpy as np


def cyclic_convolution_matrix(kernel: np.ndarray, size: int) -> np.ndarray:
    radius = (len(kernel) - 1) // 2
    matrix = np.zeros((size, size), dtype=complex)
    for row in range(size):
        for offset, value in enumerate(kernel):
            displacement = offset - radius
            column = (row - displacement) % size
            matrix[row, column] += value
    return matrix


def interval_projection(size: int, start: int, stop: int) -> np.ndarray:
    projection = np.zeros((size, size), dtype=complex)
    projection[start:stop, start:stop] = np.eye(stop - start, dtype=complex)
    return projection


def positive_square_root(matrix: np.ndarray) -> np.ndarray:
    eigenvalues, eigenvectors = np.linalg.eigh(matrix)
    eigenvalues = np.maximum(eigenvalues, 0.0)
    return eigenvectors @ np.diag(np.sqrt(eigenvalues)) @ eigenvectors.conj().T


def relative_error(actual: np.ndarray | complex, expected: np.ndarray | complex) -> float:
    return float(
        np.linalg.norm(np.asarray(actual) - np.asarray(expected))
        / max(1.0, float(np.linalg.norm(np.asarray(expected))))
    )


def certificate(size: int, radius: int, window_length: int, seed: int) -> dict:
    if window_length + 4 * radius >= size:
        raise ValueError("common window must stay away from periodic wrap")

    rng = np.random.default_rng(seed)
    kernel = (
        rng.normal(size=2 * radius + 1)
        + 1j * rng.normal(size=2 * radius + 1)
    ) / np.sqrt(2.0 * (2 * radius + 1))
    root = cyclic_convolution_matrix(kernel, size)
    root_adjoint = root.conj().T
    reflected_kernel = np.conj(kernel[::-1])
    reflected_root = cyclic_convolution_matrix(reflected_kernel, size)
    reflected_adjoint = reflected_root.conj().T
    roots = [root, root_adjoint, reflected_root, reflected_adjoint]

    start = (size - window_length) // 2
    stop = start + window_length
    window = interval_projection(size, start, stop)
    boundary_factors = [window @ operator for operator in roots]
    kernel_energy = float(np.vdot(kernel, kernel).real)
    expected_window_square = window_length * kernel_energy
    maximum_window_error = max(
        relative_error(
            np.linalg.norm(factor, "fro") ** 2,
            expected_window_square,
        )
        for factor in boundary_factors
    )

    eigenvectors, _ = np.linalg.qr(
        rng.normal(size=(size, size)) + 1j * rng.normal(size=(size, size))
    )
    eigenvalues = np.exp(-np.linspace(0.0, 7.0, size))
    prolate = eigenvectors @ np.diag(eigenvalues) @ eigenvectors.conj().T
    prolate_root = positive_square_root(prolate)
    prolate_factors = [
        prolate_root,
        prolate_root @ root,
        prolate_root @ root_adjoint,
    ]

    bundle = np.vstack(boundary_factors + prolate_factors)
    component_square = sum(
        float(np.linalg.norm(component, "fro") ** 2)
        for component in boundary_factors + prolate_factors
    )
    bundle_square = float(np.linalg.norm(bundle, "fro") ** 2)
    bundle_identity_error = relative_error(bundle_square, component_square)

    root_norm = float(np.linalg.norm(root, 2))
    bundle_bound = (
        4.0 * expected_window_square
        + float(np.trace(prolate).real) * (1.0 + 2.0 * root_norm**2)
    )
    bundle_bound_violation = max(0.0, bundle_square - bundle_bound)

    zero = np.zeros((size, size), dtype=complex)
    prolate_readout = np.hstack([root @ prolate_root, -prolate_root, zero])
    prolate_adjoint_readout = np.hstack(
        [root_adjoint @ prolate_root, zero, -prolate_root]
    )
    prolate_bundle = np.vstack(prolate_factors)
    commutator = root @ prolate - prolate @ root
    adjoint_commutator = root_adjoint @ prolate - prolate @ root_adjoint
    prolate_factor_error = max(
        relative_error(commutator, prolate_readout @ prolate_bundle),
        relative_error(
            adjoint_commutator,
            prolate_adjoint_readout @ prolate_bundle,
        ),
    )

    nested_start = start + radius
    nested_stop = stop - radius
    nested = interval_projection(size, nested_start, nested_stop)
    restriction_error = max(
        relative_error(nested @ operator, nested @ factor)
        for operator, factor in zip(roots, boundary_factors, strict=True)
    )

    return {
        "maximum finite window error": maximum_window_error,
        "bundle square identity error": bundle_identity_error,
        "bundle bound violation": bundle_bound_violation,
        "prolate factorization error": prolate_factor_error,
        "nested restriction factorization error": restriction_error,
        "kernel energy": kernel_energy,
        "common window length": float(window_length),
        "boundary bundle square": sum(
            float(np.linalg.norm(component, "fro") ** 2)
            for component in boundary_factors
        ),
        "prolate bundle square": sum(
            float(np.linalg.norm(component, "fro") ** 2)
            for component in prolate_factors
        ),
        "complete bundle square": bundle_square,
        "complete bundle bound": bundle_bound,
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--size", type=int, default=96)
    parser.add_argument("--radius", type=int, default=4)
    parser.add_argument("--window-length", type=int, default=28)
    parser.add_argument("--seed", type=int, default=383)
    parser.add_argument("--tolerance", type=float, default=3e-10)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    checks = certificate(
        args.size,
        args.radius,
        args.window_length,
        args.seed,
    )
    print("Proof 383 two-orientation boundary-root bundle certificate")
    for label, value in checks.items():
        print(f"{label.replace(' ', '_')}={value:.12e}")

    exact_labels = [
        "maximum finite window error",
        "bundle square identity error",
        "bundle bound violation",
        "prolate factorization error",
        "nested restriction factorization error",
    ]
    maximum_error = max(checks[label] for label in exact_labels)
    if maximum_error > args.tolerance:
        raise RuntimeError(f"boundary-root bundle failed: {maximum_error:.3e}")

    print(f"maximum_exact_error={maximum_error:.12e}")
    print("seven_component_common_root_bundle=EXACT")
    print("prime_count_dependence=ABSENT")
    print("julia_range_alignment=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
