"""Finite certificate for Proof 386's reflected/prolate two-sided roots."""

from __future__ import annotations

import argparse

import numpy as np


def zero_fill_convolution(kernel: np.ndarray, size: int) -> np.ndarray:
    radius = (len(kernel) - 1) // 2
    matrix = np.zeros((size, size), dtype=complex)
    for row in range(size):
        for offset, value in enumerate(kernel):
            displacement = offset - radius
            column = row - displacement
            if 0 <= column < size:
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


def certificate(size: int, radius: int, seed: int) -> dict[str, float]:
    if size <= 8 * radius + 8:
        raise ValueError("ambient grid is too small for the boundary window")

    rng = np.random.default_rng(seed)
    kernel = (
        rng.normal(size=2 * radius + 1)
        + 1j * rng.normal(size=2 * radius + 1)
    ) / np.sqrt(2.0 * (2 * radius + 1))
    root = zero_fill_convolution(kernel, size)
    detector = root.conj().T @ root

    reflection = np.fliplr(np.eye(size, dtype=complex))
    reflected_root = reflection @ root @ reflection
    reflected_detector = reflected_root.conj().T @ reflected_root

    boundary = size // 2
    positive = interval_projection(size, boundary, size)
    negative = np.eye(size, dtype=complex) - positive
    second_support = reflection @ positive @ reflection
    window = interval_projection(
        size,
        boundary - radius - 1,
        boundary + radius + 1,
    )

    left = reflection @ negative @ reflected_root.conj().T @ window
    right = window @ reflected_root @ positive @ reflection
    crossing = (
        (np.eye(size, dtype=complex) - second_support)
        @ detector
        @ second_support
    )

    left_reverse = reflection @ positive @ reflected_root.conj().T @ window
    right_reverse = window @ reflected_root @ negative @ reflection
    crossing_reverse = (
        second_support
        @ detector
        @ (np.eye(size, dtype=complex) - second_support)
    )

    random_corner = (np.eye(size) - second_support) @ (
        rng.normal(size=(size, size))
        + 1j * rng.normal(size=(size, size))
    ) @ second_support / np.sqrt(2.0 * size)
    response = np.trace(crossing.conj().T @ random_corner)
    inserted = np.vdot(left, random_corner @ right.conj().T)

    random_corner_reverse = second_support @ (
        rng.normal(size=(size, size))
        + 1j * rng.normal(size=(size, size))
    ) @ (np.eye(size) - second_support) / np.sqrt(2.0 * size)
    response_reverse = np.trace(
        crossing_reverse.conj().T @ random_corner_reverse
    )
    inserted_reverse = np.vdot(
        left_reverse,
        random_corner_reverse @ right_reverse.conj().T,
    )

    eigenvectors, _ = np.linalg.qr(
        rng.normal(size=(size, size)) + 1j * rng.normal(size=(size, size))
    )
    eigenvalues = np.exp(-np.linspace(0.0, 8.0, size))
    prolate = eigenvectors @ np.diag(eigenvalues) @ eigenvectors.conj().T
    prolate_root = positive_square_root(prolate)
    prolate_left = np.hstack(
        [detector @ prolate_root, -prolate_root]
    )
    prolate_right = np.vstack(
        [prolate_root, prolate_root @ detector]
    )
    prolate_commutator = detector @ prolate - prolate @ detector

    random_prolate_corner = (
        rng.normal(size=(size, size))
        + 1j * rng.normal(size=(size, size))
    ) / np.sqrt(2.0 * size)
    prolate_response = np.trace(
        prolate_commutator.conj().T @ random_prolate_corner
    )
    prolate_inserted = np.vdot(
        prolate_left,
        random_prolate_corner @ prolate_right.conj().T,
    )

    kernel_energy = float(np.vdot(kernel, kernel).real)
    window_length = float(np.trace(window).real)
    reflected_leg_bound = window_length * kernel_energy
    reflected_energies = [
        float(np.linalg.norm(operator, "fro") ** 2)
        for operator in [left, right, left_reverse, right_reverse]
    ]

    detector_norm = float(np.linalg.norm(detector, 2))
    prolate_trace = float(np.trace(prolate).real)
    prolate_leg_bound = (1.0 + detector_norm**2) * prolate_trace
    prolate_left_energy = float(np.linalg.norm(prolate_left, "fro") ** 2)
    prolate_right_energy = float(np.linalg.norm(prolate_right, "fro") ** 2)

    complete_right = np.block(
        [
            [right, np.zeros((size, size), dtype=complex)],
            [right_reverse, np.zeros((size, size), dtype=complex)],
            [np.zeros((2 * size, size), dtype=complex), prolate_right],
        ]
    )
    complete_square = float(np.linalg.norm(complete_right, "fro") ** 2)
    component_square = (
        reflected_energies[1]
        + reflected_energies[3]
        + prolate_right_energy
    )

    return {
        "reflected detector readback error": relative_error(
            reflection @ detector @ reflection,
            reflected_detector,
        ),
        "forward reflected factorization error": relative_error(
            crossing,
            left @ right,
        ),
        "reverse reflected factorization error": relative_error(
            crossing_reverse,
            left_reverse @ right_reverse,
        ),
        "forward reflected insertion error": relative_error(response, inserted),
        "reverse reflected insertion error": relative_error(
            response_reverse,
            inserted_reverse,
        ),
        "reflected leg bound violation": max(
            0.0,
            max(reflected_energies) - reflected_leg_bound,
        ),
        "prolate factorization error": relative_error(
            prolate_commutator,
            prolate_left @ prolate_right,
        ),
        "prolate insertion error": relative_error(
            prolate_response,
            prolate_inserted,
        ),
        "prolate left bound violation": max(
            0.0,
            prolate_left_energy - prolate_leg_bound,
        ),
        "prolate right bound violation": max(
            0.0,
            prolate_right_energy - prolate_leg_bound,
        ),
        "complete right square error": relative_error(
            complete_square,
            component_square,
        ),
        "reflected right energy": reflected_energies[1],
        "reflected reverse right energy": reflected_energies[3],
        "prolate left energy": prolate_left_energy,
        "prolate right energy": prolate_right_energy,
        "complete right square": complete_square,
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--size", type=int, default=104)
    parser.add_argument("--radius", type=int, default=5)
    parser.add_argument("--seed", type=int, default=386)
    parser.add_argument("--tolerance", type=float, default=3e-10)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    checks = certificate(args.size, args.radius, args.seed)
    print("Proof 386 reflected/prolate two-sided root certificate")
    for label, value in checks.items():
        print(f"{label.replace(' ', '_')}={value:.12e}")

    exact_labels = [
        "reflected detector readback error",
        "forward reflected factorization error",
        "reverse reflected factorization error",
        "forward reflected insertion error",
        "reverse reflected insertion error",
        "reflected leg bound violation",
        "prolate factorization error",
        "prolate insertion error",
        "prolate left bound violation",
        "prolate right bound violation",
        "complete right square error",
    ]
    maximum_error = max(checks[label] for label in exact_labels)
    if maximum_error > args.tolerance:
        raise RuntimeError(f"reflected/prolate bundle failed: {maximum_error:.3e}")

    print(f"maximum_error_or_violation={maximum_error:.12e}")
    print("reflected_two_sided_root_insertion=EXACT")
    print("prolate_two_sided_root_insertion=EXACT")
    print("moving_julia_alignment=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
