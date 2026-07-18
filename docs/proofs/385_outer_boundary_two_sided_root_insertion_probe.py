"""Finite certificate for Proof 385's two-sided outer root insertion."""

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

    boundary = size // 2
    positive = interval_projection(size, boundary, size)
    negative = np.eye(size, dtype=complex) - positive
    window = interval_projection(
        size,
        boundary - radius - 1,
        boundary + radius + 1,
    )

    right = window @ root @ positive
    left = negative @ root.conj().T @ window
    crossing = negative @ detector @ positive

    right_reverse = window @ root @ negative
    left_reverse = positive @ root.conj().T @ window
    crossing_reverse = positive @ detector @ negative

    random_corner = negative @ (
        rng.normal(size=(size, size))
        + 1j * rng.normal(size=(size, size))
    ) @ positive / np.sqrt(2.0 * size)
    response = np.trace(crossing.conj().T @ random_corner)
    inserted = np.vdot(left, random_corner @ right.conj().T)

    kernel_energy = float(np.vdot(kernel, kernel).real)
    window_length = float(np.trace(window).real)
    leg_bound = window_length * kernel_energy
    right_energy = float(np.linalg.norm(right, "fro") ** 2)
    left_energy = float(np.linalg.norm(left, "fro") ** 2)
    reverse_right_energy = float(np.linalg.norm(right_reverse, "fro") ** 2)
    reverse_left_energy = float(np.linalg.norm(left_reverse, "fro") ** 2)

    nuclear_norm = float(np.sum(np.linalg.svd(crossing, compute_uv=False)))
    nuclear_bound = np.sqrt(left_energy * right_energy)
    outer_bundle = np.vstack([right, right_reverse])

    return {
        "forward factorization error": relative_error(crossing, left @ right),
        "reverse factorization error": relative_error(
            crossing_reverse,
            left_reverse @ right_reverse,
        ),
        "rectangular trace insertion error": relative_error(response, inserted),
        "forward left leg bound violation": max(0.0, left_energy - leg_bound),
        "forward right leg bound violation": max(0.0, right_energy - leg_bound),
        "reverse left leg bound violation": max(
            0.0,
            reverse_left_energy - leg_bound,
        ),
        "reverse right leg bound violation": max(
            0.0,
            reverse_right_energy - leg_bound,
        ),
        "nuclear bound violation": max(0.0, nuclear_norm - nuclear_bound),
        "outer bundle square error": relative_error(
            np.linalg.norm(outer_bundle, "fro") ** 2,
            right_energy + reverse_right_energy,
        ),
        "left root energy": left_energy,
        "right root energy": right_energy,
        "nuclear norm": nuclear_norm,
        "nuclear bound": nuclear_bound,
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--size", type=int, default=112)
    parser.add_argument("--radius", type=int, default=5)
    parser.add_argument("--seed", type=int, default=385)
    parser.add_argument("--tolerance", type=float, default=3e-10)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    checks = certificate(args.size, args.radius, args.seed)
    print("Proof 385 outer-boundary two-sided root insertion certificate")
    for label, value in checks.items():
        print(f"{label.replace(' ', '_')}={value:.12e}")

    exact_labels = [
        "forward factorization error",
        "reverse factorization error",
        "rectangular trace insertion error",
        "forward left leg bound violation",
        "forward right leg bound violation",
        "reverse left leg bound violation",
        "reverse right leg bound violation",
        "nuclear bound violation",
        "outer bundle square error",
    ]
    maximum_error = max(checks[label] for label in exact_labels)
    if maximum_error > args.tolerance:
        raise RuntimeError(f"outer root insertion failed: {maximum_error:.3e}")

    print(f"maximum_error_or_violation={maximum_error:.12e}")
    print("outer_two_sided_root_factor=EXACT")
    print("outer_trace_preserving_insertion=EXACT")
    print("complete_corrected_bracket=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
