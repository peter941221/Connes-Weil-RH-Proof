"""Finite block certificate for Proof 380's self-adjoint root dilation."""

from __future__ import annotations

import argparse

import numpy as np


def range_projection(frame: np.ndarray) -> np.ndarray:
    orthonormal, triangular = np.linalg.qr(frame, mode="reduced")
    if float(np.min(np.abs(np.diag(triangular)))) <= 1e-12:
        raise ValueError("graph frame lost rank")
    return orthonormal @ orthonormal.conj().T


def canonical_midpoint(first: np.ndarray, second: np.ndarray) -> np.ndarray:
    identity = np.eye(first.shape[0], dtype=complex)
    bisector = first + second - identity
    eigenvalues, eigenvectors = np.linalg.eigh(bisector)
    if float(np.min(np.abs(eigenvalues))) <= 1e-9:
        raise ValueError("canonical midpoint lost its strict angle")
    symmetry = eigenvectors @ np.diag(np.sign(eigenvalues)) @ eigenvectors.conj().T
    return 0.5 * (identity + symmetry)


def block_diagonal(first: np.ndarray, second: np.ndarray) -> np.ndarray:
    zero_first_second = np.zeros(
        (first.shape[0], second.shape[1]), dtype=complex
    )
    zero_second_first = np.zeros(
        (second.shape[0], first.shape[1]), dtype=complex
    )
    return np.block(
        [[first, zero_first_second], [zero_second_first, second]]
    )


def relative_error(actual: complex | np.ndarray, expected: complex | np.ndarray) -> float:
    return float(
        np.linalg.norm(np.asarray(actual) - np.asarray(expected))
        / max(1.0, float(np.linalg.norm(np.asarray(expected))))
    )


def certificate(size: int, rank: int, seed: int) -> dict[str, float]:
    if not 0 < rank < size:
        raise ValueError("rank must lie strictly between zero and size")

    rng = np.random.default_rng(seed)
    identity = np.eye(size, dtype=complex)
    first = np.zeros((size, size), dtype=complex)
    first[:rank, :rank] = np.eye(rank, dtype=complex)

    graph = 0.12 * (
        rng.normal(size=(size - rank, rank))
        + 1j * rng.normal(size=(size - rank, rank))
    ) / np.sqrt(size)
    frame = np.vstack([np.eye(rank, dtype=complex), graph])
    second = range_projection(frame)
    midpoint = canonical_midpoint(first, second)
    complement = identity - midpoint
    difference = second - first
    range_corner = complement @ difference @ midpoint

    root = (
        rng.normal(size=(size, size))
        + 1j * rng.normal(size=(size, size))
    ) / np.sqrt(2.0 * size)
    detector = root.conj().T @ root

    root_00 = midpoint @ root @ midpoint
    root_01 = midpoint @ root @ complement
    root_10 = complement @ root @ midpoint
    root_11 = complement @ root @ complement
    detector_row = [root_10, root_01.conj().T]
    range_row = [
        root_11 @ range_corner,
        range_corner @ root_00.conj().T,
    ]
    paired = sum(
        np.trace(left.conj().T @ right)
        for left, right in zip(detector_row, range_row, strict=True)
    )
    response = np.trace(detector @ difference)

    zero = np.zeros_like(root)
    self_adjoint_root = np.block([[zero, root.conj().T], [root, zero]])
    midpoint_lift = block_diagonal(midpoint, midpoint)
    difference_lift = block_diagonal(difference, zero)
    identity_lift = np.eye(2 * size, dtype=complex)
    complement_lift = identity_lift - midpoint_lift
    detector_lift = self_adjoint_root @ self_adjoint_root
    detector_corner_lift = (
        complement_lift @ self_adjoint_root @ midpoint_lift
    )
    range_corner_lift = complement_lift @ (
        self_adjoint_root @ difference_lift
        + difference_lift @ self_adjoint_root
    ) @ midpoint_lift
    paired_lift = np.trace(
        detector_corner_lift.conj().T @ range_corner_lift
    )
    response_lift = np.trace(detector_lift @ difference_lift)

    commutator = root @ midpoint - midpoint @ root
    detector_row_energy = sum(
        float(np.linalg.norm(component, "fro") ** 2)
        for component in detector_row
    )
    range_row_energy = sum(
        float(np.linalg.norm(component, "fro") ** 2)
        for component in range_row
    )
    cauchy_bound = 2.0 * np.sqrt(detector_row_energy * range_row_energy)

    return {
        "midpoint off diagonal error": max(
            float(np.linalg.norm(midpoint @ difference @ midpoint)),
            float(np.linalg.norm(complement @ difference @ complement)),
            relative_error(
                difference,
                range_corner + range_corner.conj().T,
            ),
        ),
        "root row pairing error": relative_error(response, 2.0 * np.real(paired)),
        "dilation square error": relative_error(
            detector_lift,
            block_diagonal(detector, root @ root.conj().T),
        ),
        "dilation response error": relative_error(response_lift, response),
        "dilation pairing error": relative_error(
            response_lift,
            2.0 * np.real(paired_lift),
        ),
        "commutator energy error": relative_error(
            detector_row_energy,
            np.linalg.norm(commutator, "fro") ** 2,
        ),
        "Cauchy Schwarz violation": max(0.0, abs(response) - cauchy_bound),
        "detector row energy": detector_row_energy,
        "range row energy": range_row_energy,
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--size", type=int, default=30)
    parser.add_argument("--rank", type=int, default=13)
    parser.add_argument("--seed", type=int, default=380)
    parser.add_argument("--tolerance", type=float, default=3e-10)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    checks = certificate(args.size, args.rank, args.seed)
    print("Proof 380 midpoint self-adjoint root dilation certificate")
    for label, value in checks.items():
        print(f"{label.replace(' ', '_')}={value:.12e}")

    exact_labels = [
        "midpoint off diagonal error",
        "root row pairing error",
        "dilation square error",
        "dilation response error",
        "dilation pairing error",
        "commutator energy error",
        "Cauchy Schwarz violation",
    ]
    maximum_error = max(checks[label] for label in exact_labels)
    if maximum_error > args.tolerance:
        raise RuntimeError(f"root dilation certificate failed: {maximum_error:.3e}")

    print(f"maximum_exact_error={maximum_error:.12e}")
    print("positive_detector_root_split=EXACT")
    print("detector_row=ENDPOINT_MR6")
    print("common_range_root_factor=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
