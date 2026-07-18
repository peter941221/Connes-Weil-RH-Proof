"""Finite certificate for Proof 387's complete corrected insertion."""

from __future__ import annotations

import argparse
from collections.abc import Sequence

import numpy as np


def projection_from_columns(columns: np.ndarray) -> np.ndarray:
    return columns @ columns.conj().T


def positive_inverse_square_root(matrix: np.ndarray) -> np.ndarray:
    eigenvalues, eigenvectors = np.linalg.eigh(matrix)
    if float(np.min(eigenvalues)) <= 1e-12:
        raise ValueError("matrix is not strictly positive")
    return eigenvectors @ np.diag(eigenvalues**-0.5) @ eigenvectors.conj().T


def positive_square_root(matrix: np.ndarray) -> np.ndarray:
    eigenvalues, eigenvectors = np.linalg.eigh(matrix)
    eigenvalues = np.maximum(eigenvalues, 0.0)
    return eigenvectors @ np.diag(np.sqrt(eigenvalues)) @ eigenvectors.conj().T


def svd_factor(matrix: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    left, singular_values, right = np.linalg.svd(matrix, full_matrices=False)
    root_values = np.sqrt(singular_values)
    return left @ np.diag(root_values), np.diag(root_values) @ right


def commutator(left: np.ndarray, right: np.ndarray) -> np.ndarray:
    return left @ right - right @ left


def relative_error(actual: np.ndarray | complex, expected: np.ndarray | complex) -> float:
    return float(
        np.linalg.norm(np.asarray(actual) - np.asarray(expected))
        / max(1.0, float(np.linalg.norm(np.asarray(expected))))
    )


def two_support_geometry(
    size: int,
    intersection_rank: int,
    quotient_rank: int,
) -> tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray, np.ndarray]:
    if intersection_rank + 2 * quotient_rank > size:
        raise ValueError("ambient carrier is too small for two-support blocks")

    identity = np.eye(size, dtype=complex)
    e_columns = np.hstack(
        [
            identity[:, :intersection_rank],
            identity[
                :,
                intersection_rank : intersection_rank + quotient_rank,
            ],
        ]
    )
    e_projection = projection_from_columns(e_columns)
    r_columns = identity[:, :intersection_rank]
    r_projection = projection_from_columns(r_columns)

    q_columns = [identity[:, index] for index in range(intersection_rank)]
    angles = np.linspace(0.31, 0.87, quotient_rank)
    for offset, angle in enumerate(angles):
        inside_index = intersection_rank + offset
        outside_index = intersection_rank + quotient_rank + offset
        q_columns.append(
            np.cos(angle) * identity[:, inside_index]
            + np.sin(angle) * identity[:, outside_index]
        )
    q_projection = projection_from_columns(np.column_stack(q_columns))
    prolate = e_projection @ q_projection @ e_projection - r_projection
    quotient_columns = e_columns[:, intersection_rank:]
    return e_projection, q_projection, r_projection, prolate, quotient_columns


def direct_sum_factor(
    entries: Sequence[
        tuple[float, np.ndarray, np.ndarray, np.ndarray, np.ndarray]
    ],
) -> tuple[np.ndarray, np.ndarray]:
    left_components = []
    right_components = []
    for sign, left_dressing, atom_left, atom_right, right_dressing in entries:
        left_components.append(sign * left_dressing @ atom_left)
        right_components.append(atom_right @ right_dressing)
    return np.hstack(left_components), np.vstack(right_components)


def certificate(size: int, seed: int) -> dict[str, float]:
    rng = np.random.default_rng(seed)
    identity = np.eye(size, dtype=complex)
    e_projection, q_projection, r_projection, prolate, quotient_columns = (
        two_support_geometry(size, intersection_rank=3, quotient_rank=5)
    )

    unitary, _ = np.linalg.qr(
        rng.normal(size=(size, size)) + 1j * rng.normal(size=(size, size))
    )
    root_values = 0.4 + rng.random(size)
    phase_values = np.exp(1j * rng.uniform(-0.8, 0.8, size))
    root = unitary @ np.diag(root_values * phase_values) @ unitary.conj().T
    detector = root.conj().T @ root
    prefix_values = 0.35 + 0.6 * rng.random(size)
    ambient_prefix = unitary @ np.diag(prefix_values) @ unitary.conj().T

    compressed_detector = e_projection @ detector @ e_projection
    quotient_prefix = e_projection @ ambient_prefix @ e_projection
    fixed_commutator = commutator(compressed_detector, r_projection)
    quotient_correction = commutator(compressed_detector, quotient_prefix)
    corrected_bracket = (
        -quotient_prefix @ fixed_commutator + quotient_correction
    )

    physical_fixed = (
        e_projection @ commutator(detector, e_projection) @ q_projection @ e_projection
        + e_projection @ commutator(detector, q_projection) @ e_projection
        + e_projection @ q_projection @ commutator(detector, e_projection) @ e_projection
        - e_projection @ commutator(detector, prolate) @ e_projection
    )
    physical_correction = (
        e_projection
        @ commutator(detector, e_projection)
        @ ambient_prefix
        @ e_projection
        + e_projection
        @ ambient_prefix
        @ commutator(detector, e_projection)
        @ e_projection
    )
    physical_bracket = -quotient_prefix @ physical_fixed + physical_correction

    e_complement = identity - e_projection
    q_complement = identity - q_projection
    d_e_plus = e_complement @ detector @ e_projection
    d_e_minus = e_projection @ detector @ e_complement
    d_q_plus = q_complement @ detector @ q_projection
    d_q_minus = q_projection @ detector @ q_complement
    d_k = commutator(detector, prolate)

    e_plus_factor = svd_factor(d_e_plus)
    e_minus_factor = svd_factor(d_e_minus)
    q_plus_factor = svd_factor(d_q_plus)
    q_minus_factor = svd_factor(d_q_minus)

    prolate_root = positive_square_root(prolate)
    k_left = np.hstack(
        [detector @ prolate_root, -prolate_root]
    )
    k_right = np.vstack(
        [prolate_root, prolate_root @ detector]
    )

    entries = [
        (-1.0, quotient_prefix @ e_projection, *e_plus_factor, q_projection @ e_projection),
        (+1.0, quotient_prefix @ e_projection, *e_minus_factor, q_projection @ e_projection),
        (-1.0, quotient_prefix @ e_projection, *q_plus_factor, e_projection),
        (+1.0, quotient_prefix @ e_projection, *q_minus_factor, e_projection),
        (-1.0, quotient_prefix @ e_projection @ q_projection, *e_plus_factor, e_projection),
        (+1.0, quotient_prefix @ e_projection @ q_projection, *e_minus_factor, e_projection),
        (+1.0, quotient_prefix @ e_projection, k_left, k_right, e_projection),
        (+1.0, e_projection, *e_plus_factor, ambient_prefix @ e_projection),
        (-1.0, e_projection, *e_minus_factor, ambient_prefix @ e_projection),
        (+1.0, e_projection @ ambient_prefix, *e_plus_factor, e_projection),
        (-1.0, e_projection @ ambient_prefix, *e_minus_factor, e_projection),
    ]
    signed_left, signed_right = direct_sum_factor(entries)

    gram = quotient_columns.conj().T @ quotient_prefix.conj().T @ quotient_prefix @ quotient_columns
    gram_inverse_root = positive_inverse_square_root(gram)
    moving_frame = quotient_prefix @ quotient_columns @ gram_inverse_root
    moving_projection = projection_from_columns(moving_frame)
    moving_crossing = (
        (e_projection - moving_projection)
        @ corrected_bracket
        @ quotient_columns
        @ gram_inverse_root
    )
    moving_left = (e_projection - moving_projection) @ signed_left
    moving_right = signed_right @ quotient_columns @ gram_inverse_root

    random_corner = (e_projection - moving_projection) @ (
        rng.normal(size=(size, quotient_columns.shape[1]))
        + 1j * rng.normal(size=(size, quotient_columns.shape[1]))
    ) / np.sqrt(2.0 * size)
    response = np.vdot(moving_crossing, random_corner)
    inserted = np.vdot(
        moving_left,
        random_corner @ moving_right.conj().T,
    )

    old_crossing = (
        (e_projection - moving_projection)
        @ compressed_detector
        @ moving_frame
    )

    return {
        "ambient commutator error": relative_error(
            commutator(detector, ambient_prefix),
            np.zeros((size, size), dtype=complex),
        ),
        "fixed physical expansion error": relative_error(
            fixed_commutator,
            physical_fixed,
        ),
        "quotient correction expansion error": relative_error(
            quotient_correction,
            physical_correction,
        ),
        "corrected physical bracket error": relative_error(
            corrected_bracket,
            physical_bracket,
        ),
        "prolate two-sided factor error": relative_error(
            d_k,
            k_left @ k_right,
        ),
        "eleven term direct sum error": relative_error(
            corrected_bracket,
            signed_left @ signed_right,
        ),
        "moving crossing factor error": relative_error(
            moving_crossing,
            moving_left @ moving_right,
        ),
        "moving detector readback error": relative_error(
            moving_crossing,
            old_crossing,
        ),
        "rectangular insertion error": relative_error(response, inserted),
        "moving frame isometry error": relative_error(
            moving_frame.conj().T @ moving_frame,
            np.eye(quotient_columns.shape[1], dtype=complex),
        ),
        "quotient correction norm": float(np.linalg.norm(quotient_correction, "fro")),
        "gram inverse root norm": float(np.linalg.norm(gram_inverse_root, 2)),
        "signed left energy": float(np.linalg.norm(signed_left, "fro") ** 2),
        "moving right energy": float(np.linalg.norm(moving_right, "fro") ** 2),
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--size", type=int, default=18)
    parser.add_argument("--seed", type=int, default=387)
    parser.add_argument("--tolerance", type=float, default=5e-10)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    checks = certificate(args.size, args.seed)
    print("Proof 387 corrected-bracket two-sided insertion certificate")
    for label, value in checks.items():
        print(f"{label.replace(' ', '_')}={value:.12e}")

    exact_labels = [
        "ambient commutator error",
        "fixed physical expansion error",
        "quotient correction expansion error",
        "corrected physical bracket error",
        "prolate two-sided factor error",
        "eleven term direct sum error",
        "moving crossing factor error",
        "moving detector readback error",
        "rectangular insertion error",
        "moving frame isometry error",
    ]
    maximum_error = max(checks[label] for label in exact_labels)
    if maximum_error > args.tolerance:
        raise RuntimeError(f"corrected insertion failed: {maximum_error:.3e}")

    if checks["quotient correction norm"] <= 1e-6:
        raise RuntimeError("quotient correction is accidentally trivial")
    if abs(checks["gram inverse root norm"] - 1.0) <= 1e-3:
        raise RuntimeError("Gram normalization is accidentally trivial")

    print(f"maximum_exact_error={maximum_error:.12e}")
    print("complete_corrected_bracket_recombination=EXACT")
    print("fixed_prefix_trace_insertion=EXACT")
    print("fixed_julia_source_owner=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
