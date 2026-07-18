"""Finite certificate for Proof 398's corrected-root bi-Schur ledger."""

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
) -> tuple[
    np.ndarray,
    np.ndarray,
    np.ndarray,
    np.ndarray,
    np.ndarray,
    np.ndarray,
]:
    if intersection_rank + 2 * quotient_rank > size:
        raise ValueError("ambient carrier is too small for two-support blocks")

    identity = np.eye(size, dtype=complex)
    carrier_columns = np.hstack(
        [
            identity[:, :intersection_rank],
            identity[
                :,
                intersection_rank : intersection_rank + quotient_rank,
            ],
        ]
    )
    outer_projection = projection_from_columns(carrier_columns)
    intersection_columns = identity[:, :intersection_rank]
    sonin_projection = projection_from_columns(intersection_columns)

    second_columns = [identity[:, index] for index in range(intersection_rank)]
    angles = np.linspace(0.29, 0.91, quotient_rank)
    for offset, angle in enumerate(angles):
        inside_index = intersection_rank + offset
        outside_index = intersection_rank + quotient_rank + offset
        second_columns.append(
            np.cos(angle) * identity[:, inside_index]
            + np.sin(angle) * identity[:, outside_index]
        )
    second_projection = projection_from_columns(np.column_stack(second_columns))
    prolate = (
        outer_projection @ second_projection @ outer_projection
        - sonin_projection
    )
    quotient_columns = carrier_columns[:, intersection_rank:]
    return (
        outer_projection,
        second_projection,
        sonin_projection,
        prolate,
        quotient_columns,
        carrier_columns,
    )


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
    (
        outer_projection,
        second_projection,
        sonin_projection,
        prolate,
        source,
        carrier_columns,
    ) = two_support_geometry(size, intersection_rank=3, quotient_rank=5)

    spectral_basis, _ = np.linalg.qr(
        rng.normal(size=(size, size)) + 1j * rng.normal(size=(size, size))
    )
    root_values = 0.4 + rng.random(size)
    root_phases = np.exp(1j * rng.uniform(-0.9, 0.9, size))
    root = (
        spectral_basis
        @ np.diag(root_values * root_phases)
        @ spectral_basis.conj().T
    )
    detector = root.conj().T @ root
    prefix_values = 0.3 + 0.65 * rng.random(size)
    ambient_prefix = (
        spectral_basis
        @ np.diag(prefix_values)
        @ spectral_basis.conj().T
    )

    compressed_detector = outer_projection @ detector @ outer_projection
    quotient_prefix = outer_projection @ ambient_prefix @ outer_projection
    fixed_commutator = commutator(compressed_detector, sonin_projection)
    quotient_correction = commutator(compressed_detector, quotient_prefix)
    corrected_bracket = (
        -quotient_prefix @ fixed_commutator + quotient_correction
    )

    physical_fixed = (
        outer_projection
        @ commutator(detector, outer_projection)
        @ second_projection
        @ outer_projection
        + outer_projection
        @ commutator(detector, second_projection)
        @ outer_projection
        + outer_projection
        @ second_projection
        @ commutator(detector, outer_projection)
        @ outer_projection
        - outer_projection
        @ commutator(detector, prolate)
        @ outer_projection
    )
    physical_correction = (
        outer_projection
        @ commutator(detector, outer_projection)
        @ ambient_prefix
        @ outer_projection
        + outer_projection
        @ ambient_prefix
        @ commutator(detector, outer_projection)
        @ outer_projection
    )
    physical_bracket = -quotient_prefix @ physical_fixed + physical_correction

    outer_complement = identity - outer_projection
    second_complement = identity - second_projection
    d_outer_plus = outer_complement @ detector @ outer_projection
    d_outer_minus = outer_projection @ detector @ outer_complement
    d_second_plus = second_complement @ detector @ second_projection
    d_second_minus = second_projection @ detector @ second_complement
    d_prolate = commutator(detector, prolate)

    outer_plus_factor = svd_factor(d_outer_plus)
    outer_minus_factor = svd_factor(d_outer_minus)
    second_plus_factor = svd_factor(d_second_plus)
    second_minus_factor = svd_factor(d_second_minus)
    prolate_root = positive_square_root(prolate)
    prolate_left = np.hstack([detector @ prolate_root, -prolate_root])
    prolate_right = np.vstack([prolate_root, prolate_root @ detector])

    entries = [
        (
            -1.0,
            quotient_prefix @ outer_projection,
            *outer_plus_factor,
            second_projection @ outer_projection,
        ),
        (
            +1.0,
            quotient_prefix @ outer_projection,
            *outer_minus_factor,
            second_projection @ outer_projection,
        ),
        (
            -1.0,
            quotient_prefix @ outer_projection,
            *second_plus_factor,
            outer_projection,
        ),
        (
            +1.0,
            quotient_prefix @ outer_projection,
            *second_minus_factor,
            outer_projection,
        ),
        (
            -1.0,
            quotient_prefix @ outer_projection @ second_projection,
            *outer_plus_factor,
            outer_projection,
        ),
        (
            +1.0,
            quotient_prefix @ outer_projection @ second_projection,
            *outer_minus_factor,
            outer_projection,
        ),
        (
            +1.0,
            quotient_prefix @ outer_projection,
            prolate_left,
            prolate_right,
            outer_projection,
        ),
        (
            +1.0,
            outer_projection,
            *outer_plus_factor,
            ambient_prefix @ outer_projection,
        ),
        (
            -1.0,
            outer_projection,
            *outer_minus_factor,
            ambient_prefix @ outer_projection,
        ),
        (
            +1.0,
            outer_projection @ ambient_prefix,
            *outer_plus_factor,
            outer_projection,
        ),
        (
            -1.0,
            outer_projection @ ambient_prefix,
            *outer_minus_factor,
            outer_projection,
        ),
    ]
    signed_left, signed_right = direct_sum_factor(entries)

    gram = (
        source.conj().T
        @ quotient_prefix.conj().T
        @ quotient_prefix
        @ source
    )
    gram_inverse_root = positive_inverse_square_root(gram)
    new_frame = quotient_prefix @ source @ gram_inverse_root
    moving_projection = projection_from_columns(new_frame)
    moving_crossing = (
        (outer_projection - moving_projection)
        @ corrected_bracket
        @ source
        @ gram_inverse_root
    )
    moving_left = (outer_projection - moving_projection) @ signed_left
    moving_right = signed_right @ source @ gram_inverse_root
    direct_crossing = (
        (outer_projection - moving_projection)
        @ compressed_detector
        @ new_frame
    )

    restricted_detector = (
        carrier_columns.conj().T
        @ compressed_detector
        @ carrier_columns
    )
    _, detector_eigenvectors = np.linalg.eigh(restricted_detector)
    phases = np.exp(1j * np.linspace(-0.8, 1.1, carrier_columns.shape[1]))
    restricted_unitary = (
        detector_eigenvectors
        @ np.diag(phases)
        @ detector_eigenvectors.conj().T
    )
    local_unitary = (
        carrier_columns @ restricted_unitary @ carrier_columns.conj().T
        + identity
        - outer_projection
    )
    coefficient = 2.0**-0.5
    denominator = identity - coefficient * local_unitary
    normalized_forward = denominator / (1.0 + coefficient)
    markov_inverse = (1.0 - coefficient) * np.linalg.inv(denominator)
    rho = (1.0 - coefficient) / (1.0 + coefficient)

    old_raw = normalized_forward @ new_frame
    old_frame, transition = np.linalg.qr(old_raw)
    reverse = rho * np.linalg.inv(transition)
    old_alpha = old_frame.conj().T @ compressed_detector @ old_frame
    new_alpha = new_frame.conj().T @ compressed_detector @ new_frame
    forward_defect = transition @ new_alpha - old_alpha @ transition
    boundary_defect = (
        -old_frame.conj().T @ normalized_forward @ direct_crossing
    )
    relative_defect = (
        transition @ new_alpha @ reverse - rho * old_alpha
    )

    local_left = (
        -old_frame.conj().T @ normalized_forward @ moving_left
    )
    local_right = moving_right @ reverse
    causal_sandwich = (
        -old_frame.conj().T
        @ normalized_forward
        @ (outer_projection - moving_projection)
        @ compressed_detector
        @ markov_inverse
        @ old_frame
    )

    scalar_crossing = (
        (outer_projection - moving_projection)
        @ (1.7 * outer_projection)
        @ new_frame
    )
    scalar_relative = (
        -old_frame.conj().T
        @ normalized_forward
        @ scalar_crossing
        @ reverse
    )

    return {
        "ambient detector prefix commutator error": relative_error(
            commutator(detector, ambient_prefix),
            np.zeros((size, size), dtype=complex),
        ),
        "corrected physical bracket error": relative_error(
            corrected_bracket,
            physical_bracket,
        ),
        "prolate root factor error": relative_error(
            d_prolate,
            prolate_left @ prolate_right,
        ),
        "eleven term ledger error": relative_error(
            corrected_bracket,
            signed_left @ signed_right,
        ),
        "moving root factor error": relative_error(
            moving_crossing,
            moving_left @ moving_right,
        ),
        "moving detector readback error": relative_error(
            moving_crossing,
            direct_crossing,
        ),
        "local detector commutator error": relative_error(
            commutator(normalized_forward, compressed_detector),
            np.zeros((size, size), dtype=complex),
        ),
        "local Schur intertwining error": relative_error(
            normalized_forward @ new_frame,
            old_frame @ transition,
        ),
        "local forward boundary error": relative_error(
            forward_defect,
            boundary_defect,
        ),
        "local scalar pair error": max(
            relative_error(
                transition @ reverse,
                rho * np.eye(source.shape[1]),
            ),
            relative_error(
                reverse @ transition,
                rho * np.eye(source.shape[1]),
            ),
        ),
        "Markov source readback error": relative_error(
            markov_inverse @ old_frame,
            new_frame @ reverse,
        ),
        "relative defect completion error": relative_error(
            relative_defect,
            forward_defect @ reverse,
        ),
        "corrected root relative factor error": relative_error(
            relative_defect,
            local_left @ local_right,
        ),
        "causal boundary sandwich error": relative_error(
            relative_defect,
            causal_sandwich,
        ),
        "scalar channel crossing norm": float(np.linalg.norm(scalar_crossing, 2)),
        "scalar channel relative norm": float(np.linalg.norm(scalar_relative, 2)),
        "quotient correction norm": float(np.linalg.norm(quotient_correction, "fro")),
        "Gram inverse root norm": float(np.linalg.norm(gram_inverse_root, 2)),
        "relative defect norm": float(np.linalg.norm(relative_defect, "fro")),
        "reverse transition norm": float(np.linalg.norm(reverse, 2)),
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--size", type=int, default=18)
    parser.add_argument("--seed", type=int, default=398)
    parser.add_argument("--tolerance", type=float, default=8e-9)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    checks = certificate(args.size, args.seed)
    print("Proof 398 corrected-root bi-Schur ledger certificate")
    for label, value in checks.items():
        print(f"{label.replace(' ', '_')}={value:.12e}")

    exact_labels = [
        "ambient detector prefix commutator error",
        "corrected physical bracket error",
        "prolate root factor error",
        "eleven term ledger error",
        "moving root factor error",
        "moving detector readback error",
        "local detector commutator error",
        "local Schur intertwining error",
        "local forward boundary error",
        "local scalar pair error",
        "Markov source readback error",
        "relative defect completion error",
        "corrected root relative factor error",
        "causal boundary sandwich error",
        "scalar channel crossing norm",
        "scalar channel relative norm",
    ]
    maximum_error = max(checks[label] for label in exact_labels)
    if maximum_error > args.tolerance:
        raise RuntimeError(f"corrected bi-Schur ledger failed: {maximum_error:.3e}")
    if checks["quotient correction norm"] <= 1e-6:
        raise RuntimeError("quotient correction is accidentally trivial")
    if abs(checks["Gram inverse root norm"] - 1.0) <= 1e-3:
        raise RuntimeError("Gram normalization is accidentally trivial")
    if checks["relative defect norm"] <= 1e-6:
        raise RuntimeError("relative boundary response is accidentally trivial")
    if checks["reverse transition norm"] > 1.0 + args.tolerance:
        raise RuntimeError("Markov source transition is not contractive")

    print(f"maximum_exact_error_or_violation={maximum_error:.12e}")
    print("eleven_atom_corrected_root_ledger=RETAINED")
    print("local_bischur_boundary_factor=EXACT")
    print("fixed_s_trace_legality=CLOSED")
    print("uniform_rho_relative_bound=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
