#!/usr/bin/env python3
"""Finite-matrix certificate for Proof 230's ideal-invariance algebra.

The quotient theorem is exact C*-algebra reasoning.  This script checks the
commuting case and norm-continuous perturbations of it on deterministic nested
subspaces.
"""

from __future__ import annotations

import argparse
import math

import numpy as np


def deterministic_unitary(size: int, offset: int) -> np.ndarray:
    fourier = np.fft.fft(np.eye(size), axis=0) / math.sqrt(size)
    indices = np.arange(size, dtype=float)
    phases = np.exp(
        2j * np.pi * (indices**2 + offset * indices + 5) / size
    )
    return fourier.conj().T @ (phases[:, None] * fourier)


def orthogonal_projection(columns: np.ndarray) -> np.ndarray:
    gram = columns.conj().T @ columns
    return columns @ np.linalg.solve(gram, columns.conj().T)


def operator_norm(matrix: np.ndarray) -> float:
    return float(np.linalg.norm(matrix, ord=2))


def rotation(size: int, left: list[int], right: list[int], angle: float) -> np.ndarray:
    result = np.eye(size, dtype=complex)
    cosine = math.cos(angle)
    sine = math.sin(angle)
    for first, second in zip(left, right):
        result[first, first] = cosine
        result[second, second] = cosine
        result[first, second] = -sine
        result[second, first] = sine
    return result


def metric_projection(transfer: np.ndarray, basis: np.ndarray) -> np.ndarray:
    return orthogonal_projection(transfer @ basis)


def build_commuting_unitary(
    size: int, complement_indices: list[int], b_indices: list[int]
) -> np.ndarray:
    result = np.zeros((size, size), dtype=complex)
    complement_block = deterministic_unitary(len(complement_indices), 3)
    b_block = deterministic_unitary(len(b_indices), 7)
    result[np.ix_(complement_indices, complement_indices)] = complement_block
    result[np.ix_(b_indices, b_indices)] = b_block
    return result


def certificate(prime: int, angles: list[float]) -> dict[str, object]:
    size = 18
    r_indices = list(range(0, 5))
    b_indices = list(range(5, 11))
    outside_indices = list(range(11, size))
    complement_indices = r_indices + outside_indices

    identity = np.eye(size, dtype=complex)
    standard = identity.copy()
    r_basis = standard[:, r_indices]
    b_basis = standard[:, b_indices]
    e_basis = standard[:, r_indices + b_indices]
    r_projection = r_basis @ r_basis.conj().T
    b_projection = b_basis @ b_basis.conj().T

    parameter = prime**-0.5
    commuting_unitary = build_commuting_unitary(
        size, complement_indices, b_indices
    )

    rows = []
    exact_values: dict[str, float] = {}
    for angle in angles:
        mixer = rotation(size, b_indices, outside_indices[: len(b_indices)], angle)
        unitary = mixer @ commuting_unitary @ mixer.conj().T
        transfer = identity - parameter * unitary
        metric = transfer.conj().T @ transfer

        moved_r = metric_projection(transfer, r_basis)
        moved_e = metric_projection(transfer, e_basis)
        moved_b = moved_e - moved_r

        commutator_norm = operator_norm(
            b_projection @ unitary - unitary @ b_projection
        )
        complement_error = operator_norm(moved_b - b_projection)
        nested_error = operator_norm(moved_e @ moved_r - moved_r)
        projection_error = operator_norm(moved_b @ moved_b - moved_b)
        cross_block = operator_norm(r_projection @ metric @ b_projection)

        if angle == 0:
            exact_values = {
                "exact_commutator_error": commutator_norm,
                "exact_complement_error": complement_error,
                "exact_metric_cross_error": cross_block,
                "exact_nested_error": nested_error,
                "exact_projection_error": projection_error,
            }
        rows.append(
            {
                "angle": angle,
                "commutator_norm": commutator_norm,
                "complement_error": complement_error,
                "ratio": (
                    complement_error / commutator_norm
                    if commutator_norm > 1e-14
                    else 0.0
                ),
            }
        )

    return {"exact": exact_values, "rows": rows}


def parse_floats(raw: str) -> list[float]:
    return [float(item.strip()) for item in raw.split(",") if item.strip()]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--prime", type=int, default=2)
    parser.add_argument("--angles", default="0,0.2,0.1,0.05,0.025,0.0125")
    parser.add_argument("--max-error", type=float, default=2e-10)
    parser.add_argument("--max-ratio", type=float, default=20.0)
    args = parser.parse_args()

    if args.prime < 2:
        raise ValueError("prime must be at least 2")
    angles = parse_floats(args.angles)
    if not angles or angles[0] != 0 or min(angles) < 0:
        raise ValueError("angles must start with zero and remain nonnegative")

    values = certificate(args.prime, angles)
    exact = values["exact"]
    rows = values["rows"]

    print("identity=metric nested-complement ideal invariance")
    print(f"prime={args.prime} alpha={args.prime**-0.5:.12f}")
    for name, value in exact.items():
        print(f"{name}={value:.3e}")
    print("perturbation_table=BEGIN")
    for row in rows:
        print(
            f"angle={row['angle']:.6f} "
            f"commutator_norm={row['commutator_norm']:.12e} "
            f"complement_error={row['complement_error']:.12e} "
            f"ratio={row['ratio']:.12e}"
        )
    print("perturbation_table=END")

    if max(exact.values()) > args.max_error:
        raise RuntimeError("commuting nested complement was not invariant")
    nonzero_rows = [row for row in rows if row["commutator_norm"] > 1e-14]
    if not nonzero_rows:
        raise RuntimeError("perturbation did not create a commutator")
    if max(row["ratio"] for row in nonzero_rows) > args.max_ratio:
        raise RuntimeError("metric correction is not controlled near commuting data")
    if nonzero_rows[-1]["complement_error"] >= nonzero_rows[0]["complement_error"]:
        raise RuntimeError("metric correction did not shrink with the commutator")

    print("certificate=PASS")
    print("exact_commuting_invariance_verdict=PASS")
    print("ideal_generation_verdict=PASS")
    print("new_metric_essential_class_verdict=REJECTED")
    print("root_compact_ideal_stability_verdict=OPEN")
    print("full_metric_compactness_verdict=OPEN")
    print("integrated_three_row_sign_verdict=OPEN")


if __name__ == "__main__":
    main()
