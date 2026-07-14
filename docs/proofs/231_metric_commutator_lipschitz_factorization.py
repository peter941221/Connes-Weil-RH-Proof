#!/usr/bin/env python3
"""Certificate for Proof 231's quantitative metric graph factorization."""

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


def projection(columns: np.ndarray) -> np.ndarray:
    gram = columns.conj().T @ columns
    return columns @ np.linalg.solve(gram, columns.conj().T)


def norm(matrix: np.ndarray) -> float:
    return float(np.linalg.norm(matrix, ord=2))


def rotate(size: int, first: list[int], second: list[int], angle: float) -> np.ndarray:
    result = np.eye(size, dtype=complex)
    cosine = math.cos(angle)
    sine = math.sin(angle)
    for left, right in zip(first, second):
        result[left, left] = cosine
        result[right, right] = cosine
        result[left, right] = -sine
        result[right, left] = sine
    return result


def moved_projection(transfer: np.ndarray, basis: np.ndarray) -> np.ndarray:
    return projection(transfer @ basis)


def run(prime: int, angles: list[float]) -> tuple[dict[str, float], list[dict[str, float]]]:
    size = 18
    r_indices = list(range(0, 5))
    b_indices = list(range(5, 11))
    other_indices = list(range(11, size))
    complement_indices = r_indices + other_indices
    identity = np.eye(size, dtype=complex)
    r_basis = identity[:, r_indices]
    e_basis = identity[:, r_indices + b_indices]
    b_projection = identity[:, b_indices] @ identity[:, b_indices].conj().T
    r_projection = r_basis @ r_basis.conj().T
    block = np.zeros((size, size), dtype=complex)
    block[np.ix_(complement_indices, complement_indices)] = deterministic_unitary(
        len(complement_indices), 3
    )
    block[np.ix_(b_indices, b_indices)] = deterministic_unitary(
        len(b_indices), 7
    )
    alpha = prime**-0.5
    exact: dict[str, float] = {}
    rows: list[dict[str, float]] = []

    for angle in angles:
        mixer = rotate(size, b_indices, other_indices[: len(b_indices)], angle)
        unitary = mixer @ block @ mixer.conj().T
        transfer = identity - alpha * unitary
        metric = transfer.conj().T @ transfer
        moved_r = moved_projection(transfer, r_basis)
        moved_e = moved_projection(transfer, e_basis)
        moved_b = moved_e - moved_r
        commutator = norm(b_projection @ unitary - unitary @ b_projection)
        correction = norm(moved_b - b_projection)
        nested_error = norm(moved_e @ moved_r - moved_r)
        projection_error = norm(moved_b @ moved_b - moved_b)

        if angle == 0:
            exact = {
                "commutator_error": commutator,
                "correction_error": correction,
                "nested_error": nested_error,
                "projection_error": projection_error,
            }

        constant = alpha / (1 - alpha) + 4 * alpha * (1 + alpha) / (1 - alpha) ** 3
        rows.append(
            {
                "angle": angle,
                "commutator": commutator,
                "correction": correction,
                "bound": constant * commutator,
                "ratio": correction / commutator if commutator > 1e-14 else 0.0,
            }
        )
    return exact, rows


def parse_angles(raw: str) -> list[float]:
    return [float(item.strip()) for item in raw.split(",") if item.strip()]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--prime", type=int, default=2)
    parser.add_argument("--angles", default="0,0.2,0.1,0.05,0.025,0.0125")
    parser.add_argument("--max-error", type=float, default=2e-10)
    args = parser.parse_args()
    if args.prime < 2:
        raise ValueError("prime must be at least 2")
    angles = parse_angles(args.angles)
    if not angles or angles[0] != 0:
        raise ValueError("angles must start at zero")

    exact, rows = run(args.prime, angles)
    print("identity=metric commutator Lipschitz factorization")
    print(f"prime={args.prime} alpha={args.prime**-0.5:.12f}")
    for name, value in exact.items():
        print(f"exact_{name}={value:.3e}")
    print("perturbation_table=BEGIN")
    for row in rows:
        print(
            f"angle={row['angle']:.6f} commutator={row['commutator']:.12e} "
            f"correction={row['correction']:.12e} "
            f"bound={row['bound']:.12e} ratio={row['ratio']:.12e}"
        )
    print("perturbation_table=END")

    if max(exact.values()) > args.max_error:
        raise RuntimeError("exact commuting graph invariance failed")
    nonzero = [row for row in rows if row["commutator"] > 1e-14]
    if not nonzero:
        raise RuntimeError("no noncommuting perturbation was generated")
    if any(row["correction"] > row["bound"] + args.max_error for row in nonzero):
        raise RuntimeError("Lipschitz graph bound failed")
    if nonzero[-1]["correction"] >= nonzero[0]["correction"]:
        raise RuntimeError("correction did not shrink with commutator")

    print("certificate=PASS")
    print("exact_graph_factorization_verdict=PASS")
    print("ambient_lipschitz_bound_verdict=PASS")
    print("source_commutator_owner_verdict=PASS")
    print("root_readoff_graph_stability_verdict=OPEN")
    print("full_metric_compactness_verdict=OPEN")
    print("integrated_three_row_sign_verdict=OPEN")


if __name__ == "__main__":
    main()
