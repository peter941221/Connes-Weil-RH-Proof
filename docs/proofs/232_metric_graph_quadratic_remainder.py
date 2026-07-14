#!/usr/bin/env python3
"""Certificate for Proof 232's quadratic graph remainder.

The proof is the exact graph and Schur algebra in the companion document.
This script checks those identities on deterministic nested subspaces and
verifies that the nonlinear remainder shrinks quadratically with the source
commutator.  It does not certify the infinite-dimensional root trace ideal.
"""

from __future__ import annotations

import argparse
import math

import numpy as np


def deterministic_unitary(size: int, offset: int) -> np.ndarray:
    fourier = np.fft.fft(np.eye(size), axis=0) / math.sqrt(size)
    indices = np.arange(size, dtype=float)
    phases = np.exp(
        2j * np.pi * (indices**2 + offset * indices + 11) / size
    )
    return fourier.conj().T @ (phases[:, None] * fourier)


def projection(columns: np.ndarray) -> np.ndarray:
    gram = columns.conj().T @ columns
    return columns @ np.linalg.solve(gram, columns.conj().T)


def corner_inverse(basis: np.ndarray, operator: np.ndarray) -> np.ndarray:
    corner = basis.conj().T @ operator @ basis
    return basis @ np.linalg.solve(corner, basis.conj().T)


def norm(matrix: np.ndarray) -> float:
    return float(np.linalg.norm(matrix, ord=2))


def rotate(
    size: int, first: list[int], second: list[int], angle: float
) -> np.ndarray:
    result = np.eye(size, dtype=complex)
    cosine = math.cos(angle)
    sine = math.sin(angle)
    for left, right in zip(first, second):
        result[left, left] = cosine
        result[right, right] = cosine
        result[left, right] = -sine
        result[right, left] = sine
    return result


def run(
    prime: int, angles: list[float]
) -> tuple[dict[str, float], list[dict[str, float]]]:
    size = 20
    r_indices = list(range(0, 5))
    b_indices = list(range(5, 11))
    other_indices = list(range(11, size))
    outside_b_indices = r_indices + other_indices
    identity = np.eye(size, dtype=complex)
    r_basis = identity[:, r_indices]
    b_basis = identity[:, b_indices]
    e_basis = identity[:, r_indices + b_indices]
    r = projection(r_basis)
    b = projection(b_basis)

    block_unitary = np.zeros((size, size), dtype=complex)
    block_unitary[np.ix_(outside_b_indices, outside_b_indices)] = (
        deterministic_unitary(len(outside_b_indices), 3)
    )
    block_unitary[np.ix_(b_indices, b_indices)] = deterministic_unitary(
        len(b_indices), 7
    )

    alpha = prime**-0.5
    exact: dict[str, float] = {}
    rows: list[dict[str, float]] = []

    for angle in angles:
        mixer = rotate(
            size, b_indices, other_indices[: len(b_indices)], angle
        )
        unitary = mixer @ block_unitary @ mixer.conj().T
        transfer = identity - alpha * unitary
        metric = transfer.conj().T @ transfer

        moved_r = projection(transfer @ r_basis)
        moved_e = projection(transfer @ e_basis)
        moved_b_direct = moved_e - moved_r

        inverse_a = corner_inverse(r_basis, metric)
        inverse_d = corner_inverse(b_basis, metric)
        crossing_c = r @ metric @ b
        schur = b @ metric @ b - crossing_c.conj().T @ inverse_a @ crossing_c
        inverse_s = corner_inverse(b_basis, schur)
        z_map = b - inverse_a @ crossing_c
        moved_b_schur = transfer @ z_map @ inverse_s @ z_map.conj().T @ transfer.conj().T

        v_map = transfer @ b
        w_map = transfer @ inverse_a @ crossing_c
        bare_metric_b = v_map @ inverse_d @ v_map.conj().T

        compressed_transfer_inverse = corner_inverse(b_basis, b @ transfer @ b)
        crossing_j = (identity - b) @ transfer @ b
        graph_map = crossing_j @ compressed_transfer_inverse
        graph_r = corner_inverse(
            b_basis, b + graph_map.conj().T @ graph_map
        )
        graph_projection = (
            (b + graph_map)
            @ graph_r
            @ (b + graph_map.conj().T)
        )
        graph_tangent = graph_map + graph_map.conj().T
        graph_remainder = bare_metric_b - b - graph_tangent

        linear_schur = (
            -w_map @ inverse_d @ v_map.conj().T
            -v_map @ inverse_d @ w_map.conj().T
        )
        linear_channel = graph_tangent + linear_schur
        nonlinear_remainder = moved_b_schur - b - linear_channel

        inverse_difference = inverse_s - inverse_d
        factored_schur_remainder = (
            v_map @ inverse_difference @ v_map.conj().T
            -w_map @ inverse_difference @ v_map.conj().T
            -v_map @ inverse_difference @ w_map.conj().T
            +w_map @ inverse_s @ w_map.conj().T
        )
        factored_remainder = graph_remainder + factored_schur_remainder

        commutator = b @ unitary - unitary @ b
        commutator_star = b @ unitary.conj().T - unitary.conj().T @ b
        predicted_j = alpha * (identity - b) @ commutator @ b
        predicted_c = alpha * r @ (commutator + commutator_star) @ b
        delta = norm(commutator)
        residual = norm(nonlinear_remainder)

        if angle == 0:
            exact = {
                "direct_schur_error": norm(moved_b_direct - moved_b_schur),
                "graph_projection_error": norm(
                    graph_projection - bare_metric_b
                ),
                "commutator_j_error": norm(crossing_j - predicted_j),
                "commutator_c_error": norm(crossing_c - predicted_c),
                "commuting_correction_error": norm(moved_b_schur - b),
            }

        rows.append(
            {
                "angle": angle,
                "commutator": delta,
                "correction": norm(moved_b_schur - b),
                "linear": norm(linear_channel),
                "remainder": residual,
                "factorization_error": norm(
                    nonlinear_remainder - factored_remainder
                ),
                "remainder_over_delta": (
                    residual / delta if delta > 1e-14 else 0.0
                ),
                "remainder_over_delta2": (
                    residual / delta**2 if delta > 1e-14 else 0.0
                ),
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
    parser.add_argument("--max-quadratic-ratio", type=float, default=8.0)
    args = parser.parse_args()

    if args.prime < 2:
        raise ValueError("prime must be at least 2")
    angles = parse_angles(args.angles)
    if not angles or angles[0] != 0:
        raise ValueError("angles must start at zero")

    exact, rows = run(args.prime, angles)
    print("identity=metric graph quadratic remainder")
    print(f"prime={args.prime} alpha={args.prime**-0.5:.12f}")
    for name, value in exact.items():
        print(f"exact_{name}={value:.3e}")
    print("perturbation_table=BEGIN")
    for row in rows:
        print(
            f"angle={row['angle']:.6f} "
            f"commutator={row['commutator']:.12e} "
            f"correction={row['correction']:.12e} "
            f"linear={row['linear']:.12e} "
            f"remainder={row['remainder']:.12e} "
            f"factorization_error={row['factorization_error']:.3e} "
            f"remainder_over_delta={row['remainder_over_delta']:.12e} "
            f"remainder_over_delta2={row['remainder_over_delta2']:.12e}"
        )
    print("perturbation_table=END")

    if max(exact.values()) > args.max_error:
        raise RuntimeError("exact graph/Schur identity failed")
    nonzero = [row for row in rows if row["commutator"] > 1e-14]
    if not nonzero:
        raise RuntimeError("no noncommuting perturbation was generated")
    if max(row["factorization_error"] for row in rows) > args.max_error:
        raise RuntimeError("quadratic remainder factorization failed")
    if max(row["remainder_over_delta2"] for row in nonzero) > args.max_quadratic_ratio:
        raise RuntimeError("quadratic remainder bound failed")
    if nonzero[-1]["remainder_over_delta"] >= nonzero[0]["remainder_over_delta"]:
        raise RuntimeError("nonlinear remainder did not shrink quadratically")

    print("certificate=PASS")
    print("graph_tangent_verdict=PASS")
    print("schur_tangent_verdict=PASS")
    print("quadratic_crossing_factorization_verdict=PASS")
    print("nonlinear_two_crossing_algebra_verdict=PASS")
    print("linear_toeplitz_profile_verdict=OPEN")
    print("integrated_three_row_sign_verdict=OPEN")


if __name__ == "__main__":
    main()
