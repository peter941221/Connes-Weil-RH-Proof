"""Finite certificate for Proof 381's moving model-space defect guard."""

from __future__ import annotations

import argparse

import numpy as np


def shift_matrix(size: int) -> np.ndarray:
    shift = np.zeros((size, size), dtype=complex)
    for column in range(size - 1):
        shift[column + 1, column] = 1.0
    return shift


def model_projection(size: int, zero_index: int, degree: int) -> np.ndarray:
    projection = np.zeros((size, size), dtype=complex)
    projection[zero_index : zero_index + degree, zero_index : zero_index + degree] = (
        np.eye(degree, dtype=complex)
    )
    return projection


def numerical_rank(matrix: np.ndarray, tolerance: float = 1e-10) -> int:
    return int(np.count_nonzero(np.linalg.svd(matrix, compute_uv=False) > tolerance))


def relative_error(actual: float | np.ndarray, expected: float | np.ndarray) -> float:
    return float(
        np.linalg.norm(np.asarray(actual) - np.asarray(expected))
        / max(1.0, float(np.linalg.norm(np.asarray(expected))))
    )


def certificate(max_degree: int, degrees: list[int]) -> tuple[dict[str, float], list]:
    if max(degrees) > max_degree:
        raise ValueError("tested degree exceeds the ambient truncation")

    zero_index = 2
    size = zero_index + max_degree + 2
    shift = shift_matrix(size)
    basis_labels = np.arange(size) - zero_index
    weights = 1.0 / (1.0 + np.abs(basis_labels))
    common_owner = np.diag(weights.astype(complex))
    common_owner_inverse = np.diag((1.0 / weights).astype(complex))

    maximum_rank_error = 0.0
    maximum_operator_norm_error = 0.0
    maximum_hs_error = 0.0
    maximum_factor_error = 0.0
    rows = []

    for degree in degrees:
        projection = model_projection(size, zero_index, degree)
        defect = shift @ projection - projection @ shift
        factor = defect @ common_owner_inverse

        rank = numerical_rank(defect)
        operator_norm = float(np.linalg.norm(defect, 2))
        hs_square = float(np.linalg.norm(defect, "fro") ** 2)
        factor_norm = float(np.linalg.norm(factor, 2))

        maximum_rank_error = max(maximum_rank_error, abs(rank - 2.0))
        maximum_operator_norm_error = max(
            maximum_operator_norm_error,
            abs(operator_norm - 1.0),
        )
        maximum_hs_error = max(maximum_hs_error, abs(hs_square - 2.0))
        maximum_factor_error = max(
            maximum_factor_error,
            relative_error(defect, factor @ common_owner),
            abs(factor_norm - float(degree)),
        )
        rows.append((degree, rank, operator_norm, hs_square, factor_norm))

    owner_hs_square = float(np.linalg.norm(common_owner, "fro") ** 2)
    return (
        {
            "maximum rank error": maximum_rank_error,
            "maximum operator norm error": maximum_operator_norm_error,
            "maximum Hilbert Schmidt error": maximum_hs_error,
            "maximum factorization error": maximum_factor_error,
            "finite common owner Hilbert Schmidt square": owner_hs_square,
            "largest left factor norm": rows[-1][-1],
        },
        rows,
    )


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-degree", type=int, default=128)
    parser.add_argument("--degrees", default="2,4,8,16,32,64,128")
    parser.add_argument("--tolerance", type=float, default=3e-10)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    degrees = [int(value) for value in args.degrees.split(",")]
    checks, rows = certificate(args.max_degree, degrees)

    print("Proof 381 nearly-invariant common-owner obstruction certificate")
    print("degree  rank  operator_norm  HS_square  least_factor_norm")
    for degree, rank, operator_norm, hs_square, factor_norm in rows:
        print(
            f"{degree:6d}  {rank:4d}  {operator_norm: .8e}  "
            f"{hs_square: .8e}  {factor_norm: .8e}"
        )
    print()
    for label, value in checks.items():
        print(f"{label.replace(' ', '_')}={value:.12e}")

    exact_labels = [
        "maximum rank error",
        "maximum operator norm error",
        "maximum Hilbert Schmidt error",
        "maximum factorization error",
    ]
    maximum_error = max(checks[label] for label in exact_labels)
    if maximum_error > args.tolerance:
        raise RuntimeError(f"common-owner guard failed: {maximum_error:.3e}")

    print(f"maximum_exact_error={maximum_error:.12e}")
    print("uniform_rank_two_S2_bound=TRUE")
    print("uniform_common_HS_right_factor=FALSE")
    print("source_boundary_localization=REQUIRED")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
