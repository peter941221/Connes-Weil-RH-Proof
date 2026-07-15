#!/usr/bin/env python3
"""Finite-section death test for the complete nested first variation.

Unlike the separated Proof 225 profile, this script forms the same finite
Sonin projection for every translation length and differentiates the nested
complement itself at alpha=0.  It then builds the trace-diagonal Toeplitz
kernel and applies the pre-root differential.  The experiment distinguishes
an integrated e^(-L) law from a surviving e^(-L/2) central law.

The finite periodic scattering section is diagnostic only.  The mathematical
route still needs a continuous, operator-norm-convergent theorem.
"""

from __future__ import annotations

import argparse
import math

import numpy as np


LANCZOS_COEFFICIENTS = np.array(
    [
        0.99999999999980993,
        676.5203681218851,
        -1259.1392167224028,
        771.32342877765313,
        -176.61502916214059,
        12.507343278998905,
        -0.13857109526572012,
        9.9843695780195716e-6,
        1.5056327351493116e-7,
    ]
)


def parse_floats(raw: str) -> list[float]:
    return [float(item.strip()) for item in raw.split(",") if item.strip()]


def log_gamma_lanczos(values: np.ndarray) -> np.ndarray:
    shifted = values - 1.0
    series = np.full_like(values, LANCZOS_COEFFICIENTS[0], dtype=complex)
    for index, coefficient in enumerate(
        LANCZOS_COEFFICIENTS[1:], start=1
    ):
        series += coefficient / (shifted + index)
    tail = shifted + 7.5
    return (
        0.5 * np.log(2.0 * np.pi)
        + (shifted + 0.5) * np.log(tail)
        - tail
        + np.log(series)
    )


def archimedean_scattering(frequencies: np.ndarray) -> np.ndarray:
    arguments = 0.25 + 0.5j * frequencies
    log_gamma = log_gamma_lanczos(arguments)
    return np.exp(
        -1j * frequencies * math.log(math.pi)
        + log_gamma
        - np.conj(log_gamma)
    )


def sonin_basis(
    size: int, step: float, intersection_tolerance: float
) -> tuple[np.ndarray, np.ndarray]:
    coordinates = (np.arange(size) - size // 2) * step
    frequencies = 2.0 * np.pi * np.fft.fftfreq(size, d=step)
    scattering = archimedean_scattering(frequencies)

    positive_indices = np.flatnonzero(coordinates >= 0.0)
    positive_basis = np.zeros(
        (size, len(positive_indices)), dtype=complex
    )
    positive_basis[positive_indices, np.arange(len(positive_indices))] = 1.0
    scattering_image = np.fft.ifft(
        scattering[:, None] * np.fft.fft(positive_basis, axis=0),
        axis=0,
    )
    scattering_image[coordinates >= 0.0, :] = 0.0
    angle = scattering_image.conj().T @ scattering_image
    angle = (angle + angle.conj().T) / 2.0
    eigenvalues, eigenvectors = np.linalg.eigh(angle)
    selected = eigenvalues > 1.0 - intersection_tolerance

    basis = np.zeros((size, int(selected.sum())), dtype=complex)
    basis[positive_indices, :] = eigenvectors[:, selected]
    return basis, eigenvalues


def shifted_columns(columns: np.ndarray, displacement: int) -> np.ndarray:
    return np.roll(columns, -displacement, axis=0)


def projection_first_variation(
    basis: np.ndarray, displacement: int
) -> np.ndarray:
    shifted = shifted_columns(basis, displacement)
    tangential = basis @ (basis.conj().T @ shifted)
    normal = shifted - tangential
    return -(normal @ basis.conj().T + basis @ normal.conj().T)


def halfline_first_variation(
    coordinates: np.ndarray, displacement: int
) -> np.ndarray:
    size = len(coordinates)
    positive = coordinates >= 0.0
    shifted_positive = np.roll(positive, -displacement)
    crossing = (~positive) & shifted_positive
    matrix = np.zeros((size, size), dtype=complex)
    rows = np.flatnonzero(crossing)
    columns = (rows + displacement) % size
    matrix[rows, columns] = -1.0
    matrix += matrix.conj().T
    return matrix


def trace_diagonal_toeplitz(
    matrix: np.ndarray, root_size: int
) -> np.ndarray:
    values: dict[int, complex] = {}
    for offset in range(-(root_size - 1), root_size):
        values[offset] = np.trace(matrix, offset=offset)
    toeplitz = np.empty((root_size, root_size), dtype=complex)
    for row in range(root_size):
        for column in range(root_size):
            toeplitz[row, column] = values[column - row]
    return toeplitz


def root_differential(root_size: int, step: float) -> np.ndarray:
    differential = 0.5 * np.eye(root_size, dtype=complex)
    for index in range(root_size):
        if index + 1 < root_size:
            differential[index, index + 1] += 1.0 / (2.0 * step)
        if index - 1 >= 0:
            differential[index, index - 1] -= 1.0 / (2.0 * step)
    return differential


def operator_norm(matrix: np.ndarray) -> float:
    hermitian = (matrix + matrix.conj().T) / 2.0
    return float(np.max(np.abs(np.linalg.eigvalsh(hermitian))))


def scaling_row(
    basis: np.ndarray,
    coordinates: np.ndarray,
    step: float,
    root_size: int,
    translation_length: float,
) -> dict[str, float]:
    displacement = int(round(translation_length / step))
    realized_length = displacement * step
    sonin_derivative = projection_first_variation(basis, displacement)
    halfline_derivative = halfline_first_variation(
        coordinates, displacement
    )
    nested_derivative = halfline_derivative - sonin_derivative
    self_adjoint_error = float(
        np.linalg.norm(
            nested_derivative - nested_derivative.conj().T, ord=2
        )
    )

    toeplitz = trace_diagonal_toeplitz(nested_derivative, root_size)
    differential = root_differential(root_size, step)
    root_operator = step**2 * (
        differential.conj().T @ toeplitz @ differential
    )
    derivative_norm = operator_norm(root_operator)
    euler_parameter = math.exp(-realized_length / 2.0)
    integrated_norm = euler_parameter * derivative_norm
    return {
        "requested_length": translation_length,
        "realized_length": realized_length,
        "displacement": float(displacement),
        "derivative_norm": derivative_norm,
        "integrated_norm": integrated_norm,
        "scaled_half": integrated_norm * math.exp(realized_length / 2.0),
        "scaled_full": integrated_norm * math.exp(realized_length),
        "self_adjoint_error": self_adjoint_error,
    }


def fitted_slope(rows: list[dict[str, float]]) -> float:
    lengths = np.array([row["realized_length"] for row in rows])
    logarithms = np.log(
        np.array([row["integrated_norm"] for row in rows])
    )
    return float(np.polyfit(lengths, logarithms, 1)[0])


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--size", type=int, default=768)
    parser.add_argument("--step", type=float, default=0.05)
    parser.add_argument("--root-width", type=float, default=1.0)
    parser.add_argument("--lengths", default="2.5,3,3.5,4,4.5,5,5.5,6")
    parser.add_argument("--intersection-tolerance", type=float, default=1e-8)
    parser.add_argument("--max-self-adjoint-error", type=float, default=2e-10)
    args = parser.parse_args()

    if args.size < 256 or args.size % 2 != 0:
        raise ValueError("size must be an even integer at least 256")
    if args.step <= 0.0:
        raise ValueError("step must be positive")
    if args.root_width <= 4.0 * args.step:
        raise ValueError("root-width is too small")
    lengths = parse_floats(args.lengths)
    if len(lengths) < 4:
        raise ValueError("lengths must contain at least four values")

    coordinates = (np.arange(args.size) - args.size // 2) * args.step
    half_domain = args.size * args.step / 2.0
    if max(lengths) + args.root_width >= half_domain / 2.0:
        raise ValueError("domain is too small for the requested translations")

    basis, angle_eigenvalues = sonin_basis(
        args.size, args.step, args.intersection_tolerance
    )
    if basis.shape[1] == 0:
        raise RuntimeError("finite section found no near-Sonin directions")
    root_size = int(round(args.root_width / args.step))
    rows = [
        scaling_row(
            basis,
            coordinates,
            args.step,
            root_size,
            length,
        )
        for length in lengths
    ]
    slope = fitted_slope(rows)

    print("identity=complete nested first-variation central scaling")
    print(f"size={args.size} step={args.step:.8f}")
    print(f"domain_half_width={half_domain:.8f}")
    print(f"root_width={args.root_width:.8f}")
    print(f"near_sonin_rank={basis.shape[1]}")
    print(f"angle_max={float(angle_eigenvalues[-1]):.12e}")
    print(f"angle_selected_min={float(angle_eigenvalues[-basis.shape[1]]):.12e}")
    print("scaling_table=BEGIN")
    for row in rows:
        print(
            f"L={row['realized_length']:.8f} "
            f"derivative_norm={row['derivative_norm']:.12e} "
            f"integrated_norm={row['integrated_norm']:.12e} "
            f"scaled_half={row['scaled_half']:.12e} "
            f"scaled_full={row['scaled_full']:.12e} "
            f"self_adjoint_error={row['self_adjoint_error']:.3e}"
        )
    print("scaling_table=END")
    print(f"log_norm_slope_per_L={slope:.12e}")

    if max(row["self_adjoint_error"] for row in rows) > args.max_self_adjoint_error:
        raise RuntimeError("complete nested derivative lost self-adjointness")
    if not all(row["integrated_norm"] > 0.0 for row in rows):
        raise RuntimeError("scaling norm must stay positive")

    print("certificate=PASS")
    print("complete_nested_same_ledger_verdict=PASS")
    if slope < -0.75:
        print("central_scaling_diagnostic=FULL_HALF_POWER_GAIN")
    else:
        print("central_scaling_diagnostic=SURVIVING_HALF_POWER")
    print("continuous_operator_norm_theorem=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
