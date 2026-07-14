#!/usr/bin/env python3
"""Diagnostic constrained-Rayleigh probe for the one-prime sign gate.

This combines the literal CC20 ordinary Q-delta kernel with the finite-section
nested-complement correction from Proof 224.  The scattering section is not a
certified approximation theorem; the output is a rejection/stability screen.
"""

from __future__ import annotations

import argparse
import importlib.util
import math
from pathlib import Path

import numpy as np


def load_proof_224():
    path = Path(__file__).with_name(
        "224_metric_sonin_nested_complement_remainder.py"
    )
    spec = importlib.util.spec_from_file_location("proof_224", path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path.name}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


PROOF_224 = load_proof_224()


def sine_integral(values: np.ndarray, order: int = 256) -> np.ndarray:
    """Gauss-Legendre evaluation of Si(x) for nonnegative finite x."""
    values = np.asarray(values, dtype=float)
    nodes, weights = np.polynomial.legendre.leggauss(order)
    points = 0.5 * values[..., None] * (nodes + 1.0)
    integrand = np.sinc(points / math.pi)
    return 0.5 * values * (integrand @ weights)


def si_quotient_profiles(values: np.ndarray) -> tuple[np.ndarray, ...]:
    values = np.asarray(values, dtype=float)
    integrals = sine_integral(values)
    quotient = np.empty_like(values)
    first = np.empty_like(values)
    second = np.empty_like(values)
    is_zero = values == 0.0
    nonzero = ~is_zero
    x = values[nonzero]
    si = integrals[nonzero]
    quotient[nonzero] = si / x
    first[nonzero] = (np.sin(x) - si) / x**2
    second[nonzero] = (
        (np.cos(x) - np.sin(x) / x) * x**2
        - 2.0 * x * (np.sin(x) - si)
    ) / x**4
    quotient[is_zero] = 1.0
    first[is_zero] = 0.0
    second[is_zero] = -1.0 / 9.0
    return quotient, first, second


def cc20_q_delta_regular(log_distances: np.ndarray) -> np.ndarray:
    """Ordinary kernel Q(delta(exp(|x-y|))), excluding -2 Dirac_0."""
    rho = np.exp(np.asarray(log_distances, dtype=float))
    plus = 2.0 * math.pi * (1.0 + rho)
    minus = 2.0 * math.pi * (rho - 1.0)
    q_plus, d_plus, dd_plus = si_quotient_profiles(plus)
    q_minus, d_minus, dd_minus = si_quotient_profiles(minus)
    branch = q_plus + q_minus
    branch_d = 2.0 * math.pi * (d_plus + d_minus)
    branch_dd = (2.0 * math.pi) ** 2 * (dd_plus + dd_minus)
    sqrt_rho = np.sqrt(rho)
    delta = 2.0 * sqrt_rho * branch
    delta_d = branch / sqrt_rho + 2.0 * sqrt_rho * branch_d
    delta_dd = (
        2.0 * sqrt_rho * branch_dd
        + 2.0 * branch_d / sqrt_rho
        - branch / (2.0 * rho * sqrt_rho)
    )
    regular = -(rho * delta_d + rho**2 * delta_dd) + delta / 4.0
    diagonal = (
        8.0 * math.pi**2 / 9.0
        + sine_integral(np.array([4.0 * math.pi]))[0] / (4.0 * math.pi)
        - 0.5
    )
    regular[np.asarray(log_distances) == 0.0] = diagonal
    return regular


def scattering_residual_toeplitz(
    prime: int,
    cells_per_prime: int,
    intersection_tolerance: float,
    root_size: int,
) -> tuple[np.ndarray, int, float]:
    cell_length = math.log(prime)
    parameter = 1.0 / math.sqrt(prime)
    size = 64 * cells_per_prime
    step = cell_length / cells_per_prime
    coordinates = (np.arange(size) - size // 2) * step
    frequencies = 2.0 * math.pi * np.fft.fftfreq(size, d=step)

    gamma_arguments = 0.25 + 0.5j * frequencies
    log_gamma = PROOF_224.log_gamma_lanczos(gamma_arguments)
    phase = np.exp(
        -1j * frequencies * math.log(math.pi)
        + log_gamma
        - np.conj(log_gamma)
    )

    positive_indices = np.flatnonzero(coordinates >= 0)
    positive_basis = np.zeros(
        (size, len(positive_indices)), dtype=complex
    )
    positive_basis[positive_indices, np.arange(len(positive_indices))] = 1
    phase_image = np.fft.ifft(
        phase[:, None] * np.fft.fft(positive_basis, axis=0), axis=0
    )
    phase_image[coordinates >= 0, :] = 0
    angle = phase_image.conj().T @ phase_image
    angle = (angle + angle.conj().T) / 2.0
    eigenvalues, eigenvectors = np.linalg.eigh(angle)
    selected = eigenvalues > 1.0 - intersection_tolerance

    sonin_basis = np.zeros((size, int(selected.sum())), dtype=complex)
    sonin_basis[positive_indices, :] = eigenvectors[:, selected]
    sonin = sonin_basis @ sonin_basis.conj().T
    shift = PROOF_224.finite_shift(size, cells_per_prime)
    transfer = np.eye(size, dtype=complex) - parameter * shift
    sonin_difference = (
        PROOF_224.metric_projection(transfer, sonin_basis) - sonin
    )

    positive = positive_basis @ positive_basis.conj().T
    halfline_difference = (
        PROOF_224.metric_projection(transfer, positive_basis) - positive
    )
    # By Proof 224 (N.8), this is -(B_a-B_0), hence the correction -G_a.
    residual = sonin_difference - halfline_difference
    toeplitz = np.empty((root_size, root_size), dtype=complex)
    for row in range(root_size):
        for column in range(root_size):
            toeplitz[row, column] = np.trace(
                residual, offset=column - row
            )
    toeplitz = (toeplitz + toeplitz.conj().T) / 2.0
    return toeplitz, int(selected.sum()), step


def q_root_matrix(size: int, step: float) -> np.ndarray:
    derivative = np.zeros((size, size), dtype=complex)
    if size == 1:
        derivative[0, 0] = 0.5
        return derivative
    derivative[0, 1] = 1.0 / (2.0 * step)
    derivative[-1, -2] = -1.0 / (2.0 * step)
    for index in range(1, size - 1):
        derivative[index, index + 1] = 1.0 / (2.0 * step)
        derivative[index, index - 1] = -1.0 / (2.0 * step)
    derivative += 0.5 * np.eye(size)
    return derivative


def nullspace(rows: np.ndarray, tolerance: float = 1e-11) -> np.ndarray:
    _left, singular_values, right_h = np.linalg.svd(rows, full_matrices=True)
    rank = int(np.sum(singular_values > tolerance * singular_values[0]))
    return right_h.conj().T[:, rank:]


def constrained_extrema(operator: np.ndarray, rows: np.ndarray) -> tuple[float, float]:
    basis = nullspace(rows)
    compressed = basis.conj().T @ operator @ basis
    compressed = (compressed + compressed.conj().T) / 2.0
    eigenvalues = np.linalg.eigvalsh(compressed)
    return float(eigenvalues[0]), float(eigenvalues[-1])


def constrained_max_eigenpair(
    operator: np.ndarray, rows: np.ndarray
) -> tuple[float, np.ndarray]:
    basis = nullspace(rows)
    compressed = basis.conj().T @ operator @ basis
    compressed = (compressed + compressed.conj().T) / 2.0
    eigenvalues, eigenvectors = np.linalg.eigh(compressed)
    vector = basis @ eigenvectors[:, -1]
    vector /= np.linalg.norm(vector)
    return float(eigenvalues[-1]), vector


def constrained_extrema_in_basis(
    operator: np.ndarray, rows: np.ndarray, basis: np.ndarray
) -> tuple[float, float]:
    coefficient_rows = rows @ basis
    constraint_kernel = nullspace(coefficient_rows)
    physical_basis = basis @ constraint_kernel
    compressed = physical_basis.conj().T @ operator @ physical_basis
    compressed = (compressed + compressed.conj().T) / 2.0
    eigenvalues = np.linalg.eigvalsh(compressed)
    return float(eigenvalues[0]), float(eigenvalues[-1])


def archimedean_continuum_galerkin(
    length: float, mode_count: int, quadrature_order: int
) -> tuple[float, float]:
    nodes, weights = np.polynomial.legendre.leggauss(quadrature_order)
    points = 0.5 * length * (nodes + 1.0)
    weights = 0.5 * length * weights
    modes = np.arange(1, mode_count + 1, dtype=float)
    basis = math.sqrt(2.0 / length) * np.sin(
        math.pi * np.outer(points, modes) / length
    )
    distance_matrix = np.abs(points[:, None] - points[None, :])
    kernel = cc20_q_delta_regular(distance_matrix.reshape(-1)).reshape(
        quadrature_order, quadrature_order
    )
    weighted_basis = weights[:, None] * basis
    compact_matrix = weighted_basis.T @ kernel @ weighted_basis
    compact_matrix = (compact_matrix + compact_matrix.T) / 2.0
    remainder = -2.0 * np.eye(mode_count) + compact_matrix
    rows = np.vstack(
        [
            weights @ basis,
            (weights * np.exp(points)) @ basis,
        ]
    ).astype(complex)
    return constrained_extrema(remainder.astype(complex), rows)


def one_probe(
    prime: int,
    cells: int,
    root_fraction: float,
    intersection_tolerance: float,
    physical_modes: int,
) -> dict[str, float | int]:
    root_size = max(4, int(round(root_fraction * cells)))
    residual, rank, step = scattering_residual_toeplitz(
        prime, cells, intersection_tolerance, root_size
    )
    points = np.arange(1, root_size + 1, dtype=float) * step
    distance_indices = np.abs(
        np.arange(root_size)[:, None] - np.arange(root_size)[None, :]
    )
    regular_values = cc20_q_delta_regular(
        np.arange(root_size, dtype=float) * step
    )
    regular_kernel = regular_values[distance_indices]
    arch_compact = step * regular_kernel

    differential = q_root_matrix(root_size, step)
    metric_compact = step * differential.conj().T @ residual @ differential
    metric_compact = (metric_compact + metric_compact.conj().T) / 2.0

    identity = np.eye(root_size, dtype=complex)
    arch_remainder = -2.0 * identity + arch_compact
    finite_s_remainder = arch_remainder + metric_compact
    rows = step * np.vstack(
        [np.ones(root_size), np.exp(points)]
    ).astype(complex)

    arch_min, arch_max = constrained_extrema(arch_remainder, rows)
    finite_min, finite_max = constrained_extrema(finite_s_remainder, rows)
    compact_min, compact_max = constrained_extrema(
        arch_compact + metric_compact, rows
    )
    _finite_max_check, maximizing_vector = constrained_max_eigenpair(
        finite_s_remainder, rows
    )
    arch_on_max = float(
        np.vdot(maximizing_vector, arch_remainder @ maximizing_vector).real
    )
    metric_on_max = float(
        np.vdot(maximizing_vector, metric_compact @ maximizing_vector).real
    )
    boundary_mass = float(
        abs(maximizing_vector[0]) ** 2 + abs(maximizing_vector[-1]) ** 2
    )
    spectrum = np.abs(np.fft.fft(maximizing_vector)) ** 2
    frequencies = np.minimum(
        np.arange(root_size), root_size - np.arange(root_size)
    )
    spectral_centroid = float(
        np.sum(frequencies * spectrum) / np.sum(spectrum)
    )
    nyquist = max(1.0, root_size / 2.0)
    row_residual = float(np.linalg.norm(rows @ maximizing_vector))
    mode_count = min(physical_modes, root_size - 1)
    grid_indices = np.arange(1, root_size + 1, dtype=float)
    mode_indices = np.arange(1, mode_count + 1, dtype=float)
    sine_basis = math.sqrt(2.0 / (root_size + 1.0)) * np.sin(
        math.pi
        * np.outer(grid_indices, mode_indices)
        / (root_size + 1.0)
    )
    physical_min, physical_max = constrained_extrema_in_basis(
        finite_s_remainder, rows, sine_basis.astype(complex)
    )
    arch_physical_min, arch_physical_max = constrained_extrema_in_basis(
        arch_remainder, rows, sine_basis.astype(complex)
    )
    return {
        "cells": cells,
        "root_size": root_size,
        "sonin_rank": rank,
        "interval_length": root_size * step,
        "arch_min": arch_min,
        "arch_max": arch_max,
        "metric_norm": float(np.linalg.norm(metric_compact, ord=2)),
        "compact_min": compact_min,
        "compact_max": compact_max,
        "finite_min": finite_min,
        "finite_max": finite_max,
        "arch_on_max": arch_on_max,
        "metric_on_max": metric_on_max,
        "boundary_mass": boundary_mass,
        "spectral_fraction": spectral_centroid / nyquist,
        "row_residual": row_residual,
        "physical_modes": mode_count,
        "physical_min": physical_min,
        "physical_max": physical_max,
        "arch_physical_min": arch_physical_min,
        "arch_physical_max": arch_physical_max,
    }


def parse_integers(raw: str) -> list[int]:
    return [int(value.strip()) for value in raw.split(",") if value.strip()]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--prime", type=int, default=2)
    parser.add_argument("--cells", default="8,12,16,20")
    parser.add_argument("--root-fraction", type=float, default=0.75)
    parser.add_argument("--intersection-tolerance", type=float, default=1e-10)
    parser.add_argument("--physical-modes", type=int, default=6)
    parser.add_argument("--arch-continuum-orders", default="")
    args = parser.parse_args()
    if args.prime < 2:
        raise ValueError("prime must be at least 2")
    if not 0 < args.root_fraction <= 2:
        raise ValueError("root fraction must lie in (0,2]")
    if args.physical_modes < 3:
        raise ValueError("physical modes must be at least 3")

    print("probe=finite-S constrained sign diagnostic")
    print(f"prime={args.prime}")
    print("rows=M_0(xi),M_1(xi)")
    print("sign_gate=finite_max<=0 equivalently compact_max<=2")
    for cells in parse_integers(args.cells):
        result = one_probe(
            args.prime,
            cells,
            args.root_fraction,
            args.intersection_tolerance,
            args.physical_modes,
        )
        print(
            " ".join(
                [
                    f"cells={result['cells']}",
                    f"root_size={result['root_size']}",
                    f"sonin_rank={result['sonin_rank']}",
                    f"length={result['interval_length']:.9f}",
                    f"arch=[{result['arch_min']:+.9f},{result['arch_max']:+.9f}]",
                    f"metric_norm={result['metric_norm']:.9f}",
                    f"compact=[{result['compact_min']:+.9f},{result['compact_max']:+.9f}]",
                    f"finite=[{result['finite_min']:+.9f},{result['finite_max']:+.9f}]",
                    f"max_split={result['arch_on_max']:+.9f}+{result['metric_on_max']:+.9f}",
                    f"freq_fraction={result['spectral_fraction']:.6f}",
                    f"boundary_mass={result['boundary_mass']:.6f}",
                    f"row_residual={result['row_residual']:.3e}",
                    f"physical{result['physical_modes']}=[{result['physical_min']:+.9f},{result['physical_max']:+.9f}]",
                    f"arch_physical{result['physical_modes']}=[{result['arch_physical_min']:+.9f},{result['arch_physical_max']:+.9f}]",
                ]
            )
        )
    continuum_orders = parse_integers(args.arch_continuum_orders)
    if continuum_orders:
        length = args.root_fraction * math.log(args.prime)
        for order in continuum_orders:
            continuum_min, continuum_max = archimedean_continuum_galerkin(
                length, args.physical_modes, order
            )
            print(
                f"arch_continuum_order={order} "
                f"modes={args.physical_modes} "
                f"length={length:.9f} "
                f"range=[{continuum_min:+.12f},{continuum_max:+.12f}]"
            )
    print("finite_section_status=DIAGNOSTIC_ONLY")


if __name__ == "__main__":
    main()
