#!/usr/bin/env python3
"""Certificate and diagnostics for Proof 224.

The certificate section checks the nested metric-projection identity and its
Schur-complement formula on deterministic finite matrices.  It also reconstructs
the half-line metric projection and checks its exact Euler atoms.

The scattering section is deliberately diagnostic.  It forms finite sections
of the source archimedean scattering phase, selects near-intersection Sonin
modes, and reports their metric atoms and post-Q residual samples.  Those
finite sections do not certify the order of the Sonin/high-energy limits.
"""

from __future__ import annotations

import argparse
import math

import numpy as np


def orthogonal_projection(columns: np.ndarray) -> np.ndarray:
    gram = columns.conj().T @ columns
    return columns @ np.linalg.solve(gram, columns.conj().T)


def metric_projection(
    transfer: np.ndarray, basis: np.ndarray
) -> np.ndarray:
    return orthogonal_projection(transfer @ basis)


def deterministic_unitary(size: int) -> np.ndarray:
    phases = np.exp(
        2j * np.pi * (np.arange(size, dtype=float) ** 2 + 3) / size
    )
    fourier = np.fft.fft(np.eye(size), axis=0) / math.sqrt(size)
    return fourier.conj().T @ (phases[:, None] * fourier)


def nested_projection_certificate(parameter: float) -> dict[str, float]:
    size = 24
    outer_rank = 15
    inner_rank = 8
    identity = np.eye(size, dtype=complex)
    outer_basis = identity[:, :outer_rank]
    inner_basis = outer_basis[:, :inner_rank]
    outer = outer_basis @ outer_basis.conj().T
    inner = inner_basis @ inner_basis.conj().T
    complement = outer - inner

    unitary = deterministic_unitary(size)
    transfer = identity - parameter * unitary
    metric = transfer.conj().T @ transfer
    outer_metric = metric_projection(transfer, outer_basis)
    inner_metric = metric_projection(transfer, inner_basis)
    moved_complement = outer_metric - inner_metric

    nested_error = np.linalg.norm(
        inner_metric - outer_metric @ inner_metric, ord=2
    )
    decomposition_error = np.linalg.norm(
        (inner_metric - inner)
        - (
            (outer_metric - outer)
            - (moved_complement - complement)
        ),
        ord=2,
    )

    block_a = inner_basis.conj().T @ metric @ inner_basis
    complement_basis = outer_basis[:, inner_rank:outer_rank]
    block_c = inner_basis.conj().T @ metric @ complement_basis
    block_d = complement_basis.conj().T @ metric @ complement_basis
    schur = block_d - block_c.conj().T @ np.linalg.solve(
        block_a, block_c
    )
    correction = inner_basis @ np.linalg.solve(block_a, block_c)
    z_map = complement_basis - correction
    graph = transfer @ z_map
    schur_projection = graph @ np.linalg.solve(schur, graph.conj().T)
    schur_error = np.linalg.norm(
        schur_projection - moved_complement, ord=2
    )

    # A commuting test multiplier makes the cyclic trace identity exact.
    test = unitary + 0.3 * unitary.conj().T + 0.2 * identity
    direct_left = np.trace(test @ (inner_metric - inner))
    compressed = inner_basis.conj().T @ metric @ inner_basis
    off_diagonal = (identity - inner) @ metric @ inner_basis
    direct_right = np.trace(
        inner_basis.conj().T
        @ test
        @ off_diagonal
        @ np.linalg.inv(compressed)
    )
    trace_error = abs(direct_left - direct_right)

    return {
        "nested_error": float(nested_error),
        "decomposition_error": float(decomposition_error),
        "schur_error": float(schur_error),
        "trace_error": float(trace_error),
    }


def finite_shift(size: int, displacement: int) -> np.ndarray:
    shift = np.zeros((size, size), dtype=complex)
    for source in range(displacement, size):
        shift[source - displacement, source] = 1.0
    return shift


def halfline_atom_ratios(
    parameter: float, cells_per_prime: int, exponents: int
) -> list[float]:
    size = 64 * cells_per_prime
    center = size // 2
    positive_basis = np.eye(size, dtype=complex)[:, center:]
    positive = positive_basis @ positive_basis.conj().T
    shift = finite_shift(size, cells_per_prime)
    transfer = np.eye(size, dtype=complex) - parameter * shift
    difference = metric_projection(transfer, positive_basis) - positive
    return [
        float(
            (
                np.trace(difference, offset=exponent * cells_per_prime)
                / (
                    -cells_per_prime * parameter**exponent
                )
            ).real
        )
        for exponent in range(1, exponents + 1)
    ]


def log_gamma_lanczos(values: np.ndarray) -> np.ndarray:
    coefficients = np.array(
        [
            0.99999999999980993,
            676.5203681218851,
            -1259.1392167224028,
            771.32342877765313,
            -176.61502916214059,
            12.507343278686905,
            -0.13857109526572012,
            9.9843695780195716e-6,
            1.5056327351493116e-7,
        ]
    )
    shifted = values - 1
    series = np.full_like(values, coefficients[0], dtype=complex)
    for index, coefficient in enumerate(coefficients[1:], start=1):
        series += coefficient / (shifted + index)
    tail = shifted + 7.5
    return (
        0.5 * np.log(2 * np.pi)
        + (shifted + 0.5) * np.log(tail)
        - tail
        + np.log(series)
    )


def scattering_section(
    prime: int,
    cells_per_prime: int,
    intersection_tolerance: float,
    modulations: list[float],
) -> tuple[int, list[float], list[float]]:
    cell_length = math.log(prime)
    parameter = 1.0 / math.sqrt(prime)
    size = 64 * cells_per_prime
    step = cell_length / cells_per_prime
    coordinates = (np.arange(size) - size // 2) * step
    frequencies = 2 * np.pi * np.fft.fftfreq(size, d=step)

    gamma_arguments = 0.25 + 0.5j * frequencies
    log_gamma = log_gamma_lanczos(gamma_arguments)
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
    angle = (angle + angle.conj().T) / 2
    eigenvalues, eigenvectors = np.linalg.eigh(angle)
    selected = eigenvalues > 1.0 - intersection_tolerance

    sonin_basis = np.zeros((size, int(selected.sum())), dtype=complex)
    sonin_basis[positive_indices, :] = eigenvectors[:, selected]
    sonin = sonin_basis @ sonin_basis.conj().T

    shift = finite_shift(size, cells_per_prime)
    transfer = np.eye(size, dtype=complex) - parameter * shift
    sonin_difference = metric_projection(transfer, sonin_basis) - sonin

    positive = positive_basis @ positive_basis.conj().T
    halfline_difference = (
        metric_projection(transfer, positive_basis) - positive
    )
    residual = sonin_difference - halfline_difference

    atom_ratios = [
        float(
            (
                np.trace(
                    sonin_difference,
                    offset=exponent * cells_per_prime,
                )
                / (
                    -cells_per_prime * parameter**exponent
                )
            ).real
        )
        for exponent in range(1, 4)
    ]

    root_size = max(4, int(0.75 * cells_per_prime))
    residual_toeplitz = np.empty((root_size, root_size), dtype=complex)
    for row in range(root_size):
        for column in range(root_size):
            residual_toeplitz[row, column] = np.trace(
                residual, offset=column - row
            )

    root_points = np.arange(1, root_size + 1) * step
    envelope = np.sin(
        np.pi * np.arange(1, root_size + 1) / (root_size + 1)
    )
    post_q_values = []
    for modulation in modulations:
        root = envelope * np.exp(1j * modulation * root_points)
        root /= math.sqrt(step * float(np.vdot(root, root).real))
        q_root = np.empty(root_size, dtype=complex)
        q_root[1:-1] = (
            (root[2:] - root[:-2]) / (2 * step) + 0.5 * root[1:-1]
        )
        q_root[0] = root[1] / (2 * step) + 0.5 * root[0]
        q_root[-1] = -root[-2] / (2 * step) + 0.5 * root[-1]
        value = step**2 * np.vdot(
            q_root, residual_toeplitz @ q_root
        )
        post_q_values.append(float(value.real))

    return int(selected.sum()), atom_ratios, post_q_values


def parse_integers(raw: str) -> list[int]:
    return [int(item.strip()) for item in raw.split(",") if item.strip()]


def parse_floats(raw: str) -> list[float]:
    return [float(item.strip()) for item in raw.split(",") if item.strip()]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--prime", type=int, default=2)
    parser.add_argument("--cells", default="8,12,16,20")
    parser.add_argument("--modulations", default="0,5,10,20,30")
    parser.add_argument("--intersection-tolerance", type=float, default=1e-10)
    parser.add_argument("--max-algebra-error", type=float, default=1e-10)
    args = parser.parse_args()

    if args.prime < 2:
        raise ValueError("prime must be at least 2")
    cells = parse_integers(args.cells)
    modulations = parse_floats(args.modulations)
    if not cells or min(cells) < 4:
        raise ValueError("cells must contain integers at least 4")

    parameter = 1.0 / math.sqrt(args.prime)
    errors = nested_projection_certificate(parameter)
    print("identity=metric-Sonin nested-complement remainder")
    for name, value in errors.items():
        print(f"{name}={value:.3e}")
    if max(errors.values()) > args.max_algebra_error:
        raise RuntimeError("nested projection certificate failed")

    halfline_ratios = halfline_atom_ratios(parameter, max(cells), 3)
    print(
        "halfline_atom_ratios="
        + ",".join(f"{value:.12f}" for value in halfline_ratios)
    )
    if max(abs(value - 1.0) for value in halfline_ratios) > 1e-8:
        raise RuntimeError("half-line atom certificate failed")

    print("scattering_layer=DIAGNOSTIC_ONLY")
    print("modulations=" + ",".join(f"{value:g}" for value in modulations))
    for cell_count in cells:
        rank, atom_ratios, post_q_values = scattering_section(
            args.prime,
            cell_count,
            args.intersection_tolerance,
            modulations,
        )
        print(
            f"cells={cell_count} near_sonin_rank={rank} "
            "atom_ratios="
            + ",".join(f"{value:.9f}" for value in atom_ratios)
            + " post_q_residual="
            + ",".join(f"{value:+.9f}" for value in post_q_values)
        )

    print("certificate=PASS")
    print("compactness_verdict=OPEN")
    print("sign_verdict=OPEN")


if __name__ == "__main__":
    main()
