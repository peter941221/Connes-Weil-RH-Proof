#!/usr/bin/env python3
"""Quantitative first screen for a coupled Fourier-Mellin control frame.

The ordinary CC20 compact kernel is evaluated on a smooth Dirichlet Galerkin
space.  Pure-imaginary Mellin rows are then added until the shifted compact
form is negative on their common kernel.  A separate smooth bump-Fourier
space measures the interpolation cost of imposing those rows together with a
synthetic off-critical-line functional-equation orbit.

The synthetic orbit tests interpolation geometry only.  It is not asserted to
be a zeta-zero orbit, and this script does not model the finite-S correction.
"""

from __future__ import annotations

import argparse
import importlib.util
import math
from pathlib import Path

import numpy as np


def load_proof_239():
    path = Path(__file__).with_name("239_finite_s_constrained_sign_probe.py")
    spec = importlib.util.spec_from_file_location("proof_239", path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path.name}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


PROOF_239 = load_proof_239()


def parse_integers(raw: str) -> list[int]:
    return [int(value.strip()) for value in raw.split(",") if value.strip()]


def quadrature_on_symmetric_interval(
    length: float, order: int
) -> tuple[np.ndarray, np.ndarray]:
    nodes, weights = np.polynomial.legendre.leggauss(order)
    return 0.5 * length * nodes, 0.5 * length * weights


def dirichlet_sine_basis(
    points: np.ndarray, length: float, mode_count: int
) -> np.ndarray:
    mode_indices = np.arange(1, mode_count + 1, dtype=float)
    shifted = points + 0.5 * length
    return math.sqrt(2.0 / length) * np.sin(
        math.pi * np.outer(shifted, mode_indices) / length
    )


def ordinary_cc20_galerkin(
    length: float, mode_count: int, quadrature_order: int
) -> tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray]:
    points, weights = quadrature_on_symmetric_interval(
        length, quadrature_order
    )
    basis = dirichlet_sine_basis(points, length, mode_count)
    distances = np.abs(points[:, None] - points[None, :])
    kernel = PROOF_239.cc20_q_delta_regular(
        distances.reshape(-1)
    ).reshape(quadrature_order, quadrature_order)
    weighted_basis = weights[:, None] * basis
    compact = weighted_basis.T @ kernel @ weighted_basis
    compact = (compact + compact.T) / 2.0
    hermitian_error = float(np.linalg.norm(compact - compact.T, ord=2))
    if hermitian_error > 1e-10:
        raise RuntimeError(f"compact matrix is not symmetric: {hermitian_error}")
    return compact.astype(complex), points, weights, basis.astype(complex)


def mellin_rows_from_basis(
    nodes: list[complex],
    points: np.ndarray,
    weights: np.ndarray,
    basis: np.ndarray,
) -> np.ndarray:
    exponentials = np.exp(np.outer(np.asarray(nodes, dtype=complex), points))
    return (exponentials * weights[None, :]) @ basis


def numerical_nullspace(
    rows: np.ndarray, tolerance: float = 1e-11
) -> tuple[np.ndarray, np.ndarray, int]:
    if rows.shape[0] == 0:
        return np.eye(rows.shape[1], dtype=complex), np.array([]), 0
    _left, singular_values, right_h = np.linalg.svd(
        rows, full_matrices=True
    )
    scale = singular_values[0] if singular_values.size else 1.0
    rank = int(np.sum(singular_values > tolerance * scale))
    return right_h.conj().T[:, rank:], singular_values, rank


def constrained_maximum(
    operator: np.ndarray, rows: np.ndarray
) -> tuple[float, np.ndarray, int, int]:
    kernel, singular_values, rank = numerical_nullspace(rows)
    if kernel.shape[1] == 0:
        return -math.inf, singular_values, rank, 0
    compressed = kernel.conj().T @ operator @ kernel
    compressed = (compressed + compressed.conj().T) / 2.0
    return (
        float(np.linalg.eigvalsh(compressed)[-1]),
        singular_values,
        rank,
        kernel.shape[1],
    )


def control_nodes(length: float, radius: int) -> list[complex]:
    nodes = [0.0 + 0.0j, 1.0 + 0.0j]
    for frequency_index in range(1, radius + 1):
        frequency = 2.0 * math.pi * frequency_index / length
        nodes.extend([1j * frequency, -1j * frequency])
    return nodes


def find_control_radius(
    compact: np.ndarray,
    points: np.ndarray,
    weights: np.ndarray,
    basis: np.ndarray,
    length: float,
    margin: float,
    maximum_radius: int,
) -> dict[str, float | int | bool | list[complex]]:
    return find_control_radius_with_free_dimension(
        compact,
        points,
        weights,
        basis,
        length,
        margin,
        maximum_radius,
        1,
    )


def find_control_radius_with_free_dimension(
    compact: np.ndarray,
    points: np.ndarray,
    weights: np.ndarray,
    basis: np.ndarray,
    length: float,
    margin: float,
    maximum_radius: int,
    minimum_free_dimension: int,
) -> dict[str, float | int | list[complex]]:
    shifted = compact - 2.0 * np.eye(compact.shape[0], dtype=complex)
    best: dict[str, float | int | list[complex]] | None = None
    for radius in range(maximum_radius + 1):
        nodes = control_nodes(length, radius)
        rows = mellin_rows_from_basis(nodes, points, weights, basis)
        row_norms = np.linalg.norm(rows, axis=1)
        if np.any(row_norms == 0.0):
            raise RuntimeError("encountered a zero Mellin row")
        normalized_rows = rows / row_norms[:, None]
        maximum, singular_values, rank, free_dimension = constrained_maximum(
            shifted, normalized_rows
        )
        if free_dimension < minimum_free_dimension:
            break
        nonzero = singular_values[:rank]
        smallest = float(nonzero[-1]) if nonzero.size else 0.0
        condition = (
            float(nonzero[0] / nonzero[-1]) if nonzero.size else math.inf
        )
        best = {
            "radius": radius,
            "node_count": len(nodes),
            "row_rank": rank,
            "smallest_singular": smallest,
            "row_condition": condition,
            "constrained_max": maximum,
            "free_dimension": free_dimension,
            "controlled": maximum <= -margin,
            "nodes": nodes,
        }
        if maximum <= -margin:
            return best
    if best is None:
        raise RuntimeError("control-radius search did not run")
    return best


def smooth_bump(unit_points: np.ndarray) -> np.ndarray:
    values = np.zeros_like(unit_points)
    interior = (0.0 < unit_points) & (unit_points < 1.0)
    u = unit_points[interior]
    values[interior] = np.exp(-1.0 / (u * (1.0 - u)))
    return values


def orthonormal_bump_fourier_basis(
    points: np.ndarray,
    weights: np.ndarray,
    length: float,
    frequency_radius: int,
) -> tuple[np.ndarray, float]:
    unit_points = points / length + 0.5
    envelope = smooth_bump(unit_points)
    indices = np.arange(-frequency_radius, frequency_radius + 1)
    raw = envelope[:, None] * np.exp(
        2j * math.pi * np.outer(unit_points, indices)
    )
    weighted = np.sqrt(weights)[:, None] * raw
    q_matrix, r_matrix = np.linalg.qr(weighted, mode="reduced")
    if np.linalg.matrix_rank(r_matrix) != r_matrix.shape[0]:
        raise RuntimeError("bump-Fourier basis lost rank")
    physical = q_matrix / np.sqrt(weights)[:, None]
    gram_error = float(
        np.linalg.norm(
            physical.conj().T @ (weights[:, None] * physical)
            - np.eye(physical.shape[1]),
            ord=2,
        )
    )
    return physical, gram_error


def deduplicate_constraints(
    nodes: list[complex], values: list[complex], tolerance: float = 1e-10
) -> tuple[list[complex], list[complex]]:
    unique_nodes: list[complex] = []
    unique_values: list[complex] = []
    for node, value in zip(nodes, values, strict=True):
        match = next(
            (
                index
                for index, existing in enumerate(unique_nodes)
                if abs(node - existing) <= tolerance
            ),
            None,
        )
        if match is None:
            unique_nodes.append(node)
            unique_values.append(value)
        elif abs(unique_values[match] - value) > tolerance:
            raise RuntimeError("incompatible values at a collided node")
    return unique_nodes, unique_values


def correction_interpolation_probe(
    length: float,
    master_index: int,
    control_mellin_nodes: list[complex],
    target: complex,
    quadrature_order: int,
    extra_modes: int,
    tail_start: float,
    tail_end: float,
    tail_samples: int,
    contraction: float,
) -> dict[str, float | int | bool]:
    source_orbit = [
        target,
        1.0 - target.conjugate(),
        target.conjugate(),
        1.0 - target,
    ]
    orbit_values = [1.0 + 0.0j, -1.0 + 0.0j, 0.0j, 0.0j]
    shifted_control_nodes = [node + 0.5 for node in control_mellin_nodes]
    nodes, values = deduplicate_constraints(
        source_orbit + shifted_control_nodes,
        orbit_values + [0.0j] * len(shifted_control_nodes),
    )

    target_frequency = abs(target.imag) * length / (2.0 * math.pi)
    minimum_columns = len(nodes) + extra_modes
    frequency_radius = max(
        math.ceil(target_frequency) + extra_modes,
        math.ceil((minimum_columns - 1) / 2),
    )
    points, weights = quadrature_on_symmetric_interval(
        length, quadrature_order
    )
    basis, gram_error = orthonormal_bump_fourier_basis(
        points, weights, length, frequency_radius
    )
    evaluation = mellin_rows_from_basis(nodes, points, weights, basis)
    singular_values = np.linalg.svd(evaluation, compute_uv=False)
    rank_tolerance = 1e-11 * singular_values[0]
    rank = int(np.sum(singular_values > rank_tolerance))
    full_row_rank = rank == len(nodes)
    coefficients = np.linalg.lstsq(
        evaluation, np.asarray(values, dtype=complex), rcond=1e-12
    )[0]
    residual = float(
        np.linalg.norm(evaluation @ coefficients - np.asarray(values))
    )
    correction_values = basis @ coefficients

    positive_heights = np.geomspace(tail_start, tail_end, tail_samples)
    heights = np.concatenate([-positive_heights[::-1], positive_heights])
    tail_proxy = 0.0
    for sigma in (0.0, 0.5, 1.0):
        spectral_nodes = sigma + 1j * heights
        transforms = (
            np.exp(np.outer(spectral_nodes, points))
            * weights[None, :]
        ) @ correction_values
        weighted = (np.abs(heights) / (2.0 * math.pi)) ** 2 * np.abs(
            transforms
        )
        tail_proxy = max(tail_proxy, float(np.max(weighted)))

    smallest = float(singular_values[-1])
    right_inverse = 1.0 / smallest if full_row_rank else math.inf
    weighted_tail = (
        contraction ** (master_index + 1) * tail_proxy
        if full_row_rank
        else math.inf
    )
    return {
        "constraint_count": len(nodes),
        "interpolation_rank": rank,
        "full_row_rank": full_row_rank,
        "correction_dimension": basis.shape[1],
        "frequency_radius": frequency_radius,
        "gram_error": gram_error,
        "interpolation_residual": residual,
        "smallest_singular": smallest,
        "right_inverse_norm": right_inverse,
        "solution_norm": float(np.linalg.norm(coefficients)),
        "tail_proxy": tail_proxy,
        "weighted_tail_proxy": weighted_tail,
    }


def diagnostic_line(
    master_index: int,
    length: float,
    mode_count: int,
    compact: np.ndarray,
    control: dict[str, float | int | list[complex]],
) -> str:
    eigenvalues = np.linalg.eigvalsh(compact)
    bad_dimension = int(np.sum(eigenvalues > 2.0))
    return " ".join(
        [
            f"N={master_index}",
            f"length={length:.9f}",
            f"modes={mode_count}",
            f"compact_top={eigenvalues[-1]:+.9f}",
            f"bad_dim={bad_dimension}",
            f"control_radius={control['radius']}",
            f"control_rank={control['row_rank']}",
            f"control_sigma_min={control['smallest_singular']:.3e}",
            f"control_condition={control['row_condition']:.3e}",
            f"free_dim={control['free_dimension']}",
            f"controlled={str(control['controlled']).lower()}",
            f"controlled_max={control['constrained_max']:+.9f}",
        ]
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--master-indices", default="1,2,3,4,5,6")
    parser.add_argument("--modes", default="16,24,32")
    parser.add_argument("--cell-length", type=float, default=math.log(2.0))
    parser.add_argument("--quadrature-order", type=int, default=224)
    parser.add_argument("--maximum-control-radius", type=int, default=12)
    parser.add_argument("--minimum-free-dimension", type=int, default=6)
    parser.add_argument("--sign-margin", type=float, default=0.05)
    parser.add_argument("--target-real", type=float, default=0.4)
    parser.add_argument("--target-imag", type=float, default=14.134725141734695)
    parser.add_argument("--correction-extra-modes", type=int, default=6)
    parser.add_argument("--tail-start", type=float, default=30.0)
    parser.add_argument("--tail-end", type=float, default=120.0)
    parser.add_argument("--tail-samples", type=int, default=80)
    parser.add_argument("--contraction", type=float, default=0.5)
    parser.add_argument("--skip-interpolation", action="store_true")
    args = parser.parse_args()

    master_indices = parse_integers(args.master_indices)
    mode_counts = parse_integers(args.modes)
    if not master_indices or min(master_indices) < 1:
        raise ValueError("master indices must be positive")
    if not mode_counts or min(mode_counts) < 4:
        raise ValueError("mode counts must be at least four")
    if args.quadrature_order <= max(mode_counts):
        raise ValueError("quadrature order must exceed the largest mode count")
    if not 0.0 < args.contraction < 1.0:
        raise ValueError("contraction must lie in (0,1)")
    if args.tail_start <= 0.0 or args.tail_end <= args.tail_start:
        raise ValueError("tail interval must satisfy 0 < start < end")

    target = complex(args.target_real, args.target_imag)
    maximum_modes = max(mode_counts)
    weighted_proxies: list[tuple[int, float]] = []
    every_largest_space_controlled = True
    every_interpolation_valid = True
    print("probe=quantitative Fourier-Mellin control")
    print("owner=ordinary continuous CC20 compact kernel")
    print("finite_S_correction=NOT_INCLUDED")
    print(
        "target_geometry="
        f"synthetic({target.real:+.6f}{target.imag:+.6f}i)"
    )
    print(
        "coupled_gate=q^(N+1)*tail_proxy "
        f"q={args.contraction:.6f}"
    )

    for master_index in master_indices:
        length = master_index * args.cell_length
        compact, points, weights, full_basis = ordinary_cc20_galerkin(
            length, maximum_modes, args.quadrature_order
        )
        largest_control: (
            dict[str, float | int | bool | list[complex]] | None
        ) = None
        for mode_count in mode_counts:
            basis = full_basis[:, :mode_count]
            mode_compact = compact[:mode_count, :mode_count]
            control = find_control_radius_with_free_dimension(
                mode_compact,
                points,
                weights,
                basis,
                length,
                args.sign_margin,
                min(args.maximum_control_radius, (mode_count - 2) // 2),
                args.minimum_free_dimension,
            )
            print(
                diagnostic_line(
                    master_index,
                    length,
                    mode_count,
                    mode_compact,
                    control,
                )
            )
            if mode_count == maximum_modes:
                largest_control = control

        if largest_control is None:
            raise RuntimeError("largest Galerkin control result is missing")
        every_largest_space_controlled = (
            every_largest_space_controlled and bool(largest_control["controlled"])
        )
        if args.skip_interpolation:
            print(f"coupled_N={master_index} interpolation=SKIPPED")
            continue
        interpolation = correction_interpolation_probe(
            length,
            master_index,
            largest_control["nodes"],  # type: ignore[arg-type]
            target,
            args.quadrature_order,
            args.correction_extra_modes,
            args.tail_start,
            args.tail_end,
            args.tail_samples,
            args.contraction,
        )
        weighted_proxies.append(
            (master_index, float(interpolation["weighted_tail_proxy"]))
        )
        every_interpolation_valid = every_interpolation_valid and bool(
            interpolation["full_row_rank"]
        )
        print(
            " ".join(
                [
                    f"coupled_N={master_index}",
                    f"constraints={interpolation['constraint_count']}",
                    f"interpolation_rank={interpolation['interpolation_rank']}",
                    f"full_row_rank={str(interpolation['full_row_rank']).lower()}",
                    f"correction_dim={interpolation['correction_dimension']}",
                    f"correction_radius={interpolation['frequency_radius']}",
                    f"gram_error={interpolation['gram_error']:.3e}",
                    f"interpolation_residual={interpolation['interpolation_residual']:.3e}",
                    f"interpolation_sigma_min={interpolation['smallest_singular']:.3e}",
                    f"right_inverse={interpolation['right_inverse_norm']:.3e}",
                    f"solution_norm={interpolation['solution_norm']:.3e}",
                    f"tail_proxy={interpolation['tail_proxy']:.3e}",
                    f"q_weighted_tail={interpolation['weighted_tail_proxy']:.3e}",
                ]
            )
        )

    if len(weighted_proxies) >= 3:
        tail = weighted_proxies[len(weighted_proxies) // 2 :]
        indices = np.asarray([item[0] for item in tail], dtype=float)
        values = np.asarray(
            [max(item[1], np.finfo(float).tiny) for item in tail], dtype=float
        )
        slope = float(np.polyfit(indices, np.log(values), 1)[0])
        print(f"weighted_tail_log_slope={slope:+.9f}")
        if not every_interpolation_valid:
            growth_status = "RANK_DEFICIENT_INTERPOLATION_DIAGNOSTIC"
        elif not every_largest_space_controlled:
            growth_status = "INCOMPLETE_CONTROL_DIAGNOSTIC"
        elif slope < 0.0:
            growth_status = "FAVORABLE_DIAGNOSTIC"
        else:
            growth_status = "UNFAVORABLE_DIAGNOSTIC"
        print(f"coupled_growth_status={growth_status}")
    print("route_status=DIAGNOSTIC_ONLY")


if __name__ == "__main__":
    main()
