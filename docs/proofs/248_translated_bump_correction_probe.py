#!/usr/bin/env python3
"""Support-coupled translated-bump interpolation for the Yoshida correction.

The correction is a finite sum of disjoint translates of one normalized
smooth bump.  The raw bump is preweighted by ``exp(-x/2)``, so the selected
half-density source is an ordinary translate.  On the critical Mellin lattice
its evaluation matrix is therefore a smooth scalar factor times a Fourier
matrix, without the spurious ``exp(a_j/2)`` column weight.

The Fourier period is the full support envelope after convolution:

    final span = (N + 1) * base span + correction span.

This accounting is essential.  Using only the correction span understates the
number of low Fourier rows and can turn a rank-deficient interpolation into a
false favorable diagnostic.

The off-critical-line orbit is synthetic and used only as a geometry stress
test.  Finite sampling of the vertical tail is diagnostic, not a proof.
"""

from __future__ import annotations

import argparse
import importlib.util
import math
from pathlib import Path

import numpy as np


def load_module(filename: str, module_name: str):
    path = Path(__file__).with_name(filename)
    spec = importlib.util.spec_from_file_location(module_name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path.name}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


PROOF_245 = load_module(
    "245_quantitative_fourier_control_probe.py", "proof_245"
)


def parse_integers(raw: str) -> list[int]:
    return [int(value.strip()) for value in raw.split(",") if value.strip()]


def normalized_compact_bump(
    width: float, quadrature_order: int
) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    nodes, weights = np.polynomial.legendre.leggauss(quadrature_order)
    points = 0.5 * width * (nodes + 1.0)
    weights = 0.5 * width * weights
    unit_points = points / width
    values = PROOF_245.smooth_bump(unit_points)
    norm = math.sqrt(float(np.sum(weights * values**2)))
    if norm == 0.0:
        raise RuntimeError("compact bump has zero norm")
    return points, weights, values / norm


def bump_laplace(
    spectral_nodes: np.ndarray,
    points: np.ndarray,
    weights: np.ndarray,
    values: np.ndarray,
) -> np.ndarray:
    return (
        np.exp(np.outer(spectral_nodes, points))
        * weights[None, :]
    ) @ values


def translated_bump_matrix(
    spectral_nodes: np.ndarray,
    centers: np.ndarray,
    bump_transform: np.ndarray,
) -> np.ndarray:
    return bump_transform[:, None] * np.exp(
        np.outer(spectral_nodes, centers)
    )


def half_density_translated_bump_matrix(
    source_nodes: np.ndarray,
    centers: np.ndarray,
    bump_points: np.ndarray,
    bump_weights: np.ndarray,
    bump_values: np.ndarray,
) -> np.ndarray:
    """Evaluate raw ``exp(-x/2)``-weighted bump translates.

    After the project's half-density shift, ``source_nodes - 1/2`` is the
    centered Fourier variable.  This makes the low critical-line block an
    exact sampled Fourier matrix up to the common bump transform.
    """

    centered_nodes = source_nodes - 0.5
    bump_transform = bump_laplace(
        centered_nodes, bump_points, bump_weights, bump_values
    )
    return translated_bump_matrix(centered_nodes, centers, bump_transform)


def coupled_constraints(
    length: float,
    vertical_threshold: float,
    target: complex,
) -> tuple[list[complex], list[complex], int]:
    low_radius = math.ceil(vertical_threshold * length / (2.0 * math.pi))
    control_nodes = PROOF_245.control_nodes(length, low_radius)
    shifted_control = [node + 0.5 for node in control_nodes]
    source_orbit = [
        target,
        1.0 - target.conjugate(),
        target.conjugate(),
        1.0 - target,
    ]
    nodes, values = PROOF_245.deduplicate_constraints(
        source_orbit + shifted_control,
        [1.0 + 0.0j, -1.0 + 0.0j, 0.0j, 0.0j]
        + [0.0j] * len(shifted_control),
    )
    return nodes, values, low_radius


def one_probe(
    master_index: int,
    cell_length: float,
    correction_span_ratio: float,
    vertical_threshold: float,
    target: complex,
    extra_columns: int,
    fill_fraction: float,
    bump_quadrature_order: int,
    tail_end: float,
    tail_samples: int,
    contraction: float,
) -> dict[str, float | int | bool]:
    base_span = (master_index + 1) * cell_length
    correction_span = correction_span_ratio * master_index * cell_length
    final_span = base_span + correction_span
    nodes, values, low_radius = coupled_constraints(
        final_span, vertical_threshold, target
    )
    column_count = len(nodes) + extra_columns
    nominal_spacing = correction_span / column_count
    bump_width = fill_fraction * nominal_spacing
    center_spacing = nominal_spacing
    centers = (
        -0.5 * correction_span
        + center_spacing * np.arange(column_count)
    )
    if bump_width >= center_spacing:
        raise RuntimeError("translated bumps are not disjoint")

    bump_points, bump_weights, bump_values = normalized_compact_bump(
        bump_width, bump_quadrature_order
    )
    spectral_nodes = np.asarray(nodes, dtype=complex)
    matrix = half_density_translated_bump_matrix(
        spectral_nodes,
        centers,
        bump_points,
        bump_weights,
        bump_values,
    )
    singular_values = np.linalg.svd(matrix, compute_uv=False)
    rank = int(np.sum(singular_values > 1e-11 * singular_values[0]))
    full_row_rank = rank == len(nodes)
    coefficients = np.linalg.lstsq(
        matrix, np.asarray(values, dtype=complex), rcond=1e-12
    )[0]
    residual = float(
        np.linalg.norm(matrix @ coefficients - np.asarray(values))
    )

    positive_heights = np.geomspace(
        vertical_threshold, tail_end, tail_samples
    )
    heights = np.concatenate([-positive_heights[::-1], positive_heights])
    tail_proxy = 0.0
    contraction_sup = 0.0
    for sigma in (0.0, 0.25, 0.5, 0.75, 1.0):
        tail_nodes = sigma + 1j * heights
        tail_matrix = half_density_translated_bump_matrix(
            tail_nodes,
            centers,
            bump_points,
            bump_weights,
            bump_values,
        )
        transforms = tail_matrix @ coefficients
        contraction_sup = max(contraction_sup, float(np.max(np.abs(transforms))))
        weighted = (np.abs(heights) / (2.0 * math.pi)) ** 2 * np.abs(
            transforms
        )
        tail_proxy = max(tail_proxy, float(np.max(weighted)))

    assembled_tail = (
        contraction ** (master_index + 1) * tail_proxy
        if full_row_rank
        else math.inf
    )
    return {
        "base_span": base_span,
        "correction_span": correction_span,
        "final_span": final_span,
        "correction_fraction": correction_span / final_span,
        "missing_time_bandwidth": vertical_threshold * base_span,
        "low_radius": low_radius,
        "constraint_count": len(nodes),
        "column_count": column_count,
        "rank": rank,
        "full_row_rank": full_row_rank,
        "bump_width": bump_width,
        "center_spacing": center_spacing,
        "smallest_singular": float(singular_values[-1]),
        "condition": float(singular_values[0] / singular_values[-1]),
        "residual": residual,
        "coefficient_norm": float(np.linalg.norm(coefficients)),
        "contraction_sup": contraction_sup,
        "tail_proxy": tail_proxy,
        "assembled_tail": assembled_tail,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--master-indices", default="1,2,3,4,5,6,8,10")
    parser.add_argument("--cell-length", type=float, default=math.log(2.0))
    parser.add_argument("--correction-span-ratio", type=float, default=1.0)
    parser.add_argument("--vertical-threshold", type=float, default=30.0)
    parser.add_argument("--target-real", type=float, default=0.4)
    parser.add_argument("--target-imag", type=float, default=14.134725141734695)
    parser.add_argument("--extra-columns", type=int, default=8)
    parser.add_argument("--fill-fraction", type=float, default=0.6)
    parser.add_argument("--bump-quadrature-order", type=int, default=192)
    parser.add_argument("--tail-end", type=float, default=240.0)
    parser.add_argument("--tail-samples", type=int, default=96)
    parser.add_argument("--contraction", type=float, default=0.04)
    args = parser.parse_args()

    if not 0.0 < args.fill_fraction < 1.0:
        raise ValueError("fill fraction must lie in (0,1)")
    if args.correction_span_ratio <= 0.0:
        raise ValueError("correction span ratio must be positive")
    if not 0.0 < args.contraction < 1.0:
        raise ValueError("contraction must lie in (0,1)")
    target = complex(args.target_real, args.target_imag)
    print("probe=translated-bump coupled correction")
    print(
        "target_geometry="
        f"synthetic({target.real:+.6f}{target.imag:+.6f}i)"
    )
    print(f"vertical_threshold={args.vertical_threshold:.9f}")
    print(f"contraction={args.contraction:.9f}")
    print(f"correction_span_ratio={args.correction_span_ratio:.9f}")
    assembled_values: list[tuple[int, float]] = []
    all_full_rank = True
    for master_index in parse_integers(args.master_indices):
        result = one_probe(
            master_index,
            args.cell_length,
            args.correction_span_ratio,
            args.vertical_threshold,
            target,
            args.extra_columns,
            args.fill_fraction,
            args.bump_quadrature_order,
            args.tail_end,
            args.tail_samples,
            args.contraction,
        )
        all_full_rank = all_full_rank and bool(result["full_row_rank"])
        assembled_values.append(
            (master_index, float(result["assembled_tail"]))
        )
        print(
            " ".join(
                [
                    f"N={master_index}",
                    f"base_span={result['base_span']:.9f}",
                    f"correction_span={result['correction_span']:.9f}",
                    f"final_span={result['final_span']:.9f}",
                    f"correction_fraction={result['correction_fraction']:.6f}",
                    f"missing_TL={result['missing_time_bandwidth']:.6f}",
                    f"low_radius={result['low_radius']}",
                    f"constraints={result['constraint_count']}",
                    f"columns={result['column_count']}",
                    f"rank={result['rank']}",
                    f"full_row_rank={str(result['full_row_rank']).lower()}",
                    f"bump_width={result['bump_width']:.6f}",
                    f"spacing={result['center_spacing']:.6f}",
                    f"sigma_min={result['smallest_singular']:.3e}",
                    f"condition={result['condition']:.3e}",
                    f"residual={result['residual']:.3e}",
                    f"coefficient_norm={result['coefficient_norm']:.3e}",
                    f"tail_sup={result['contraction_sup']:.3e}",
                    f"tail_proxy={result['tail_proxy']:.3e}",
                    f"assembled_tail={result['assembled_tail']:.3e}",
                ]
            )
        )

    if not all_full_rank:
        print("assembled_tail_log_slope=NOT_COMPUTED_RANK_DEFICIENT")
        print("translated_bump_status=RANK_DEFICIENT_DIAGNOSTIC")
    elif len(assembled_values) >= 3:
        tail = assembled_values[len(assembled_values) // 2 :]
        indices = np.asarray([item[0] for item in tail], dtype=float)
        values = np.asarray(
            [max(item[1], np.finfo(float).tiny) for item in tail], dtype=float
        )
        slope = float(np.polyfit(indices, np.log(values), 1)[0])
        print(f"assembled_tail_log_slope={slope:+.9f}")
        if slope < 0.0:
            status = "FAVORABLE_DIAGNOSTIC"
        else:
            status = "UNFAVORABLE_DIAGNOSTIC"
        print(f"translated_bump_status={status}")
    print("route_status=DIAGNOSTIC_ONLY")


if __name__ == "__main__":
    main()
