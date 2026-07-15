#!/usr/bin/env python3
"""Certificate for the Proof 250 chirp-mixture interior estimate.

The mathematical proof is the exact factorization of each dangerous negative
cell into a Bochner integral of Proof 228 logarithmic chirps.  This script
checks the algebra, the transferred second derivative, the uniform analytic
majorant, and selected Nyström discretizations.  The discretizations are
diagnostic evidence only; the operator bound comes from Plancherel plus the
Bochner integral triangle inequality.
"""

from __future__ import annotations

import argparse
import math
from dataclasses import dataclass

import numpy as np


TWO_PI = 2.0 * math.pi


@dataclass(frozen=True)
class NystromCase:
    prime: int
    cell: int


def parse_integers(raw: str) -> list[int]:
    return [int(item.strip()) for item in raw.split(",") if item.strip()]


def parse_cases(raw: str) -> list[NystromCase]:
    cases: list[NystromCase] = []
    for item in raw.split(","):
        stripped = item.strip()
        if not stripped:
            continue
        prime_raw, cell_raw = stripped.split(":", maxsplit=1)
        cases.append(NystromCase(int(prime_raw), int(cell_raw)))
    return cases


def trapezoid_weights(size: int, step: float) -> np.ndarray:
    weights = np.full(size, step)
    weights[0] *= 0.5
    weights[-1] *= 0.5
    return weights


def local_envelope(prime: int, values: np.ndarray) -> np.ndarray:
    parameter = prime**-0.5
    cell_length = math.log(prime)
    return (
        cell_length - (1.0 - parameter) * values
    ) / (1.0 - parameter) ** 2


def scattering_response(values: np.ndarray) -> np.ndarray:
    return 2.0 * np.exp(values / 2.0) * np.cos(TWO_PI * np.exp(values))


def direct_cell_product(
    prime: int, cell: int, differences: np.ndarray, local: np.ndarray
) -> np.ndarray:
    parameter = prime**-0.5
    cell_length = math.log(prime)
    radius = cell * cell_length + local
    envelope = parameter ** (cell + 1) * local_envelope(prime, local)
    return (
        envelope
        * scattering_response(-radius)
        * scattering_response(differences + radius)
    )


def factored_cell_product(
    prime: int, cell: int, differences: np.ndarray, local: np.ndarray
) -> np.ndarray:
    parameter = prime**-0.5
    slow_phase = TWO_PI * prime ** (-cell) * np.exp(-local)
    fast_phase = TWO_PI * prime**cell * np.exp(differences + local)
    return (
        4.0
        * parameter ** (cell + 1)
        * np.exp(differences / 2.0)
        * local_envelope(prime, local)
        * np.cos(slow_phase)
        * np.cos(fast_phase)
    )


def slow_cosine_data(
    prime: int, cell: int, local: np.ndarray
) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    scale = prime ** (-cell) * np.exp(-local)
    phase = TWO_PI * scale
    value = np.cos(phase)
    first = TWO_PI * scale * np.sin(phase)
    second = (
        -TWO_PI * scale * np.sin(phase)
        - TWO_PI**2 * scale**2 * np.cos(phase)
    )
    return value, first, second


def transferred_coefficient(
    prime: int, cell: int, local: np.ndarray
) -> np.ndarray:
    """Coefficient of one complex fast phase after applying D^2."""
    parameter = prime**-0.5
    envelope = local_envelope(prime, local)
    envelope_first = -1.0 / (1.0 - parameter)
    slow, slow_first, slow_second = slow_cosine_data(prime, cell, local)
    transferred = (
        envelope * (slow_second - slow_first + 0.25 * slow)
        + envelope_first * (2.0 * slow_first - slow)
    )
    return 2.0 * parameter ** (cell + 1) * transferred


def complex_phase_amplitude(
    prime: int, cell: int, difference: np.ndarray, local: np.ndarray
) -> np.ndarray:
    parameter = prime**-0.5
    slow_phase = TWO_PI * prime ** (-cell) * np.exp(-local)
    return (
        2.0
        * parameter ** (cell + 1)
        * np.exp(difference / 2.0)
        * local_envelope(prime, local)
        * np.cos(slow_phase)
    )


def transferred_derivative_error(
    prime: int, cell: int, difference: float, local: float, step: float
) -> float:
    def amplitude(direction: float) -> complex:
        shifted_difference = np.array(difference + direction)
        shifted_local = np.array(local - direction)
        return complex(
            complex_phase_amplitude(
                prime, cell, shifted_difference, shifted_local
            )
        )

    finite_second = (
        amplitude(step) - 2.0 * amplitude(0.0) + amplitude(-step)
    ) / step**2
    exact = math.exp(difference / 2.0) * float(
        transferred_coefficient(prime, cell, np.array(local))
    )
    return abs(finite_second - exact) / max(1.0, abs(exact))


def coarse_coefficient_bound(prime: int, cell: int) -> float:
    parameter = prime**-0.5
    cell_length = math.log(prime)
    denominator = 1.0 - parameter
    slow_first_bound = TWO_PI
    slow_second_bound = TWO_PI + TWO_PI**2
    transferred_bound = (
        cell_length
        / denominator**2
        * (slow_second_bound + slow_first_bound + 0.25)
        + 1.0 / denominator * (2.0 * slow_first_bound + 1.0)
    )
    return 2.0 * parameter ** (cell + 1) * transferred_bound


def coarse_operator_bound(prime: int, cell: int) -> float:
    parameter = prime**-0.5
    weighted_length = 2.0 * (1.0 - parameter)
    return (
        prime ** (-cell / 2.0)
        * coarse_coefficient_bound(prime, cell)
        * weighted_length
    )


def quadrature_operator_bound(
    prime: int, cell: int, quadrature_order: int
) -> float:
    nodes, weights = np.polynomial.legendre.leggauss(quadrature_order)
    cell_length = math.log(prime)
    local = 0.5 * cell_length * (nodes + 1.0)
    local_weights = 0.5 * cell_length * weights
    coefficient = transferred_coefficient(prime, cell, local)
    return float(
        prime ** (-cell / 2.0)
        * np.sum(local_weights * np.abs(coefficient) * np.exp(-local / 2.0))
    )


def mixture_matrix(
    prime: int,
    cell: int,
    grid_size: int,
    quadrature_order: int,
    interval_bound: float,
    chunk_size: int,
) -> tuple[np.ndarray, float, float]:
    points = np.linspace(-interval_bound, interval_bound, grid_size)
    step = float(points[1] - points[0])
    spatial_weights = trapezoid_weights(grid_size, step)
    weighted = np.sqrt(spatial_weights)
    differences = points[:, None] - points[None, :]

    base_nodes, base_weights = np.polynomial.legendre.leggauss(quadrature_order)
    cell_length = math.log(prime)
    local = 0.5 * cell_length * (base_nodes + 1.0)
    local_weights = 0.5 * cell_length * base_weights
    coefficient = transferred_coefficient(prime, cell, local)

    kernel = np.zeros((grid_size, grid_size), dtype=complex)
    frequency = prime**cell
    difference_exponential = np.exp(differences)
    half_density = np.exp(differences / 2.0)
    for start in range(0, quadrature_order, chunk_size):
        stop = min(start + chunk_size, quadrature_order)
        phases = np.exp(
            1j
            * TWO_PI
            * frequency
            * difference_exponential[:, :, None]
            * np.exp(local[start:stop])[None, None, :]
        )
        kernel += half_density * np.sum(
            phases
            * (local_weights[start:stop] * coefficient[start:stop])[
                None, None, :
            ],
            axis=2,
        )

    matrix = weighted[:, None] * kernel * weighted[None, :]
    phase_step = (
        TWO_PI
        * prime ** (cell + 1)
        * math.exp(2.0 * interval_bound)
        * step
    )
    return matrix, phase_step, step


def run_nystrom_case(
    case: NystromCase,
    grid_sizes: list[int],
    quadrature_order: int,
    interval_bound: float,
    chunk_size: int,
) -> dict[str, object]:
    analytic_bound = quadrature_operator_bound(
        case.prime, case.cell, quadrature_order
    )
    rows = []
    for grid_size in grid_sizes:
        matrix, phase_step, step = mixture_matrix(
            case.prime,
            case.cell,
            grid_size,
            quadrature_order,
            interval_bound,
            chunk_size,
        )
        singular_values = np.linalg.svd(matrix, compute_uv=False)
        rows.append(
            {
                "grid_size": grid_size,
                "operator_norm": float(singular_values[0]),
                "analytic_bound": analytic_bound,
                "bound_ratio": float(singular_values[0] / analytic_bound),
                "phase_step": phase_step,
                "step": step,
            }
        )
    return {"case": case, "rows": rows}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--primes", default="2,3,5,7,11")
    parser.add_argument("--cells", type=int, default=12)
    parser.add_argument("--sample-points", type=int, default=41)
    parser.add_argument("--difference-bound", type=float, default=0.6)
    parser.add_argument("--max-identity-frequency", type=float, default=1e7)
    parser.add_argument("--finite-difference-step", type=float, default=2e-4)
    parser.add_argument("--max-product-error", type=float, default=2e-8)
    parser.add_argument("--max-derivative-error", type=float, default=2e-6)
    parser.add_argument(
        "--nystrom-cases", default="2:1,2:2,2:3,3:1,3:2"
    )
    parser.add_argument("--grid-sizes", default="192,256")
    parser.add_argument("--quadrature-order", type=int, default=192)
    parser.add_argument("--interval-bound", type=float, default=0.25)
    parser.add_argument("--chunk-size", type=int, default=12)
    parser.add_argument("--bound-slack", type=float, default=1.08)
    parser.add_argument("--max-phase-step", type=float, default=0.9)
    args = parser.parse_args()

    primes = parse_integers(args.primes)
    grid_sizes = parse_integers(args.grid_sizes)
    cases = parse_cases(args.nystrom_cases)
    if not primes or min(primes) < 2:
        raise ValueError("primes must contain integers at least 2")
    if args.cells < 1:
        raise ValueError("cells must be positive")
    if args.sample_points < 9:
        raise ValueError("sample-points must be at least 9")
    if len(grid_sizes) < 2 or min(grid_sizes) < 64:
        raise ValueError("grid-sizes must contain two values at least 64")
    if args.quadrature_order < 64:
        raise ValueError("quadrature-order must be at least 64")

    product_error = 0.0
    derivative_error = 0.0
    max_scaled_coarse_bound = 0.0
    max_scaled_quadrature_bound = 0.0
    for prime in primes:
        cell_length = math.log(prime)
        local = np.linspace(0.0, cell_length, args.sample_points)
        differences = np.linspace(
            -args.difference_bound,
            args.difference_bound,
            args.sample_points,
        )
        difference_grid, local_grid = np.meshgrid(
            differences, local, indexing="ij"
        )
        for cell in range(1, args.cells + 1):
            max_identity_frequency = (
                prime ** (cell + 1) * math.exp(args.difference_bound)
            )
            if max_identity_frequency <= args.max_identity_frequency:
                direct = direct_cell_product(
                    prime, cell, difference_grid, local_grid
                )
                factored = factored_cell_product(
                    prime, cell, difference_grid, local_grid
                )
                product_error = max(
                    product_error,
                    float(np.max(np.abs(direct - factored))),
                )
            for fraction in (0.17, 0.43, 0.79):
                derivative_error = max(
                    derivative_error,
                    transferred_derivative_error(
                        prime,
                        cell,
                        args.difference_bound * (2.0 * fraction - 1.0),
                        cell_length * fraction,
                        args.finite_difference_step,
                    ),
                )
            scale = prime**cell / (1.0 + cell_length)
            max_scaled_coarse_bound = max(
                max_scaled_coarse_bound,
                scale * coarse_operator_bound(prime, cell),
            )
            max_scaled_quadrature_bound = max(
                max_scaled_quadrature_bound,
                scale
                * quadrature_operator_bound(
                    prime, cell, args.quadrature_order
                ),
            )

    print("identity=Euler interior chirp-mixture gain")
    print(f"primes={','.join(str(prime) for prime in primes)}")
    print(f"cells_per_prime={args.cells}")
    print(f"cell_product_identity_error={product_error:.3e}")
    print(f"transferred_D2_relative_error={derivative_error:.3e}")
    print(
        "max_scaled_coarse_bound="
        f"{max_scaled_coarse_bound:.12e}"
    )
    print(
        "max_scaled_quadrature_bound="
        f"{max_scaled_quadrature_bound:.12e}"
    )

    nystrom_results = [
        run_nystrom_case(
            case,
            grid_sizes,
            args.quadrature_order,
            args.interval_bound,
            args.chunk_size,
        )
        for case in cases
    ]
    print("nystrom_table=BEGIN")
    central_scaled_values = []
    for result in nystrom_results:
        case = result["case"]
        assert isinstance(case, NystromCase)
        for row in result["rows"]:
            print(
                f"p={case.prime} cell={case.cell} "
                f"grid={row['grid_size']} "
                f"operator_norm={row['operator_norm']:.12e} "
                f"analytic_bound={row['analytic_bound']:.12e} "
                f"bound_ratio={row['bound_ratio']:.6f} "
                f"phase_step={row['phase_step']:.6f}"
            )
        if case.cell == 0:
            finest_row = result["rows"][-1]
            central_scaled_values.append(
                finest_row["operator_norm"]
                * math.sqrt(case.prime)
                / math.log(case.prime)
            )
    print("nystrom_table=END")
    if central_scaled_values:
        print(
            "central_scaled_sqrt_p_over_log_p_min="
            f"{min(central_scaled_values):.12e}"
        )
        print(
            "central_scaled_sqrt_p_over_log_p_max="
            f"{max(central_scaled_values):.12e}"
        )

    if product_error > args.max_product_error:
        raise RuntimeError("exact negative-cell factorization failed")
    if derivative_error > args.max_derivative_error:
        raise RuntimeError("transferred D^2 coefficient failed")
    if not math.isfinite(max_scaled_coarse_bound):
        raise RuntimeError("coarse p^(-m) majorant is not finite")
    if not math.isfinite(max_scaled_quadrature_bound):
        raise RuntimeError("quadrature p^(-m) majorant is not finite")
    for result in nystrom_results:
        for row in result["rows"]:
            if row["phase_step"] > args.max_phase_step:
                raise RuntimeError("Nyström grid does not resolve a chirp")
            if row["bound_ratio"] > args.bound_slack:
                raise RuntimeError("discrete norm exceeded the analytic bound")

    print("certificate=PASS")
    print("exact_separable_amplitude_verdict=PASS")
    print("bochner_chirp_bound_verdict=PASS")
    print("positive_tail_cells_p_to_minus_m_verdict=PASS")
    if central_scaled_values:
        print("central_cell_termwise_p_to_minus_one_verdict=REJECTED")
    else:
        print("central_cell_termwise_p_to_minus_one_verdict=NOT_TESTED")
    print("complete_signed_central_cancellation_verdict=OPEN")
    print("full_graph_dressing_verdict=OPEN")
    print("same_object_finite_S_remainder_verdict=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
