#!/usr/bin/env python3
"""Nested Berezin decomposition of the synchronized finite-S flow.

In the Mellin coordinate the synchronized generator is multiplication by

    x_S,t(s) = -sum_p a_p exp(i s log p)
                         / (1 - t a_p exp(i s log p)).

For nested projections R_t <= E_t, put B_t=E_t-R_t.  The exact diagonal flow
has two difference-kernel pieces:

    d_t b_t(s)
      = 2 Re sum_u (x(s)-x(u)) |B_t(s,u)|^2
        + 4 Re sum_u (Re x(s)-Re x(u))
                     R_t(s,u) B_t(u,s).

The script verifies this identity against the direct projection derivative,
checks invariance under adding a scalar to x, and integrates both components
on Proof 251's fixed compact four-mode pre-root.  The Fourier section is a
diagnostic; it is not a continuous-kernel estimate or a sign theorem.
"""

from __future__ import annotations

import argparse
import importlib.util
import math
from pathlib import Path
from types import ModuleType

import numpy as np


def load_proof_252() -> ModuleType:
    path = Path(__file__).with_name(
        "252_synchronized_finite_s_logarithmic_flow_probe.py"
    )
    spec = importlib.util.spec_from_file_location("proof_252", path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path.name}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


PROOF_252 = load_proof_252()
PROOF_251 = PROOF_252.PROOF_251


def to_fourier_coordinate(matrix: np.ndarray) -> np.ndarray:
    """Return F matrix F*, with the unitary discrete Fourier matrix F."""
    return np.fft.ifft(np.fft.fft(matrix, axis=0), axis=1)


def generator_multiplier(
    factors: list[dict[str, object]], parameter: float
) -> np.ndarray:
    multiplier = np.zeros(
        len(np.asarray(factors[0]["multiplier"])), dtype=complex
    )
    for factor in factors:
        amplitude = float(factor["amplitude"])
        translation = np.asarray(factor["multiplier"])
        multiplier -= (
            amplitude
            * translation
            / (1.0 - parameter * amplitude * translation)
        )
    return multiplier


def berezin_density(
    projection: np.ndarray, multiplier: np.ndarray
) -> np.ndarray:
    difference = multiplier[:, None] - multiplier[None, :]
    return 2.0 * np.real(
        np.sum(difference * np.abs(projection) ** 2, axis=1)
    )


def nested_berezin_components(
    inner_projection: np.ndarray,
    band_projection: np.ndarray,
    multiplier: np.ndarray,
) -> tuple[np.ndarray, np.ndarray]:
    difference = multiplier[:, None] - multiplier[None, :]
    band_variance = 2.0 * np.real(
        np.sum(difference * np.abs(band_projection) ** 2, axis=1)
    )
    real_difference = multiplier.real[:, None] - multiplier.real[None, :]
    coherence = 4.0 * np.real(
        np.sum(
            real_difference
            * inner_projection
            * band_projection.T,
            axis=1,
        )
    )
    return band_variance, coherence


def compact_root_weight(
    size: int, step: float, root_size: int
) -> tuple[np.ndarray, float]:
    witness, row_residual = PROOF_251.four_mode_row_witness(root_size, step)
    embedded = np.zeros(size, dtype=complex)
    start = size // 2 - root_size // 2
    embedded[start : start + root_size] = witness
    embedded /= np.linalg.norm(embedded)
    frequencies = 2.0 * np.pi * np.fft.fftfreq(size, d=step)
    transform = np.fft.fft(embedded) / math.sqrt(size)
    root_transform = (0.5 + 1j * frequencies) * transform
    return np.abs(root_transform) ** 2, row_residual


def weighted_value(weight: np.ndarray, density: np.ndarray) -> float:
    return float(np.sum(weight * density).real)


def commutator_pairing(
    projection: np.ndarray,
    first_multiplier: np.ndarray,
    second_multiplier: np.ndarray,
) -> float:
    first_difference = (
        first_multiplier[:, None] - first_multiplier[None, :]
    )
    second_difference = (
        second_multiplier[:, None] - second_multiplier[None, :]
    )
    first_commutator = first_difference * projection
    second_commutator = second_difference * projection
    return float(np.vdot(first_commutator, second_commutator).real)


def projection_density_error(projection: np.ndarray) -> float:
    row_norms = np.sum(np.abs(projection) ** 2, axis=1)
    diagonal = np.diag(projection).real
    denominator = max(float(np.max(np.abs(diagonal))), 1e-15)
    return float(np.max(np.abs(row_norms - diagonal)) / denominator)


def relative_vector_error(actual: np.ndarray, expected: np.ndarray) -> float:
    denominator = max(float(np.linalg.norm(expected)), 1e-15)
    return float(np.linalg.norm(actual - expected) / denominator)


def cutoff_row(
    outer_basis: np.ndarray,
    inner_basis: np.ndarray,
    base_band: np.ndarray,
    factors: list[dict[str, object]],
    root_weight: np.ndarray,
    quadrature_order: int,
) -> dict[str, float]:
    endpoint_outer, _, _ = PROOF_252.transported_projection(
        outer_basis, factors, 1.0
    )
    endpoint_inner, _, _ = PROOF_252.transported_projection(
        inner_basis, factors, 1.0
    )
    endpoint_band = endpoint_outer - endpoint_inner
    endpoint_change = endpoint_band - base_band
    endpoint_density = np.diag(
        to_fourier_coordinate(endpoint_change)
    ).real
    endpoint_value = weighted_value(root_weight, endpoint_density)

    nodes, weights = np.polynomial.legendre.leggauss(quadrature_order)
    direct_value = 0.0
    individual_value = 0.0
    outer_dirichlet_value = 0.0
    inner_dirichlet_value = 0.0
    band_value = 0.0
    coherence_value = 0.0
    absolute_band_value = 0.0
    absolute_coherence_value = 0.0
    maximum_direct_error = 0.0
    maximum_nested_error = 0.0
    maximum_constant_error = 0.0
    maximum_commutator_pairing_error = 0.0
    maximum_projection_density_error = 0.0
    maximum_orthogonality_error = 0.0
    maximum_trace_error = 0.0
    minimum_normalized_metric = math.inf
    minimum_normalized_generator = math.inf
    maximum_normalized_generator = 0.0

    for node, weight in zip((nodes + 1.0) / 2.0, weights / 2.0):
        parameter = float(node)
        outer, outer_columns, _ = PROOF_252.transported_projection(
            outer_basis, factors, parameter
        )
        inner, inner_columns, _ = PROOF_252.transported_projection(
            inner_basis, factors, parameter
        )
        band = outer - inner
        generator = PROOF_252.right_logarithmic_derivative(
            factors, parameter
        )
        direct_derivative = PROOF_252.projection_derivative(
            outer, outer_columns, generator
        ) - PROOF_252.projection_derivative(
            inner, inner_columns, generator
        )

        outer_fourier = to_fourier_coordinate(outer)
        inner_fourier = to_fourier_coordinate(inner)
        band_fourier = outer_fourier - inner_fourier
        direct_density = np.diag(
            to_fourier_coordinate(direct_derivative)
        ).real
        multiplier = generator_multiplier(factors, parameter)
        normalized_metric = np.ones(len(multiplier), dtype=float)
        for factor in factors:
            amplitude = float(factor["amplitude"])
            translation = np.asarray(factor["multiplier"])
            normalized_metric *= (
                np.abs(1.0 - parameter * amplitude * translation) ** 2
                / (1.0 - parameter * amplitude) ** 2
            )
        normalized_generator = multiplier.real - multiplier.real[0]
        minimum_normalized_metric = min(
            minimum_normalized_metric, float(normalized_metric.min())
        )
        minimum_normalized_generator = min(
            minimum_normalized_generator,
            float(normalized_generator.min()),
        )
        maximum_normalized_generator = max(
            maximum_normalized_generator,
            float(normalized_generator.max()),
        )

        outer_density = berezin_density(outer_fourier, multiplier)
        inner_density = berezin_density(inner_fourier, multiplier)
        individual_density = outer_density - inner_density
        band_density, coherence_density = nested_berezin_components(
            inner_fourier, band_fourier, multiplier
        )
        nested_density = band_density + coherence_density

        shifted_multiplier = multiplier + (2.3 - 1.7j)
        shifted_band, shifted_coherence = nested_berezin_components(
            inner_fourier, band_fourier, shifted_multiplier
        )

        maximum_direct_error = max(
            maximum_direct_error,
            relative_vector_error(individual_density, direct_density),
        )
        maximum_nested_error = max(
            maximum_nested_error,
            relative_vector_error(nested_density, individual_density),
        )
        maximum_constant_error = max(
            maximum_constant_error,
            relative_vector_error(
                shifted_band + shifted_coherence, nested_density
            ),
        )
        maximum_projection_density_error = max(
            maximum_projection_density_error,
            projection_density_error(outer_fourier),
            projection_density_error(inner_fourier),
            projection_density_error(band_fourier),
        )
        maximum_orthogonality_error = max(
            maximum_orthogonality_error,
            float(np.linalg.norm(inner_fourier @ band_fourier, ord="fro")),
        )
        maximum_trace_error = max(
            maximum_trace_error,
            float(abs(np.sum(direct_density))),
            float(abs(np.sum(individual_density))),
            float(abs(np.sum(nested_density))),
        )

        direct_quadratic = weighted_value(root_weight, direct_density)
        outer_quadratic = weighted_value(root_weight, outer_density)
        inner_quadratic = weighted_value(root_weight, inner_density)
        individual_quadratic = weighted_value(
            root_weight, individual_density
        )
        band_quadratic = weighted_value(root_weight, band_density)
        coherence_quadratic = weighted_value(
            root_weight, coherence_density
        )
        commutator_quadratic = commutator_pairing(
            outer_fourier, root_weight, multiplier.real
        ) - commutator_pairing(
            inner_fourier, root_weight, multiplier.real
        )
        maximum_commutator_pairing_error = max(
            maximum_commutator_pairing_error,
            abs(commutator_quadratic - direct_quadratic)
            / max(abs(direct_quadratic), 1e-15),
        )
        direct_value += weight * direct_quadratic
        individual_value += weight * individual_quadratic
        outer_dirichlet_value += weight * outer_quadratic
        inner_dirichlet_value += weight * inner_quadratic
        band_value += weight * band_quadratic
        coherence_value += weight * coherence_quadratic
        absolute_band_value += weight * abs(band_quadratic)
        absolute_coherence_value += weight * abs(coherence_quadratic)

    endpoint_error = abs(direct_value - endpoint_value) / max(
        abs(endpoint_value), 1e-15
    )
    component_error = abs(
        band_value + coherence_value - direct_value
    ) / max(abs(direct_value), 1e-15)
    individual_error = abs(individual_value - direct_value) / max(
        abs(direct_value), 1e-15
    )
    return {
        "endpoint_value": endpoint_value,
        "direct_value": direct_value,
        "individual_value": individual_value,
        "outer_dirichlet_value": outer_dirichlet_value,
        "inner_dirichlet_value": inner_dirichlet_value,
        "band_value": band_value,
        "coherence_value": coherence_value,
        "absolute_band_value": absolute_band_value,
        "absolute_coherence_value": absolute_coherence_value,
        "endpoint_error": endpoint_error,
        "component_error": component_error,
        "individual_error": individual_error,
        "maximum_direct_error": maximum_direct_error,
        "maximum_nested_error": maximum_nested_error,
        "maximum_constant_error": maximum_constant_error,
        "maximum_commutator_pairing_error": (
            maximum_commutator_pairing_error
        ),
        "maximum_projection_density_error": maximum_projection_density_error,
        "maximum_orthogonality_error": maximum_orthogonality_error,
        "maximum_trace_error": maximum_trace_error,
        "minimum_normalized_metric": minimum_normalized_metric,
        "minimum_normalized_generator": minimum_normalized_generator,
        "maximum_normalized_generator": maximum_normalized_generator,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--size", type=int, default=160)
    parser.add_argument("--step", type=float, default=0.08)
    parser.add_argument("--root-width", type=float, default=0.96)
    parser.add_argument("--prime-cutoffs", default="2,3,5,11,29")
    parser.add_argument("--intersection-tolerance", type=float, default=1e-8)
    parser.add_argument("--quadrature-order", type=int, default=12)
    parser.add_argument("--max-density-error", type=float, default=2e-10)
    parser.add_argument("--max-endpoint-error", type=float, default=3e-6)
    parser.add_argument("--max-orthogonality-error", type=float, default=2e-9)
    parser.add_argument("--max-trace-error", type=float, default=2e-9)
    args = parser.parse_args()

    if args.size < 64 or args.size % 2:
        raise ValueError("size must be an even integer at least 64")
    if args.step <= 0.0 or args.root_width <= 0.0:
        raise ValueError("step and root-width must be positive")
    if args.quadrature_order < 4:
        raise ValueError("quadrature-order must be at least four")

    cutoffs = PROOF_252.parse_positive_integers(args.prime_cutoffs)
    primes = PROOF_252.primes_up_to(cutoffs[-1])
    factors = PROOF_252.make_factors(primes, args.size, args.step)
    root_size = int(round(args.root_width / args.step)) + 1
    half_domain = args.size * args.step / 2.0
    if math.log(primes[-1]) + args.root_width >= half_domain:
        raise ValueError("domain is too small for the largest prime translation")

    coordinates = (np.arange(args.size) - args.size // 2) * args.step
    inner_basis, sonin_eigenvalues = PROOF_251.sonin_basis(
        args.size, args.step, args.intersection_tolerance
    )
    outer_basis = PROOF_251.halfline_basis(coordinates)
    outer_projection = PROOF_252.projection_from_basis(outer_basis)
    inner_projection = PROOF_252.projection_from_basis(inner_basis)
    base_band = outer_projection - inner_projection
    root_weight, row_residual = compact_root_weight(
        args.size, args.step, root_size
    )

    rows: list[dict[str, float]] = []
    for cutoff in cutoffs:
        factor_count = sum(prime <= cutoff for prime in primes)
        active_factors = factors[:factor_count]
        row = cutoff_row(
            outer_basis,
            inner_basis,
            base_band,
            active_factors,
            root_weight,
            args.quadrature_order,
        )
        row["cutoff"] = float(cutoff)
        row["factor_count"] = float(factor_count)
        row["half_weight"] = sum(
            float(factor["amplitude"]) for factor in active_factors
        )
        row["endpoint_scalar_bulk"] = sum(
            float(factor["amplitude"])
            / (1.0 - float(factor["amplitude"]))
            for factor in active_factors
        )
        rows.append(row)

    maximum_density_error = max(
        max(
            row["maximum_direct_error"],
            row["maximum_nested_error"],
            row["maximum_constant_error"],
            row["maximum_commutator_pairing_error"],
            row["maximum_projection_density_error"],
            row["component_error"],
            row["individual_error"],
        )
        for row in rows
    )
    maximum_endpoint_error = max(row["endpoint_error"] for row in rows)
    maximum_orthogonality_error = max(
        row["maximum_orthogonality_error"] for row in rows
    )
    maximum_trace_error = max(row["maximum_trace_error"] for row in rows)

    print("identity=nested Berezin synchronized finite-S flow")
    print("status=finite-section decomposition certificate")
    print(f"size={args.size}")
    print(f"step={args.step:.12g}")
    print(f"half_domain={half_domain:.12g}")
    print(f"root_size={root_size}")
    print(f"root_width={(root_size - 1) * args.step:.12g}")
    print(f"sonin_rank={inner_basis.shape[1]}")
    print(f"sonin_top_eigenvalue={sonin_eigenvalues[-1]:.12e}")
    print(f"four_mode_row_residual={row_residual:.12e}")
    print(f"maximum_density_error={maximum_density_error:.12e}")
    print(f"maximum_endpoint_error={maximum_endpoint_error:.12e}")
    print(
        "maximum_orthogonality_error="
        f"{maximum_orthogonality_error:.12e}"
    )
    print(f"maximum_trace_error={maximum_trace_error:.12e}")
    print("berezin_component_table=BEGIN")
    for row in rows:
        print(
            f"cutoff={int(row['cutoff'])} "
            f"prime_count={int(row['factor_count'])} "
            f"sum_p_half={row['half_weight']:.12e} "
            f"endpoint_scalar_bulk={row['endpoint_scalar_bulk']:.12e} "
            f"endpoint={row['endpoint_value']:.12e} "
            f"integrated={row['direct_value']:.12e} "
            f"outer_dirichlet={row['outer_dirichlet_value']:.12e} "
            f"inner_dirichlet={row['inner_dirichlet_value']:.12e} "
            f"band_variance={row['band_value']:.12e} "
            f"coherence={row['coherence_value']:.12e} "
            f"absolute_band={row['absolute_band_value']:.12e} "
            f"absolute_coherence={row['absolute_coherence_value']:.12e} "
            f"minimum_metric={row['minimum_normalized_metric']:.12e} "
            f"minimum_generator={row['minimum_normalized_generator']:.12e} "
            f"maximum_generator={row['maximum_normalized_generator']:.12e} "
            f"endpoint_error={row['endpoint_error']:.3e}"
        )
    print("berezin_component_table=END")

    if maximum_density_error > args.max_density_error:
        raise RuntimeError("nested Berezin density identity failed")
    if maximum_endpoint_error > args.max_endpoint_error:
        raise RuntimeError("integrated Berezin flow missed the endpoint")
    if maximum_orthogonality_error > args.max_orthogonality_error:
        raise RuntimeError("nested Fourier projections lost orthogonality")
    if maximum_trace_error > args.max_trace_error:
        raise RuntimeError("constant-rank trace identity failed")
    if min(row["minimum_normalized_metric"] for row in rows) < 1.0 - 2e-12:
        raise RuntimeError("scalar-normalized metric fell below the identity")
    if min(row["minimum_normalized_generator"] for row in rows) < -2e-12:
        raise RuntimeError("scalar-normalized real generator lost positivity")

    print("certificate=PASS")
    print("individual_berezin_difference_verdict=EXACT")
    print("nested_band_coherence_decomposition_verdict=EXACT")
    print("commutator_dirichlet_pairing_verdict=EXACT")
    print("scalar_generator_cancellation_verdict=EXACT")
    print("normalized_metric_lower_bound_verdict=EXACT")
    print("continuous_kernel_estimate=OPEN")
    print("detector_specific_integrated_bound=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
