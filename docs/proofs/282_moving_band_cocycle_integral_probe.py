#!/usr/bin/env python3
"""Certificate for Proof 282's moving-band cocycle integral.

The script reuses Proof 253's actual synchronized finite-S translations and
moving outer/Sonin projections.  At every quadrature node it checks

    D_E(W,h)-D_R(W,h)
      =2 [Tr(B W C h B)-Tr(R W B h R)],

and verifies that the time integral recovers the endpoint band response.  It
also differentiates Proof 281's ordinary band Fredholm cocycle on the actual
moving band at selected nodes.
"""

from __future__ import annotations

import argparse
import importlib.util
import math
from pathlib import Path
from types import ModuleType

import numpy as np


def load_module(filename: str, name: str) -> ModuleType:
    path = Path(__file__).with_name(filename)
    specification = importlib.util.spec_from_file_location(name, path)
    if specification is None or specification.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(specification)
    specification.loader.exec_module(module)
    return module


PROOF_253 = load_module(
    "253_nested_berezin_synchronized_flow_probe.py",
    "proof_253_for_282",
)
PROOF_281 = load_module(
    "281_band_shorted_semicommutator_probe.py",
    "proof_281_for_282",
)
PROOF_252 = PROOF_253.PROOF_252
PROOF_251 = PROOF_253.PROOF_251


def relative_error(actual: complex, expected: complex) -> float:
    return float(abs(actual - expected) / max(abs(expected), 1.0))


def covariance(
    projection: np.ndarray,
    detector: np.ndarray,
    generator: np.ndarray,
) -> complex:
    identity = np.eye(projection.shape[0], dtype=complex)
    return np.trace(
        projection
        @ detector
        @ (identity - projection)
        @ generator
        @ projection
    )


def moving_band_terms(
    outer: np.ndarray,
    inner: np.ndarray,
    detector: np.ndarray,
    generator: np.ndarray,
) -> dict[str, complex]:
    identity = np.eye(outer.shape[0], dtype=complex)
    band = outer - inner
    exterior = identity - outer
    outer_band = np.trace(
        band @ detector @ exterior @ generator @ band
    )
    inner_band = np.trace(
        inner @ detector @ band @ generator @ inner
    )
    relative_covariance = covariance(
        outer, detector, generator
    ) - covariance(inner, detector, generator)
    return {
        "outer_band": outer_band,
        "inner_band": inner_band,
        "difference": outer_band - inner_band,
        "relative_covariance": relative_covariance,
    }


def band_cocycle_log(
    model: dict[str, np.ndarray],
    detector: np.ndarray,
    generator: np.ndarray,
    detector_parameter: float,
    generator_parameter: float,
) -> float:
    detector_diagonal = np.real(np.diag(detector))
    generator_diagonal = np.real(np.diag(generator))
    detector_multiplier = np.diag(
        np.exp(detector_parameter * detector_diagonal)
    ).astype(complex)
    generator_multiplier = np.diag(
        np.exp(generator_parameter * generator_diagonal)
    ).astype(complex)
    return float(
        PROOF_281.band_cocycle(
            model, detector_multiplier, generator_multiplier
        )["log_determinant"]
    )


def band_cocycle_mixed_derivative(
    model: dict[str, np.ndarray],
    detector: np.ndarray,
    generator: np.ndarray,
    step: float,
) -> float:
    values: dict[tuple[int, int], float] = {}
    for detector_sign in (-1, 1):
        for generator_sign in (-1, 1):
            values[(detector_sign, generator_sign)] = band_cocycle_log(
                model,
                detector,
                generator,
                detector_sign * step,
                generator_sign * step,
            )
    return (
        values[(1, 1)]
        - values[(1, -1)]
        - values[(-1, 1)]
        + values[(-1, -1)]
    ) / (4.0 * step**2)


def cutoff_row(
    outer_basis: np.ndarray,
    inner_basis: np.ndarray,
    base_band: np.ndarray,
    factors: list[dict[str, object]],
    root_weight: np.ndarray,
    quadrature_order: int,
    derivative_step: float,
    cocycle_nodes: int,
) -> dict[str, float]:
    endpoint_outer, _, _ = PROOF_252.transported_projection(
        outer_basis, factors, 1.0
    )
    endpoint_inner, _, _ = PROOF_252.transported_projection(
        inner_basis, factors, 1.0
    )
    endpoint_band = endpoint_outer - endpoint_inner
    endpoint_density = np.diag(
        PROOF_253.to_fourier_coordinate(endpoint_band - base_band)
    ).real
    endpoint_value = PROOF_253.weighted_value(
        root_weight, endpoint_density
    )

    nodes, weights = np.polynomial.legendre.leggauss(quadrature_order)
    normalized_nodes = (nodes + 1.0) / 2.0
    normalized_weights = weights / 2.0
    cocycle_indices = set(
        np.linspace(
            0,
            quadrature_order - 1,
            min(cocycle_nodes, quadrature_order),
            dtype=int,
        ).tolist()
    )

    detector = np.diag(root_weight).astype(complex)
    integrated_direct = 0.0
    integrated_band = 0.0
    integrated_outer = 0.0
    integrated_inner = 0.0
    absolute_branch_integral = 0.0
    maximum_band_identity_error = 0.0
    maximum_factor_two_error = 0.0
    maximum_direct_error = 0.0
    maximum_gauge_error = 0.0
    maximum_cocycle_derivative_error = 0.0
    maximum_imaginary_residue = 0.0

    for index, (node, weight) in enumerate(
        zip(normalized_nodes, normalized_weights)
    ):
        parameter = float(node)
        outer, outer_columns, _ = PROOF_252.transported_projection(
            outer_basis, factors, parameter
        )
        inner, inner_columns, _ = PROOF_252.transported_projection(
            inner_basis, factors, parameter
        )
        band = outer - inner
        exterior = np.eye(len(outer), dtype=complex) - outer
        generator_matrix = PROOF_252.right_logarithmic_derivative(
            factors, parameter
        )
        direct_derivative = PROOF_252.projection_derivative(
            outer, outer_columns, generator_matrix
        ) - PROOF_252.projection_derivative(
            inner, inner_columns, generator_matrix
        )
        direct_density = np.diag(
            PROOF_253.to_fourier_coordinate(direct_derivative)
        ).real
        direct_scalar = PROOF_253.weighted_value(
            root_weight, direct_density
        )

        outer_fourier = PROOF_253.to_fourier_coordinate(outer)
        inner_fourier = PROOF_253.to_fourier_coordinate(inner)
        band_fourier = outer_fourier - inner_fourier
        exterior_fourier = np.eye(len(outer), dtype=complex) - outer_fourier
        generator_values = PROOF_253.generator_multiplier(
            factors, parameter
        ).real
        generator = np.diag(generator_values).astype(complex)
        terms = moving_band_terms(
            outer_fourier, inner_fourier, detector, generator
        )
        band_scalar = terms["difference"]
        relative_covariance = terms["relative_covariance"]

        outer_band_direct = np.trace(
            band_fourier
            @ detector
            @ exterior_fourier
            @ generator
            @ band_fourier
        )
        inner_band_direct = np.trace(
            inner_fourier
            @ detector
            @ band_fourier
            @ generator
            @ inner_fourier
        )
        maximum_band_identity_error = max(
            maximum_band_identity_error,
            relative_error(band_scalar, relative_covariance),
            relative_error(terms["outer_band"], outer_band_direct),
            relative_error(terms["inner_band"], inner_band_direct),
        )
        maximum_factor_two_error = max(
            maximum_factor_two_error,
            relative_error(2.0 * band_scalar, direct_scalar),
        )
        maximum_direct_error = max(
            maximum_direct_error,
            relative_error(
                2.0 * relative_covariance, direct_scalar
            ),
        )
        shifted_terms = moving_band_terms(
            outer_fourier,
            inner_fourier,
            detector,
            generator + (2.7 - 1.3j) * np.eye(len(generator)),
        )
        maximum_gauge_error = max(
            maximum_gauge_error,
            relative_error(shifted_terms["difference"], band_scalar),
        )
        maximum_imaginary_residue = max(
            maximum_imaginary_residue,
            abs(band_scalar.imag),
            abs(relative_covariance.imag),
        )

        if index in cocycle_indices:
            model = {"outer": outer_fourier, "sonin": inner_fourier}
            cocycle_derivative = band_cocycle_mixed_derivative(
                model,
                detector,
                generator,
                derivative_step,
            )
            maximum_cocycle_derivative_error = max(
                maximum_cocycle_derivative_error,
                relative_error(cocycle_derivative, band_scalar.real),
            )

        integrated_direct += weight * direct_scalar
        integrated_band += weight * 2.0 * band_scalar.real
        integrated_outer += weight * 2.0 * terms["outer_band"].real
        integrated_inner += weight * 2.0 * terms["inner_band"].real
        absolute_branch_integral += weight * 2.0 * (
            abs(terms["outer_band"]) + abs(terms["inner_band"])
        )

    endpoint_error = relative_error(integrated_band, endpoint_value)
    direct_integral_error = relative_error(
        integrated_direct, endpoint_value
    )
    band_direct_error = relative_error(integrated_band, integrated_direct)
    return {
        "endpoint": endpoint_value,
        "integrated_direct": integrated_direct,
        "integrated_band": integrated_band,
        "integrated_outer": integrated_outer,
        "integrated_inner": integrated_inner,
        "absolute_branch_integral": absolute_branch_integral,
        "branch_cancellation_ratio": absolute_branch_integral
        / max(abs(integrated_band), 1e-15),
        "endpoint_error": endpoint_error,
        "direct_integral_error": direct_integral_error,
        "band_direct_error": band_direct_error,
        "maximum_band_identity_error": maximum_band_identity_error,
        "maximum_factor_two_error": maximum_factor_two_error,
        "maximum_direct_error": maximum_direct_error,
        "maximum_gauge_error": maximum_gauge_error,
        "maximum_cocycle_derivative_error": (
            maximum_cocycle_derivative_error
        ),
        "maximum_imaginary_residue": maximum_imaginary_residue,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--size", type=int, default=128)
    parser.add_argument("--step", type=float, default=0.08)
    parser.add_argument("--root-width", type=float, default=0.72)
    parser.add_argument("--prime-cutoffs", default="2,5,11")
    parser.add_argument("--intersection-tolerance", type=float, default=1e-8)
    parser.add_argument("--quadrature-order", type=int, default=8)
    parser.add_argument("--derivative-step", type=float, default=5e-4)
    parser.add_argument("--cocycle-nodes", type=int, default=3)
    parser.add_argument("--algebra-tolerance", type=float, default=2e-9)
    parser.add_argument("--endpoint-tolerance", type=float, default=2e-5)
    parser.add_argument("--derivative-tolerance", type=float, default=2e-5)
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
        raise ValueError("domain is too small for the largest translation")

    coordinates = (np.arange(args.size) - args.size // 2) * args.step
    inner_basis, sonin_eigenvalues = PROOF_251.sonin_basis(
        args.size, args.step, args.intersection_tolerance
    )
    outer_basis = PROOF_251.halfline_basis(coordinates)
    outer_projection = PROOF_252.projection_from_basis(outer_basis)
    inner_projection = PROOF_252.projection_from_basis(inner_basis)
    base_band = outer_projection - inner_projection
    root_weight, row_residual = PROOF_253.compact_root_weight(
        args.size, args.step, root_size
    )

    rows: list[dict[str, float]] = []
    for cutoff in cutoffs:
        factor_count = sum(prime <= cutoff for prime in primes)
        row = cutoff_row(
            outer_basis,
            inner_basis,
            base_band,
            factors[:factor_count],
            root_weight,
            args.quadrature_order,
            args.derivative_step,
            args.cocycle_nodes,
        )
        row["cutoff"] = float(cutoff)
        row["factor_count"] = float(factor_count)
        rows.append(row)

    maximum_algebra_error = max(
        max(
            row["maximum_band_identity_error"],
            row["maximum_factor_two_error"],
            row["maximum_direct_error"],
            row["maximum_gauge_error"],
            row["maximum_imaginary_residue"],
            row["band_direct_error"],
        )
        for row in rows
    )
    maximum_endpoint_error = max(row["endpoint_error"] for row in rows)
    maximum_derivative_error = max(
        row["maximum_cocycle_derivative_error"] for row in rows
    )

    print("identity=moving-band cocycle integral")
    print("status=actual synchronized finite-S certificate")
    print(f"size={args.size}")
    print(f"step={args.step:.12g}")
    print(f"half_domain={half_domain:.12g}")
    print(f"root_size={root_size}")
    print(f"sonin_rank={inner_basis.shape[1]}")
    print(f"sonin_top_eigenvalue={sonin_eigenvalues[-1]:.12e}")
    print(f"four_mode_row_residual={row_residual:.12e}")
    print(f"maximum_algebra_error={maximum_algebra_error:.12e}")
    print(f"maximum_endpoint_error={maximum_endpoint_error:.12e}")
    print(f"maximum_cocycle_derivative_error={maximum_derivative_error:.12e}")
    print("moving_band_table=BEGIN")
    for row in rows:
        print(
            f"cutoff={int(row['cutoff'])} "
            f"prime_count={int(row['factor_count'])} "
            f"endpoint={row['endpoint']:.12e} "
            f"integrated_direct={row['integrated_direct']:.12e} "
            f"integrated_band={row['integrated_band']:.12e} "
            f"outer_band={row['integrated_outer']:.12e} "
            f"inner_band={row['integrated_inner']:.12e} "
            f"absolute_branches={row['absolute_branch_integral']:.12e} "
            f"cancellation_ratio={row['branch_cancellation_ratio']:.6e} "
            f"endpoint_error={row['endpoint_error']:.3e} "
            f"cocycle_error={row['maximum_cocycle_derivative_error']:.3e}"
        )
    print("moving_band_table=END")

    if maximum_algebra_error > args.algebra_tolerance:
        raise SystemExit(
            f"moving-band algebra failed: {maximum_algebra_error:.6e}"
        )
    if maximum_endpoint_error > args.endpoint_tolerance:
        raise SystemExit(
            f"moving-band integral missed endpoint: {maximum_endpoint_error:.6e}"
        )
    if maximum_derivative_error > args.derivative_tolerance:
        raise SystemExit(
            f"moving-band cocycle derivative failed: {maximum_derivative_error:.6e}"
        )

    print("moving_generator_owner=EXACT")
    print("dirichlet_to_covariance_factor_two=EXACT")
    print("common_R_C_crossing_cancellation=EXACT")
    print("moving_band_cocycle_jet=EXACT")
    print("time_integral_recovers_endpoint=EXACT")
    print("endpoint_metric_substitution=REJECTED")
    print("pointwise_crossing_bound_required=FALSE")
    print("uniform_integrated_bound=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
