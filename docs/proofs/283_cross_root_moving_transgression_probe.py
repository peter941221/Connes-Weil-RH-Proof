#!/usr/bin/env python3
"""Certificate for Proof 283's cross-root moving transgression.

Two distinct compact roots eta,xi define the complex detector

    W=C_xi* C_eta.

The script checks that its legal endpoint response equals twice the complete
moving-band cocycle integral from Proof 282.  It also verifies complex
polarization from four diagonal compact-root responses.  No raw point trace of
a translated projection difference is formed.
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


PROOF_282 = load_module(
    "282_moving_band_cocycle_integral_probe.py",
    "proof_282_for_283",
)
PROOF_253 = PROOF_282.PROOF_253
PROOF_252 = PROOF_282.PROOF_252
PROOF_251 = PROOF_282.PROOF_251
PROOF_281 = PROOF_282.PROOF_281


def complex_log_determinant(matrix: np.ndarray) -> complex:
    sign, logarithm = np.linalg.slogdet(matrix)
    if abs(sign) < 0.5:
        raise ValueError("matrix is singular")
    return complex(logarithm + np.log(sign))


def compact_root_pair(
    size: int, step: float, root_size: int
) -> tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray, float]:
    base, row_residual = PROOF_251.four_mode_row_witness(root_size, step)
    local_coordinate = (
        np.arange(root_size) - (root_size - 1) / 2.0
    ) * step
    eta_local = np.asarray(base, dtype=complex)
    xi_local = (
        np.exp(0.71j * local_coordinate) * eta_local
        + 0.23j * np.roll(eta_local, 1)
    )
    eta_local /= np.linalg.norm(eta_local)
    xi_local /= np.linalg.norm(xi_local)

    eta = np.zeros(size, dtype=complex)
    xi = np.zeros(size, dtype=complex)
    start = size // 2 - root_size // 2
    eta[start : start + root_size] = eta_local
    xi[start : start + root_size] = xi_local

    eta_transform = np.fft.fft(eta) / math.sqrt(size)
    xi_transform = np.fft.fft(xi) / math.sqrt(size)
    cross_multiplier = np.conj(xi_transform) * eta_transform
    return eta, xi, eta_transform, cross_multiplier, row_residual


def response(
    multiplier: np.ndarray, matrix: np.ndarray
) -> complex:
    return complex(np.sum(multiplier * np.diag(matrix)))


def complex_band_cocycle_log(
    model: dict[str, np.ndarray],
    detector_values: np.ndarray,
    generator_values: np.ndarray,
    detector_parameter: float,
    generator_parameter: float,
) -> complex:
    detector = np.diag(
        np.exp(detector_parameter * detector_values)
    ).astype(complex)
    generator = np.diag(
        np.exp(generator_parameter * generator_values)
    ).astype(complex)
    detector_short = PROOF_281.shorted_band(
        model, detector
    )["shorted"]
    generator_short = PROOF_281.shorted_band(
        model, generator
    )["shorted"]
    product_short = PROOF_281.shorted_band(
        model, detector @ generator
    )["shorted"]
    return (
        complex_log_determinant(product_short)
        - complex_log_determinant(detector_short)
        - complex_log_determinant(generator_short)
    )


def complex_band_cocycle_derivative(
    model: dict[str, np.ndarray],
    detector_values: np.ndarray,
    generator_values: np.ndarray,
    step: float,
) -> complex:
    values: dict[tuple[int, int], complex] = {}
    for detector_sign in (-1, 1):
        for generator_sign in (-1, 1):
            values[(detector_sign, generator_sign)] = (
                complex_band_cocycle_log(
                    model,
                    detector_values,
                    generator_values,
                    detector_sign * step,
                    generator_sign * step,
                )
            )
    return (
        values[(1, 1)]
        - values[(1, -1)]
        - values[(-1, 1)]
        + values[(-1, -1)]
    ) / (4.0 * step**2)


def diagonal_endpoint_response(
    root_transform: np.ndarray, endpoint_change: np.ndarray
) -> complex:
    return response(np.abs(root_transform) ** 2, endpoint_change)


def cutoff_row(
    outer_basis: np.ndarray,
    inner_basis: np.ndarray,
    base_band: np.ndarray,
    factors: list[dict[str, object]],
    eta_transform: np.ndarray,
    xi_transform: np.ndarray,
    cross_multiplier: np.ndarray,
    quadrature_order: int,
    derivative_step: float,
    cocycle_nodes: int,
) -> dict[str, float | complex]:
    endpoint_outer, _, _ = PROOF_252.transported_projection(
        outer_basis, factors, 1.0
    )
    endpoint_inner, _, _ = PROOF_252.transported_projection(
        inner_basis, factors, 1.0
    )
    endpoint_change = PROOF_253.to_fourier_coordinate(
        endpoint_outer - endpoint_inner - base_band
    )
    endpoint = response(cross_multiplier, endpoint_change)

    polarized_endpoint = 0.0j
    for power in range(4):
        phase = 1j**power
        combined = eta_transform + phase * xi_transform
        polarized_endpoint += phase * diagonal_endpoint_response(
            combined, endpoint_change
        ) / 4.0

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

    detector = np.diag(cross_multiplier).astype(complex)
    integrated = 0.0j
    integrated_direct = 0.0j
    absolute_branches = 0.0
    maximum_band_error = 0.0
    maximum_direct_error = 0.0
    maximum_gauge_error = 0.0
    maximum_cocycle_error = 0.0

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
        generator_matrix = PROOF_252.right_logarithmic_derivative(
            factors, parameter
        )
        direct_derivative = PROOF_252.projection_derivative(
            outer, outer_columns, generator_matrix
        ) - PROOF_252.projection_derivative(
            inner, inner_columns, generator_matrix
        )
        direct_fourier = PROOF_253.to_fourier_coordinate(
            direct_derivative
        )
        direct_scalar = response(cross_multiplier, direct_fourier)

        outer_fourier = PROOF_253.to_fourier_coordinate(outer)
        inner_fourier = PROOF_253.to_fourier_coordinate(inner)
        generator_values = PROOF_253.generator_multiplier(
            factors, parameter
        ).real
        generator = np.diag(generator_values).astype(complex)
        terms = PROOF_282.moving_band_terms(
            outer_fourier, inner_fourier, detector, generator
        )
        band_scalar = terms["difference"]
        maximum_band_error = max(
            maximum_band_error,
            PROOF_282.relative_error(
                band_scalar, terms["relative_covariance"]
            ),
        )
        maximum_direct_error = max(
            maximum_direct_error,
            PROOF_282.relative_error(2.0 * band_scalar, direct_scalar),
        )
        shifted_terms = PROOF_282.moving_band_terms(
            outer_fourier,
            inner_fourier,
            detector,
            generator + (1.9 + 0.8j) * np.eye(len(generator)),
        )
        maximum_gauge_error = max(
            maximum_gauge_error,
            PROOF_282.relative_error(
                shifted_terms["difference"], band_scalar
            ),
        )

        if index in cocycle_indices:
            model = {"outer": outer_fourier, "sonin": inner_fourier}
            cocycle_derivative = complex_band_cocycle_derivative(
                model,
                cross_multiplier,
                generator_values,
                derivative_step,
            )
            maximum_cocycle_error = max(
                maximum_cocycle_error,
                PROOF_282.relative_error(cocycle_derivative, band_scalar),
            )

        integrated += weight * 2.0 * band_scalar
        integrated_direct += weight * direct_scalar
        absolute_branches += weight * 2.0 * (
            abs(terms["outer_band"]) + abs(terms["inner_band"])
        )

    return {
        "endpoint": endpoint,
        "polarized_endpoint": polarized_endpoint,
        "integrated": integrated,
        "integrated_direct": integrated_direct,
        "endpoint_error": PROOF_282.relative_error(integrated, endpoint),
        "direct_error": PROOF_282.relative_error(
            integrated_direct, endpoint
        ),
        "polarization_error": PROOF_282.relative_error(
            polarized_endpoint, endpoint
        ),
        "maximum_band_error": maximum_band_error,
        "maximum_direct_error": maximum_direct_error,
        "maximum_gauge_error": maximum_gauge_error,
        "maximum_cocycle_error": maximum_cocycle_error,
        "absolute_branches": absolute_branches,
        "cancellation_ratio": absolute_branches / max(abs(endpoint), 1e-15),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--size", type=int, default=96)
    parser.add_argument("--step", type=float, default=0.08)
    parser.add_argument("--root-width", type=float, default=0.64)
    parser.add_argument("--prime-cutoffs", default="2,5,11")
    parser.add_argument("--intersection-tolerance", type=float, default=1e-8)
    parser.add_argument("--quadrature-order", type=int, default=8)
    parser.add_argument("--derivative-step", type=float, default=5e-4)
    parser.add_argument("--cocycle-nodes", type=int, default=2)
    parser.add_argument("--algebra-tolerance", type=float, default=3e-9)
    parser.add_argument("--endpoint-tolerance", type=float, default=3e-5)
    parser.add_argument("--derivative-tolerance", type=float, default=3e-5)
    args = parser.parse_args()

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
    eta, xi, eta_transform, cross_multiplier, row_residual = (
        compact_root_pair(args.size, args.step, root_size)
    )
    xi_transform = np.fft.fft(xi) / math.sqrt(args.size)

    support_tolerance = 1e-14
    support_indices = np.flatnonzero(
        (np.abs(eta) + np.abs(xi)) > support_tolerance
    )
    support_span = (
        float((support_indices[-1] - support_indices[0]) * args.step)
        if len(support_indices)
        else 0.0
    )

    rows: list[dict[str, float | complex]] = []
    for cutoff in cutoffs:
        factor_count = sum(prime <= cutoff for prime in primes)
        row = cutoff_row(
            outer_basis,
            inner_basis,
            base_band,
            factors[:factor_count],
            eta_transform,
            xi_transform,
            cross_multiplier,
            args.quadrature_order,
            args.derivative_step,
            args.cocycle_nodes,
        )
        row["cutoff"] = float(cutoff)
        row["factor_count"] = float(factor_count)
        rows.append(row)

    maximum_algebra_error = max(
        max(
            float(row["maximum_band_error"]),
            float(row["maximum_direct_error"]),
            float(row["maximum_gauge_error"]),
            float(row["polarization_error"]),
        )
        for row in rows
    )
    maximum_endpoint_error = max(
        float(row["endpoint_error"]) for row in rows
    )
    maximum_cocycle_error = max(
        float(row["maximum_cocycle_error"]) for row in rows
    )

    print("identity=cross-root moving transgression")
    print("status=actual finite-S sesquilinear certificate")
    print(f"size={args.size}")
    print(f"step={args.step:.12g}")
    print(f"root_size={root_size}")
    print(f"support_span={support_span:.12e}")
    print(f"sonin_rank={inner_basis.shape[1]}")
    print(f"sonin_top_eigenvalue={sonin_eigenvalues[-1]:.12e}")
    print(f"four_mode_row_residual={row_residual:.12e}")
    print(f"maximum_algebra_error={maximum_algebra_error:.12e}")
    print(f"maximum_endpoint_error={maximum_endpoint_error:.12e}")
    print(f"maximum_cocycle_error={maximum_cocycle_error:.12e}")
    print("cross_root_table=BEGIN")
    for row in rows:
        endpoint = complex(row["endpoint"])
        integrated = complex(row["integrated"])
        print(
            f"cutoff={int(row['cutoff'])} "
            f"prime_count={int(row['factor_count'])} "
            f"endpoint_real={endpoint.real:.12e} "
            f"endpoint_imag={endpoint.imag:.12e} "
            f"integrated_real={integrated.real:.12e} "
            f"integrated_imag={integrated.imag:.12e} "
            f"endpoint_error={float(row['endpoint_error']):.3e} "
            f"polarization_error={float(row['polarization_error']):.3e} "
            f"cocycle_error={float(row['maximum_cocycle_error']):.3e} "
            f"cancellation_ratio={float(row['cancellation_ratio']):.6e}"
        )
    print("cross_root_table=END")

    if maximum_algebra_error > args.algebra_tolerance:
        raise SystemExit(
            f"cross-root algebra failed: {maximum_algebra_error:.6e}"
        )
    if maximum_endpoint_error > args.endpoint_tolerance:
        raise SystemExit(
            f"cross-root integral missed endpoint: {maximum_endpoint_error:.6e}"
        )
    if maximum_cocycle_error > args.derivative_tolerance:
        raise SystemExit(
            f"cross-root cocycle derivative failed: {maximum_cocycle_error:.6e}"
        )

    print("sesquilinear_endpoint_owner=EXACT")
    print("complex_polarization=EXACT")
    print("moving_band_transgression=EXACT")
    print("compact_root_support_preserved=EXACT")
    print("raw_point_translation_trace_required=FALSE")
    print("uniform_cross_root_bound=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
