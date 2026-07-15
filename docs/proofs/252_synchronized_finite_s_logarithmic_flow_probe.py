#!/usr/bin/env python3
"""Synchronized finite-S flow for the complete nested Sonin complement.

For a finite prime set S, put

    T_S(t) = product_(p in S) (I - t p^(-1/2) U_(log p)).

The translations commute, so the right logarithmic derivative is the exact
prime-power sum

    T_S'(t) T_S(t)^(-1)
      = -sum_(p in S) sum_(m >= 1)
          t^(m-1) p^(-m/2) U_(m log p).

This script keeps the complete transported outer and Sonin projections whole.
It compares their endpoint difference with the integral of the exact nested
projection flow, and compares the complete result with the sum of one-prime
endpoints and with the polarized mixed Hessian from Proof 251.

The periodic Fourier section is a diagnostic, not a continuous theorem.  No
sign, finite-S trace identity, or Riemann-hypothesis conclusion is assumed.
"""

from __future__ import annotations

import argparse
import importlib.util
import math
from pathlib import Path
from types import ModuleType

import numpy as np


def load_proof_251() -> ModuleType:
    path = Path(__file__).with_name(
        "251_mixed_prime_projection_curvature_probe.py"
    )
    spec = importlib.util.spec_from_file_location("proof_251", path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path.name}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


PROOF_251 = load_proof_251()


def primes_up_to(limit: int) -> list[int]:
    primes: list[int] = []
    for candidate in range(2, limit + 1):
        if all(candidate % prime for prime in primes if prime * prime <= candidate):
            primes.append(candidate)
    return primes


def parse_positive_integers(raw: str) -> list[int]:
    values = sorted({int(item) for item in raw.split(",") if item.strip()})
    if not values or values[0] < 2:
        raise ValueError("prime cutoffs must contain integers at least two")
    return values


def spectral_translation(
    size: int, step: float, length: float
) -> tuple[np.ndarray, np.ndarray]:
    frequencies = np.fft.fftfreq(size, d=step)
    multiplier = np.exp(2j * np.pi * frequencies * length)
    identity = np.eye(size, dtype=complex)
    matrix = np.fft.ifft(
        multiplier[:, None] * np.fft.fft(identity, axis=0), axis=0
    )
    return matrix, multiplier


def make_factors(
    primes: list[int], size: int, step: float
) -> list[dict[str, object]]:
    factors: list[dict[str, object]] = []
    for prime in primes:
        length = math.log(prime)
        translation, multiplier = spectral_translation(size, step, length)
        factors.append(
            {
                "prime": prime,
                "amplitude": prime ** -0.5,
                "length": length,
                "translation": translation,
                "multiplier": multiplier,
            }
        )
    return factors


def orthonormalize(columns: np.ndarray) -> tuple[np.ndarray, float]:
    basis, triangular = np.linalg.qr(columns, mode="reduced")
    diagonal = np.abs(np.diag(triangular))
    if len(diagonal) == 0:
        return basis, 1.0
    return basis, float(diagonal.min() / max(diagonal.max(), 1e-300))


def transport_basis(
    basis: np.ndarray,
    factors: list[dict[str, object]],
    parameter: float,
) -> tuple[np.ndarray, float]:
    transported = basis.copy()
    minimum_local_ratio = 1.0
    for factor in factors:
        amplitude = float(factor["amplitude"])
        translation = np.asarray(factor["translation"])
        transported, local_ratio = orthonormalize(
            transported - parameter * amplitude * (translation @ transported)
        )
        minimum_local_ratio = min(minimum_local_ratio, local_ratio)
    return transported, minimum_local_ratio


def projection_from_basis(basis: np.ndarray) -> np.ndarray:
    return basis @ basis.conj().T


def transported_projection(
    basis: np.ndarray,
    factors: list[dict[str, object]],
    parameter: float,
) -> tuple[np.ndarray, np.ndarray, float]:
    transported, minimum_local_ratio = transport_basis(
        basis, factors, parameter
    )
    return (
        projection_from_basis(transported),
        transported,
        minimum_local_ratio,
    )


def direct_product_projection(
    basis: np.ndarray, factors: list[dict[str, object]], parameter: float
) -> tuple[np.ndarray, float]:
    logarithm = np.zeros(len(np.asarray(factors[0]["multiplier"])), dtype=complex)
    for factor in factors:
        amplitude = float(factor["amplitude"])
        multiplier = np.asarray(factor["multiplier"])
        logarithm += np.log(1.0 - parameter * amplitude * multiplier)
    log_condition = float(logarithm.real.max() - logarithm.real.min())
    normalized_multiplier = np.exp(logarithm - logarithm.real.max())
    transported = np.fft.ifft(
        normalized_multiplier[:, None] * np.fft.fft(basis, axis=0), axis=0
    )
    transported, _ = orthonormalize(transported)
    return projection_from_basis(transported), log_condition


def right_logarithmic_derivative(
    factors: list[dict[str, object]], parameter: float
) -> np.ndarray:
    if not factors:
        raise ValueError("at least one finite-place factor is required")
    size = len(np.asarray(factors[0]["multiplier"]))
    multiplier = np.zeros(size, dtype=complex)
    for factor in factors:
        amplitude = float(factor["amplitude"])
        translation_multiplier = np.asarray(factor["multiplier"])
        multiplier -= (
            amplitude
            * translation_multiplier
            / (1.0 - parameter * amplitude * translation_multiplier)
        )
    identity = np.eye(size, dtype=complex)
    return np.fft.ifft(
        multiplier[:, None] * np.fft.fft(identity, axis=0), axis=0
    )


def logarithmic_derivative_multiplier_error(
    factors: list[dict[str, object]], parameter: float
) -> float:
    factor_values = [
        1.0
        - parameter
        * float(factor["amplitude"])
        * np.asarray(factor["multiplier"])
        for factor in factors
    ]
    product = np.prod(np.stack(factor_values), axis=0)
    derivative = np.zeros_like(product)
    for index, factor in enumerate(factors):
        amplitude = float(factor["amplitude"])
        translation_multiplier = np.asarray(factor["multiplier"])
        other_product = np.ones_like(product)
        for other_index, value in enumerate(factor_values):
            if other_index != index:
                other_product *= value
        derivative -= amplitude * translation_multiplier * other_product
    direct = derivative / product
    additive = np.zeros_like(direct)
    for factor in factors:
        amplitude = float(factor["amplitude"])
        translation_multiplier = np.asarray(factor["multiplier"])
        additive -= (
            amplitude
            * translation_multiplier
            / (1.0 - parameter * amplitude * translation_multiplier)
        )
    return float(np.max(np.abs(direct - additive)))


def projection_derivative(
    projection: np.ndarray, basis: np.ndarray, generator: np.ndarray
) -> np.ndarray:
    image = generator @ basis
    normal = image - basis @ (basis.conj().T @ image)
    derivative = normal @ basis.conj().T + basis @ normal.conj().T
    return (derivative + derivative.conj().T) / 2.0


def nested_flow_derivative(
    outer_projection: np.ndarray,
    inner_projection: np.ndarray,
    generator: np.ndarray,
) -> np.ndarray:
    identity = np.eye(len(outer_projection), dtype=complex)
    band_projection = outer_projection - inner_projection
    outer_complement = identity - outer_projection
    crossing = (
        outer_complement @ generator @ band_projection
        - inner_projection @ generator.conj().T @ band_projection
    )
    derivative = crossing + crossing.conj().T
    return (derivative + derivative.conj().T) / 2.0


def relative_frobenius_error(actual: np.ndarray, expected: np.ndarray) -> float:
    denominator = max(float(np.linalg.norm(expected, ord="fro")), 1e-15)
    return float(np.linalg.norm(actual - expected, ord="fro") / denominator)


def root_statistics(
    matrix: np.ndarray,
    root_size: int,
    step: float,
    witness: np.ndarray,
    constraint_basis: np.ndarray,
    galerkin_basis: np.ndarray,
) -> dict[str, object]:
    root = PROOF_251.root_operator(matrix, root_size, step)
    constrained = constraint_basis.conj().T @ root @ constraint_basis
    constrained = (constrained + constrained.conj().T) / 2.0
    galerkin = galerkin_basis.conj().T @ root @ galerkin_basis
    galerkin = (galerkin + galerkin.conj().T) / 2.0
    constrained_eigenvalues = np.linalg.eigvalsh(constrained)
    galerkin_eigenvalues = np.linalg.eigvalsh(galerkin)
    return {
        "root": root,
        "norm": PROOF_251.operator_norm(root),
        "quadratic": float(np.vdot(witness, root @ witness).real),
        "constrained_minimum": float(constrained_eigenvalues.min()),
        "constrained_maximum": float(constrained_eigenvalues.max()),
        "galerkin_minimum": float(galerkin_eigenvalues.min()),
        "galerkin_maximum": float(galerkin_eigenvalues.max()),
    }


def pair_hessian_sum(
    projection: np.ndarray,
    factors: list[dict[str, object]],
) -> np.ndarray:
    weighted_translation = sum(
        (
            float(factor["amplitude"])
            * np.asarray(factor["translation"])
            for factor in factors
        ),
        start=np.zeros_like(np.asarray(factors[0]["translation"])),
    )
    diagonal = np.zeros_like(weighted_translation)
    for factor in factors:
        amplitude = float(factor["amplitude"])
        translation = np.asarray(factor["translation"])
        diagonal += amplitude**2 * PROOF_251.projection_mixed_hessian(
            projection, translation, translation
        )
    complete = PROOF_251.projection_mixed_hessian(
        projection, weighted_translation, weighted_translation
    )
    return (complete - diagonal) / 2.0


def direct_pair_hessian_sum(
    projection: np.ndarray,
    factors: list[dict[str, object]],
) -> np.ndarray:
    result = np.zeros_like(projection)
    for first_index, first in enumerate(factors):
        for second in factors[first_index + 1 :]:
            result += (
                float(first["amplitude"])
                * float(second["amplitude"])
                * PROOF_251.projection_mixed_hessian(
                    projection,
                    np.asarray(first["translation"]),
                    np.asarray(second["translation"]),
                )
            )
    return result


def flow_integral(
    outer_basis: np.ndarray,
    inner_basis: np.ndarray,
    factors: list[dict[str, object]],
    root_size: int,
    step: float,
    quadrature_order: int,
) -> tuple[np.ndarray, float, float, float]:
    nodes, weights = np.polynomial.legendre.leggauss(quadrature_order)
    integral = np.zeros((root_size, root_size), dtype=complex)
    maximum_nested_error = 0.0
    minimum_local_ratio = 1.0
    maximum_nesting_error = 0.0
    for node, weight in zip((nodes + 1.0) / 2.0, weights / 2.0):
        outer_projection, outer_columns, outer_ratio = transported_projection(
            outer_basis, factors, float(node)
        )
        inner_projection, inner_columns, inner_ratio = transported_projection(
            inner_basis, factors, float(node)
        )
        generator = right_logarithmic_derivative(factors, float(node))
        direct = projection_derivative(
            outer_projection, outer_columns, generator
        ) - projection_derivative(inner_projection, inner_columns, generator)
        nested = nested_flow_derivative(
            outer_projection, inner_projection, generator
        )
        maximum_nested_error = max(
            maximum_nested_error, relative_frobenius_error(nested, direct)
        )
        minimum_local_ratio = min(
            minimum_local_ratio, outer_ratio, inner_ratio
        )
        maximum_nesting_error = max(
            maximum_nesting_error,
            float(
                np.linalg.norm(
                    outer_projection @ inner_projection - inner_projection,
                    ord="fro",
                )
            ),
        )
        integral += weight * PROOF_251.root_operator(
            (direct + direct.conj().T) / 2.0, root_size, step
        )
    integral = (integral + integral.conj().T) / 2.0
    return (
        integral,
        maximum_nested_error,
        minimum_local_ratio,
        maximum_nesting_error,
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--size", type=int, default=192)
    parser.add_argument("--step", type=float, default=0.08)
    parser.add_argument("--root-width", type=float, default=0.96)
    parser.add_argument(
        "--prime-cutoffs", default="2,3,5,7,11,17,29"
    )
    parser.add_argument("--intersection-tolerance", type=float, default=1e-8)
    parser.add_argument("--galerkin-modes", type=int, default=8)
    parser.add_argument("--quadrature-order", type=int, default=12)
    parser.add_argument("--skip-pair-hessian", action="store_true")
    parser.add_argument("--skip-flow-integral", action="store_true")
    parser.add_argument("--max-algebra-error", type=float, default=2e-12)
    parser.add_argument("--max-unitary-error", type=float, default=2e-10)
    parser.add_argument("--max-commutator-error", type=float, default=2e-10)
    parser.add_argument("--max-order-error", type=float, default=2e-9)
    parser.add_argument("--max-direct-product-error", type=float, default=2e-8)
    parser.add_argument("--max-polarization-error", type=float, default=2e-8)
    parser.add_argument("--max-nested-flow-error", type=float, default=2e-8)
    parser.add_argument("--max-flow-endpoint-error", type=float, default=2e-6)
    parser.add_argument("--max-nesting-error", type=float, default=2e-8)
    args = parser.parse_args()

    if args.size < 64 or args.size % 2:
        raise ValueError("size must be an even integer at least 64")
    if args.step <= 0.0 or args.root_width <= 0.0:
        raise ValueError("step and root-width must be positive")
    if args.galerkin_modes < 4:
        raise ValueError("galerkin-modes must be at least four")
    if args.quadrature_order < 4:
        raise ValueError("quadrature-order must be at least four")

    cutoffs = parse_positive_integers(args.prime_cutoffs)
    primes = primes_up_to(cutoffs[-1])
    factors = make_factors(primes, args.size, args.step)
    root_size = int(round(args.root_width / args.step)) + 1
    if root_size < 6 or root_size >= args.size // 2:
        raise ValueError("root interval is incompatible with the finite section")
    half_domain = args.size * args.step / 2.0
    if math.log(primes[-1]) + args.root_width >= half_domain:
        raise ValueError("domain is too small for the largest prime translation")

    coordinates = (np.arange(args.size) - args.size // 2) * args.step
    inner_basis, sonin_eigenvalues = PROOF_251.sonin_basis(
        args.size, args.step, args.intersection_tolerance
    )
    outer_basis = PROOF_251.halfline_basis(coordinates)
    outer_projection = projection_from_basis(outer_basis)
    inner_projection = projection_from_basis(inner_basis)
    base_band = outer_projection - inner_projection
    base_nesting_error = float(
        np.linalg.norm(
            outer_projection @ inner_projection - inner_projection, ord="fro"
        )
    )

    witness, witness_row_residual = PROOF_251.four_mode_row_witness(
        root_size, args.step
    )
    constraint_basis = PROOF_251.pre_root_constraint_basis(
        root_size, args.step
    )
    galerkin_basis = PROOF_251.constrained_dirichlet_galerkin_basis(
        root_size, args.step, args.galerkin_modes
    )

    unitary_errors = [
        float(
            np.linalg.norm(
                np.asarray(factor["translation"]).conj().T
                @ np.asarray(factor["translation"])
                - np.eye(args.size),
                ord="fro",
            )
        )
        for factor in factors
    ]
    commutator_error = 0.0
    for first, second in zip(factors, factors[1:]):
        first_translation = np.asarray(first["translation"])
        second_translation = np.asarray(second["translation"])
        commutator_error = max(
            commutator_error,
            float(
                np.linalg.norm(
                    first_translation @ second_translation
                    - second_translation @ first_translation,
                    ord="fro",
                )
            ),
        )

    algebra_errors = [
        logarithmic_derivative_multiplier_error(factors, parameter)
        for parameter in (0.13, 0.51, 0.89)
    ]

    direct_pair_count = min(3, len(factors))
    direct_factors = factors[:direct_pair_count]
    polarization_errors = []
    for projection in (outer_projection, inner_projection):
        polarized_direct = pair_hessian_sum(projection, direct_factors)
        explicit_direct = direct_pair_hessian_sum(
            projection, direct_factors
        )
        polarization_errors.append(
            relative_frobenius_error(polarized_direct, explicit_direct)
        )
    polarization_error = max(polarization_errors)

    cutoff_factor_counts = {
        cutoff: sum(prime <= cutoff for prime in primes) for cutoff in cutoffs
    }
    requested_counts = set(cutoff_factor_counts.values())
    prefix_outer: dict[int, np.ndarray] = {}
    prefix_inner: dict[int, np.ndarray] = {}
    prefix_minimum_ratio: dict[int, float] = {}
    current_outer = outer_basis.copy()
    current_inner = inner_basis.copy()
    running_minimum_ratio = 1.0
    for index, factor in enumerate(factors, start=1):
        current_outer, outer_ratio = orthonormalize(
            current_outer
            - float(factor["amplitude"])
            * (np.asarray(factor["translation"]) @ current_outer)
        )
        current_inner, inner_ratio = orthonormalize(
            current_inner
            - float(factor["amplitude"])
            * (np.asarray(factor["translation"]) @ current_inner)
        )
        running_minimum_ratio = min(
            running_minimum_ratio, outer_ratio, inner_ratio
        )
        if index in requested_counts:
            prefix_outer[index] = projection_from_basis(current_outer)
            prefix_inner[index] = projection_from_basis(current_inner)
            prefix_minimum_ratio[index] = running_minimum_ratio

    single_running = np.zeros_like(base_band)
    single_prefix: dict[int, np.ndarray] = {}
    for index, factor in enumerate(factors, start=1):
        single_outer, _, _ = transported_projection(
            outer_basis, [factor], 1.0
        )
        single_inner, _, _ = transported_projection(
            inner_basis, [factor], 1.0
        )
        single_running += (
            single_outer - single_inner - base_band
        )
        if index in requested_counts:
            single_prefix[index] = single_running.copy()

    rows: list[dict[str, object]] = []
    for cutoff in cutoffs:
        factor_count = cutoff_factor_counts[cutoff]
        active_factors = factors[:factor_count]
        complete = (
            prefix_outer[factor_count]
            - prefix_inner[factor_count]
            - base_band
        )
        singles = single_prefix[factor_count]
        connected = complete - singles
        pair = None
        if not args.skip_pair_hessian:
            pair = pair_hessian_sum(
                outer_projection, active_factors
            ) - pair_hessian_sum(inner_projection, active_factors)

        complete_stats = root_statistics(
            complete,
            root_size,
            args.step,
            witness,
            constraint_basis,
            galerkin_basis,
        )
        single_stats = root_statistics(
            singles,
            root_size,
            args.step,
            witness,
            constraint_basis,
            galerkin_basis,
        )
        connected_stats = root_statistics(
            connected,
            root_size,
            args.step,
            witness,
            constraint_basis,
            galerkin_basis,
        )
        pair_stats = None
        if pair is not None:
            pair_stats = root_statistics(
                pair,
                root_size,
                args.step,
                witness,
                constraint_basis,
                galerkin_basis,
            )
        rows.append(
            {
                "cutoff": cutoff,
                "factor_count": factor_count,
                "last_prime": int(active_factors[-1]["prime"]),
                "half_weight": sum(
                    float(factor["amplitude"])
                    for factor in active_factors
                ),
                "minimum_local_ratio": prefix_minimum_ratio[factor_count],
                "complete": complete_stats,
                "singles": single_stats,
                "connected": connected_stats,
                "pair": pair_stats,
            }
        )

    largest_factors = factors[: cutoff_factor_counts[cutoffs[-1]]]
    reverse_outer, _, _ = transported_projection(
        outer_basis, list(reversed(largest_factors)), 1.0
    )
    reverse_inner, _, _ = transported_projection(
        inner_basis, list(reversed(largest_factors)), 1.0
    )
    forward_band = (
        prefix_outer[len(largest_factors)]
        - prefix_inner[len(largest_factors)]
    )
    reverse_band = reverse_outer - reverse_inner
    order_error = relative_frobenius_error(reverse_band, forward_band)

    direct_outer, transport_log_condition = direct_product_projection(
        outer_basis, largest_factors, 1.0
    )
    direct_inner, inner_log_condition = direct_product_projection(
        inner_basis, largest_factors, 1.0
    )
    direct_band = direct_outer - direct_inner
    direct_product_error = relative_frobenius_error(
        direct_band, forward_band
    )
    transport_log_condition = max(
        transport_log_condition, inner_log_condition
    )

    endpoint_root = np.asarray(rows[-1]["complete"]["root"])
    integrated_root = np.zeros_like(endpoint_root)
    nested_flow_error = math.nan
    flow_minimum_ratio = math.nan
    flow_nesting_error = math.nan
    flow_endpoint_error = math.nan
    flow_quadratic = math.nan
    if not args.skip_flow_integral:
        (
            integrated_root,
            nested_flow_error,
            flow_minimum_ratio,
            flow_nesting_error,
        ) = flow_integral(
            outer_basis,
            inner_basis,
            largest_factors,
            root_size,
            args.step,
            args.quadrature_order,
        )
        flow_endpoint_error = relative_frobenius_error(
            integrated_root, endpoint_root
        )
        flow_quadratic = float(
            np.vdot(witness, integrated_root @ witness).real
        )
    endpoint_quadratic = float(rows[-1]["complete"]["quadratic"])

    print("identity=synchronized finite-S nested projection flow")
    print("status=finite-section death test only")
    print("transport=product_p(I-t*p^(-1/2)*U_logp)")
    print("generator=prime-power right logarithmic derivative")
    print("shift_mode=exact periodic Fourier translation")
    print(f"size={args.size}")
    print(f"step={args.step:.12g}")
    print(f"half_domain={half_domain:.12g}")
    print(f"root_size={root_size}")
    print(f"root_width={(root_size - 1) * args.step:.12g}")
    print(f"sonin_rank={inner_basis.shape[1]}")
    print(f"sonin_top_eigenvalue={sonin_eigenvalues[-1]:.12e}")
    print(f"four_mode_row_residual={witness_row_residual:.12e}")
    print(f"maximum_unitary_error={max(unitary_errors):.12e}")
    print(f"maximum_commutator_error={commutator_error:.12e}")
    print(f"maximum_log_derivative_error={max(algebra_errors):.12e}")
    print(f"pair_polarization_error={polarization_error:.12e}")
    print(f"base_nesting_error={base_nesting_error:.12e}")
    print(f"factor_order_error={order_error:.12e}")
    print(f"direct_product_error={direct_product_error:.12e}")
    print(f"transport_log_condition={transport_log_condition:.12e}")
    print(f"nested_flow_error={nested_flow_error:.12e}")
    print(f"flow_nesting_error={flow_nesting_error:.12e}")
    print(f"flow_endpoint_error={flow_endpoint_error:.12e}")
    print(f"flow_minimum_local_qr_ratio={flow_minimum_ratio:.12e}")
    print(f"endpoint_quadratic={endpoint_quadratic:.12e}")
    print(f"integrated_flow_quadratic={flow_quadratic:.12e}")
    print("finite_S_table=BEGIN")
    for row in rows:
        complete = row["complete"]
        singles = row["singles"]
        connected = row["connected"]
        pair = row["pair"]
        pair_quadratic = math.nan
        if pair is not None:
            pair_quadratic = float(pair["quadratic"])
        print(
            f"cutoff={row['cutoff']} "
            f"prime_count={row['factor_count']} "
            f"last_prime={row['last_prime']} "
            f"sum_p_half={row['half_weight']:.12e} "
            f"minimum_qr_ratio={row['minimum_local_ratio']:.3e} "
            f"complete_norm={complete['norm']:.12e} "
            f"complete_quadratic={complete['quadratic']:.12e} "
            f"single_quadratic={singles['quadratic']:.12e} "
            f"connected_quadratic={connected['quadratic']:.12e} "
            f"pair_quadratic={pair_quadratic:.12e} "
            f"constrained_minimum={complete['constrained_minimum']:.12e} "
            f"constrained_maximum={complete['constrained_maximum']:.12e} "
            f"galerkin_minimum={complete['galerkin_minimum']:.12e} "
            f"galerkin_maximum={complete['galerkin_maximum']:.12e}"
        )
    print("finite_S_table=END")

    if max(unitary_errors) > args.max_unitary_error:
        raise RuntimeError("spectral translation lost unitarity")
    if commutator_error > args.max_commutator_error:
        raise RuntimeError("prime translations stopped commuting")
    if max(algebra_errors) > args.max_algebra_error:
        raise RuntimeError("right logarithmic derivative identity failed")
    if polarization_error > args.max_polarization_error:
        raise RuntimeError("mixed-Hessian polarization identity failed")
    if base_nesting_error > args.max_nesting_error:
        raise RuntimeError("base Sonin range is not nested in the half-line range")
    if order_error > args.max_order_error:
        raise RuntimeError("finite-S transported range depends on factor order")
    if direct_product_error > args.max_direct_product_error:
        raise RuntimeError("sequential and direct finite-S transports disagree")
    if (
        not args.skip_flow_integral
        and nested_flow_error > args.max_nested_flow_error
    ):
        raise RuntimeError("complete nested-flow identity failed")
    if (
        not args.skip_flow_integral
        and flow_nesting_error > args.max_nesting_error
    ):
        raise RuntimeError("transported Sonin range lost nesting")
    if (
        not args.skip_flow_integral
        and flow_endpoint_error > args.max_flow_endpoint_error
    ):
        raise RuntimeError("integrated flow did not recover the endpoint")

    print("certificate=PASS")
    print("right_logarithmic_derivative_verdict=EXACT")
    print("mixed_hessian_polarization_verdict=EXACT")
    print("synchronized_flow_endpoint_verdict=PASS")
    print("finite_S_signed_aggregate_verdict=DIAGNOSTIC_ONLY")
    print("continuous_aggregate_theorem=OPEN")
    print("same_object_finite_S_trace_identity=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
