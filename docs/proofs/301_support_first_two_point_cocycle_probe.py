#!/usr/bin/env python3
"""Certificate for Proof 301's support-first two-point cocycle."""

from __future__ import annotations

import argparse
import math

import numpy as np


def relative_error(
    actual: complex | np.ndarray, expected: complex | np.ndarray
) -> float:
    actual_array = np.asarray(actual)
    expected_array = np.asarray(expected)
    scale = max(float(np.linalg.norm(expected_array)), 1.0)
    return float(np.linalg.norm(actual_array - expected_array) / scale)


def parse_primes(value: str) -> list[int]:
    primes = [int(item.strip()) for item in value.split(",") if item.strip()]
    if len(primes) < 2:
        raise argparse.ArgumentTypeError("provide at least two primes")
    return primes


def is_prime(value: int) -> bool:
    if value < 2:
        return False
    if value % 2 == 0:
        return value == 2
    divisor = 3
    while divisor <= math.isqrt(value):
        if value % divisor == 0:
            return False
        divisor += 2
    return True


def random_nested_projections(
    size: int, outer_rank: int, inner_rank: int, seed: int
) -> tuple[np.ndarray, np.ndarray]:
    if not 0 < inner_rank < outer_rank < size:
        raise ValueError("require 0 < inner_rank < outer_rank < size")
    rng = np.random.default_rng(seed)
    matrix = rng.normal(size=(size, size)) + 1j * rng.normal(
        size=(size, size)
    )
    unitary, _ = np.linalg.qr(matrix)
    outer_basis = unitary[:, :outer_rank]
    inner_basis = unitary[:, :inner_rank]
    outer = outer_basis @ outer_basis.conj().T
    inner = inner_basis @ inner_basis.conj().T
    return outer, inner


def compact_root(
    size: int, support_radius: int, seed: int
) -> tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray]:
    if 4 * support_radius + 1 >= size:
        raise ValueError("support is too wide for a non-wrapping correlation")
    rng = np.random.default_rng(seed)
    root = np.zeros(size, dtype=complex)
    support_indices = np.arange(-support_radius, support_radius + 1)
    values = rng.normal(size=support_indices.size) + 1j * rng.normal(
        size=support_indices.size
    )
    values /= np.linalg.norm(values)
    root[np.mod(support_indices, size)] = values

    root_fourier = np.fft.fft(root) / np.sqrt(size)
    multiplier = np.abs(root_fourier) ** 2
    offsets = np.arange(-(size // 2), size - size // 2)
    correlation = np.asarray(
        [
            np.vdot(root, np.roll(root, -int(offset)))
            for offset in offsets
        ],
        dtype=complex,
    )
    return root, multiplier, offsets, correlation


def toeplitz_covariance(
    projection: np.ndarray, first: np.ndarray, second: np.ndarray
) -> complex:
    identity = np.eye(projection.shape[0], dtype=complex)
    return complex(
        np.trace(
            projection
            @ np.diag(first)
            @ (identity - projection)
            @ np.diag(second)
            @ projection
        )
    )


def covariance_kernel_formula(
    projection: np.ndarray, first: np.ndarray, second: np.ndarray
) -> complex:
    first_difference = first[:, None] - first[None, :]
    second_difference = second[:, None] - second[None, :]
    kernel_mass = np.abs(projection) ** 2
    return complex(
        0.5 * np.sum(first_difference * second_difference * kernel_mass)
    )


def raw_mode_covariance(
    projection: np.ndarray,
    angles: np.ndarray,
    offset: int,
    displacement: float,
) -> complex:
    first = np.exp(-1j * offset * angles)
    second = np.exp(1j * displacement * angles)
    return toeplitz_covariance(projection, first, second)


def support_first_checks(
    size: int,
    support_radius: int,
    outer_rank: int,
    inner_rank: int,
    displacement: float,
    seed: int,
) -> tuple[dict[str, float], dict[str, np.ndarray | complex]]:
    outer, inner = random_nested_projections(
        size, outer_rank, inner_rank, seed
    )
    _, multiplier, offsets, correlation = compact_root(
        size, support_radius, seed + 1
    )
    angles = 2.0 * np.pi * np.arange(size) / size
    translation = np.exp(1j * displacement * angles)
    identity = np.eye(size, dtype=complex)

    reconstructed_multiplier = sum(
        (
            correlation[index]
            * np.exp(-1j * int(offset) * angles)
            for index, offset in enumerate(offsets)
        ),
        np.zeros(size, dtype=complex),
    ) / size
    support_mask = np.abs(offsets) <= 2 * support_radius
    support_leakage = float(
        np.max(np.abs(correlation[~support_mask]))
    )

    outer_direct = toeplitz_covariance(outer, multiplier, translation)
    inner_direct = toeplitz_covariance(inner, multiplier, translation)
    nested_direct = outer_direct - inner_direct
    outer_kernel = covariance_kernel_formula(
        outer, multiplier, translation
    )
    inner_kernel = covariance_kernel_formula(
        inner, multiplier, translation
    )

    outer_modes = np.asarray(
        [
            raw_mode_covariance(
                outer, angles, int(offset), displacement
            )
            for offset in offsets
        ],
        dtype=complex,
    )
    inner_modes = np.asarray(
        [
            raw_mode_covariance(
                inner, angles, int(offset), displacement
            )
            for offset in offsets
        ],
        dtype=complex,
    )
    signed_modes = outer_modes - inner_modes
    full_pairing = np.sum(correlation * signed_modes) / size
    support_pairing = (
        np.sum(correlation[support_mask] * signed_modes[support_mask])
        / size
    )
    support_terms = (
        correlation[support_mask] * signed_modes[support_mask] / size
    )
    support_cancellation_ratio = float(
        np.sum(np.abs(support_terms)) / max(abs(support_pairing), 1e-30)
    )
    branch_cancellation_ratio = float(
        (abs(outer_direct) + abs(inner_direct))
        / max(abs(nested_direct), 1e-30)
    )

    checks = {
        "outer projection error": relative_error(outer @ outer, outer),
        "inner projection error": relative_error(inner @ inner, inner),
        "nested projection error": relative_error(outer @ inner, inner),
        "root multiplier reconstruction error": relative_error(
            reconstructed_multiplier, multiplier
        ),
        "root correlation support leakage": support_leakage,
        "outer two-point kernel error": float(
            abs(outer_direct - outer_kernel)
        ),
        "inner two-point kernel error": float(
            abs(inner_direct - inner_kernel)
        ),
        "full distribution pairing error": float(
            abs(full_pairing - nested_direct)
        ),
        "support-first pairing error": float(
            abs(support_pairing - nested_direct)
        ),
        "zero first mode magnitude": float(
            abs(signed_modes[np.where(offsets == 0)[0][0]])
        ),
        "support-mode cancellation ratio": support_cancellation_ratio,
        "outer-inner cancellation ratio": branch_cancellation_ratio,
        "nested response magnitude": float(abs(nested_direct)),
    }
    data: dict[str, np.ndarray | complex] = {
        "outer": outer,
        "inner": inner,
        "multiplier": multiplier,
        "angles": angles,
        "offsets": offsets,
        "correlation": correlation,
        "support_mask": support_mask,
        "nested_response": nested_direct,
    }
    return checks, data


def local_euler_factor(
    angles: np.ndarray, prime: int, flow_time: float
) -> np.ndarray:
    amplitude = flow_time / np.sqrt(prime)
    phase = np.exp(1j * np.log(prime) * angles)
    return (1.0 - amplitude) / (1.0 - amplitude * phase)


def product_cocycle_checks(
    data: dict[str, np.ndarray | complex],
    primes: list[int],
    flow_time: float,
) -> dict[str, float]:
    if not all(is_prime(prime) for prime in primes):
        raise ValueError("every Euler factor parameter must be prime")
    outer = np.asarray(data["outer"])
    inner = np.asarray(data["inner"])
    multiplier = np.asarray(data["multiplier"])
    angles = np.asarray(data["angles"])

    factors = [
        local_euler_factor(angles, prime, flow_time) for prime in primes
    ]
    complete_product = np.prod(np.asarray(factors), axis=0)
    complete_difference = (
        complete_product[:, None] - complete_product[None, :]
    )

    cocycle_terms: list[np.ndarray] = []
    local_formula_errors: list[float] = []
    for index, (prime, factor) in enumerate(zip(primes, factors)):
        prefix = np.prod(np.asarray(factors[:index]), axis=0) if index else np.ones_like(factor)
        suffix = (
            np.prod(np.asarray(factors[index + 1 :]), axis=0)
            if index + 1 < len(factors)
            else np.ones_like(factor)
        )
        cocycle_terms.append(
            prefix[:, None]
            * (factor[:, None] - factor[None, :])
            * suffix[None, :]
        )

        amplitude = flow_time / np.sqrt(prime)
        phase = np.exp(1j * np.log(prime) * angles)
        denominator = 1.0 - amplitude * phase
        explicit_difference = (
            amplitude
            * (1.0 - amplitude)
            * (phase[:, None] - phase[None, :])
            / (denominator[:, None] * denominator[None, :])
        )
        local_formula_errors.append(
            relative_error(
                factor[:, None] - factor[None, :],
                explicit_difference,
            )
        )

    telescope = sum(cocycle_terms, np.zeros_like(complete_difference))
    signed_kernel_mass = np.abs(outer) ** 2 - np.abs(inner) ** 2
    multiplier_difference = (
        multiplier[:, None] - multiplier[None, :]
    )
    complete_scalar = complex(
        0.5
        * np.sum(
            multiplier_difference
            * complete_difference
            * signed_kernel_mass
        )
    )
    direct_scalar = toeplitz_covariance(
        outer, multiplier, complete_product
    ) - toeplitz_covariance(inner, multiplier, complete_product)
    channel_scalars = np.asarray(
        [
            0.5
            * np.sum(
                multiplier_difference * term * signed_kernel_mass
            )
            for term in cocycle_terms
        ],
        dtype=complex,
    )
    channel_cancellation_ratio = float(
        np.sum(np.abs(channel_scalars))
        / max(abs(np.sum(channel_scalars)), 1e-30)
    )

    return {
        "complete product contraction excess": float(
            max(np.max(np.abs(complete_product)) - 1.0, 0.0)
        ),
        "product cocycle telescope error": relative_error(
            telescope, complete_difference
        ),
        "local resolvent difference error": max(local_formula_errors),
        "direct versus two-point product error": float(
            abs(direct_scalar - complete_scalar)
        ),
        "prime-channel scalar telescope error": float(
            abs(np.sum(channel_scalars) - complete_scalar)
        ),
        "prime-channel cancellation ratio": channel_cancellation_ratio,
        "complete product response magnitude": float(abs(complete_scalar)),
    }


def projection_basis(projection: np.ndarray) -> np.ndarray:
    eigenvalues, eigenvectors = np.linalg.eigh(projection)
    return eigenvectors[:, eigenvalues > 0.5]


def transported_projection(
    projection: np.ndarray, transport: np.ndarray
) -> np.ndarray:
    basis = projection_basis(projection)
    frame = transport[:, None] * basis
    gram = frame.conj().T @ frame
    return frame @ np.linalg.inv(gram) @ frame.conj().T


def synchronized_transport_data(
    angles: np.ndarray, primes: list[int], flow_time: float
) -> tuple[np.ndarray, np.ndarray, list[np.ndarray]]:
    phases = [np.exp(1j * np.log(prime) * angles) for prime in primes]
    amplitudes = [prime**-0.5 for prime in primes]
    transport = np.prod(
        np.asarray(
            [
                1.0 - flow_time * amplitude * phase
                for amplitude, phase in zip(amplitudes, phases)
            ]
        ),
        axis=0,
    )
    local_generators = [
        -amplitude * phase / (1.0 - flow_time * amplitude * phase)
        for amplitude, phase in zip(amplitudes, phases)
    ]
    generator = np.sum(np.asarray(local_generators), axis=0)
    return transport, generator, local_generators


def synchronized_flow_checks(
    data: dict[str, np.ndarray | complex],
    primes: list[int],
    flow_time: float,
    quadrature_order: int,
) -> dict[str, float]:
    outer_0 = np.asarray(data["outer"])
    inner_0 = np.asarray(data["inner"])
    multiplier = np.asarray(data["multiplier"])
    angles = np.asarray(data["angles"])
    offsets = np.asarray(data["offsets"])
    correlation = np.asarray(data["correlation"])
    support_mask = np.asarray(data["support_mask"], dtype=bool)

    def projections_at(parameter: float) -> tuple[np.ndarray, np.ndarray]:
        transport, _, _ = synchronized_transport_data(
            angles, primes, parameter
        )
        return (
            transported_projection(outer_0, transport),
            transported_projection(inner_0, transport),
        )

    outer_end, inner_end = projections_at(flow_time)
    endpoint_response = complex(
        np.trace(
            np.diag(multiplier)
            @ ((outer_end - inner_end) - (outer_0 - inner_0))
        )
    )

    nodes, weights = np.polynomial.legendre.leggauss(quadrature_order)
    parameters = 0.5 * flow_time * (nodes + 1.0)
    scaled_weights = 0.5 * flow_time * weights
    integrated_response = 0.0j
    complex_real_errors: list[float] = []
    support_errors: list[float] = []
    prime_sum_errors: list[float] = []

    for parameter, weight in zip(parameters, scaled_weights):
        outer, inner = projections_at(float(parameter))
        _, generator, local_generators = synchronized_transport_data(
            angles, primes, float(parameter)
        )
        real_generator = generator.real

        complex_flow = 2.0 * np.real(
            toeplitz_covariance(outer, multiplier, generator)
            - toeplitz_covariance(inner, multiplier, generator)
        )
        real_flow = 2.0 * (
            toeplitz_covariance(outer, multiplier, real_generator)
            - toeplitz_covariance(inner, multiplier, real_generator)
        )
        complex_real_errors.append(float(abs(complex_flow - real_flow)))

        signed_modes = np.asarray(
            [
                toeplitz_covariance(
                    outer,
                    np.exp(-1j * int(offset) * angles),
                    real_generator,
                )
                - toeplitz_covariance(
                    inner,
                    np.exp(-1j * int(offset) * angles),
                    real_generator,
                )
                for offset in offsets
            ],
            dtype=complex,
        )
        support_pairing = (
            np.sum(
                correlation[support_mask] * signed_modes[support_mask]
            )
            / angles.size
        )
        support_errors.append(
            float(abs(support_pairing - 0.5 * real_flow))
        )

        prime_flow = sum(
            (
                2.0
                * (
                    toeplitz_covariance(
                        outer, multiplier, local_generator.real
                    )
                    - toeplitz_covariance(
                        inner, multiplier, local_generator.real
                    )
                )
                for local_generator in local_generators
            ),
            0.0j,
        )
        prime_sum_errors.append(float(abs(prime_flow - real_flow)))
        integrated_response += weight * real_flow

    midpoint = 0.5 * flow_time
    derivative_step = 2e-5
    outer_plus, inner_plus = projections_at(midpoint + derivative_step)
    outer_minus, inner_minus = projections_at(midpoint - derivative_step)
    numerical_derivative = np.trace(
        np.diag(multiplier)
        @ (
            (outer_plus - inner_plus)
            - (outer_minus - inner_minus)
        )
    ) / (2.0 * derivative_step)
    outer_mid, inner_mid = projections_at(midpoint)
    _, midpoint_generator, _ = synchronized_transport_data(
        angles, primes, midpoint
    )
    analytic_derivative = 2.0 * np.real(
        toeplitz_covariance(
            outer_mid, multiplier, midpoint_generator
        )
        - toeplitz_covariance(
            inner_mid, multiplier, midpoint_generator
        )
    )

    normalized_inverse_factors = [
        local_euler_factor(angles, prime, flow_time) for prime in primes
    ]
    static_product = np.prod(
        np.asarray(normalized_inverse_factors), axis=0
    )
    static_product_covariance = toeplitz_covariance(
        outer_0, multiplier, static_product
    ) - toeplitz_covariance(inner_0, multiplier, static_product)
    substitution_gap = float(
        abs(static_product_covariance - endpoint_response)
        / max(abs(endpoint_response), 1e-30)
    )

    return {
        "complex versus real generator error": max(complex_real_errors),
        "moving support-first pairing error": max(support_errors),
        "complete-kernel prime generator sum error": max(prime_sum_errors),
        "moving derivative finite-difference error": float(
            abs(numerical_derivative - analytic_derivative)
        ),
        "moving endpoint integration error": float(
            abs(integrated_response - endpoint_response)
        ),
        "static product substitution gap": substitution_gap,
        "moving endpoint response magnitude": float(abs(endpoint_response)),
    }


def half_power_guard(flow_time: float) -> dict[str, float]:
    primes = np.asarray([101, 1009, 10007, 100003, 1000003], dtype=float)
    amplitudes = flow_time / np.sqrt(primes)
    phase_x = np.exp(0.37j)
    phase_y = np.exp(-0.61j)
    differences = np.asarray(
        [
            abs(
                (1.0 - amplitude)
                / (1.0 - amplitude * phase_x)
                - (1.0 - amplitude)
                / (1.0 - amplitude * phase_y)
            )
            for amplitude in amplitudes
        ]
    )
    exponent = float(
        np.polyfit(np.log(amplitudes), np.log(differences), 1)[0]
    )
    half_power_ratios = differences / amplitudes
    full_power_ratios = differences / amplitudes**2
    return {
        "local amplitude exponent": exponent,
        "local half-power ratio minimum": float(np.min(half_power_ratios)),
        "local half-power ratio maximum": float(np.max(half_power_ratios)),
        "local full-power ratio at largest prime": float(full_power_ratios[-1]),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--size", type=int, default=32)
    parser.add_argument("--support-radius", type=int, default=3)
    parser.add_argument("--outer-rank", type=int, default=13)
    parser.add_argument("--inner-rank", type=int, default=7)
    parser.add_argument("--displacement", type=float, default=5.3)
    parser.add_argument("--seed", type=int, default=301)
    parser.add_argument(
        "--primes",
        type=parse_primes,
        default=parse_primes("2,3,5,7,11,13"),
    )
    parser.add_argument("--flow-time", type=float, default=0.82)
    parser.add_argument("--quadrature-order", type=int, default=24)
    parser.add_argument("--tolerance", type=float, default=2e-11)
    parser.add_argument("--derivative-tolerance", type=float, default=2e-8)
    parser.add_argument("--cancellation-floor", type=float, default=1.01)
    parser.add_argument("--substitution-gap-floor", type=float, default=0.05)
    args = parser.parse_args()

    support, data = support_first_checks(
        args.size,
        args.support_radius,
        args.outer_rank,
        args.inner_rank,
        args.displacement,
        args.seed,
    )
    product = product_cocycle_checks(data, args.primes, args.flow_time)
    moving = synchronized_flow_checks(
        data, args.primes, args.flow_time, args.quadrature_order
    )
    guard = half_power_guard(args.flow_time)

    print("identity=support-first two-point covariance cocycle")
    print("status=exact distribution owner; source strip estimate open")
    for title, checks in (
        ("support", support),
        ("product", product),
        ("moving", moving),
        ("guard", guard),
    ):
        print(f"{title}_checks=BEGIN")
        for label, value in checks.items():
            print(f"{label.replace(' ', '_')}={float(value):.12e}")
        print(f"{title}_checks=END")

    support_excluded = {
        "support-mode cancellation ratio",
        "outer-inner cancellation ratio",
        "nested response magnitude",
    }
    product_excluded = {
        "prime-channel cancellation ratio",
        "complete product response magnitude",
    }
    moving_excluded = {
        "moving derivative finite-difference error",
        "static product substitution gap",
        "moving endpoint response magnitude",
    }
    exact_errors = [
        value
        for label, value in support.items()
        if label not in support_excluded
    ] + [
        value
        for label, value in product.items()
        if label not in product_excluded
    ] + [
        value
        for label, value in moving.items()
        if label not in moving_excluded
    ]
    maximum_exact_error = max(float(value) for value in exact_errors)
    print(f"maximum_exact_error={maximum_exact_error:.12e}")
    if maximum_exact_error > args.tolerance:
        raise SystemExit(
            "support-first two-point certificate failed: "
            f"{maximum_exact_error:.6e}"
        )
    if support["support-mode cancellation ratio"] < args.cancellation_floor:
        raise SystemExit("support-mode cancellation guard did not fire")
    if product["prime-channel cancellation ratio"] < args.cancellation_floor:
        raise SystemExit("prime-channel cancellation guard did not fire")
    if (
        moving["moving derivative finite-difference error"]
        > args.derivative_tolerance
    ):
        raise SystemExit("synchronized moving derivative check failed")
    if (
        moving["static product substitution gap"]
        < args.substitution_gap_floor
    ):
        raise SystemExit("static product owner-mismatch guard did not fire")
    if not (0.95 <= guard["local amplitude exponent"] <= 1.05):
        raise SystemExit("local Euler difference is not at half-power scale")

    print("root_support_before_raw_modes=EXACT")
    print("nested_outer_minus_sonin_kernel=RECOMBINED")
    print("moving_kernel_prime_generator_sum=EXACT")
    print("static_complete_product_cocycle=EXACT_BUT_NOT_ROUTE_OWNER")
    print("primewise_absolute_values=FORBIDDEN")
    print("raw_point_trace=NOT_REQUIRED")
    print("combined_kernel_strip_estimate=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
