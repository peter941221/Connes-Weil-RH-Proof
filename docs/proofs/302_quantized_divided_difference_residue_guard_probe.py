#!/usr/bin/env python3
"""Certificate for Proof 302's Q-residue and divided-difference guard."""

from __future__ import annotations

import argparse

import numpy as np


TWO_PI = 2.0 * np.pi


def relative_error(
    actual: complex | np.ndarray, expected: complex | np.ndarray
) -> float:
    actual_array = np.asarray(actual)
    expected_array = np.asarray(expected)
    scale = max(float(np.linalg.norm(expected_array)), 1.0)
    return float(np.linalg.norm(actual_array - expected_array) / scale)


def sine_integral(argument: float) -> float:
    """Dependency-free Si approximation: power series then asymptotic tail."""
    if argument == 0.0:
        return 0.0
    sign = 1.0 if argument > 0.0 else -1.0
    value = abs(argument)
    if value < 16.0:
        term = value
        total = term
        for index in range(1, 220):
            term *= -value**2 * (2 * index - 1) / (
                (2 * index) * (2 * index + 1) ** 2
            )
            total += term
            if abs(term) < 2e-17 * max(abs(total), 1.0):
                break
        return sign * float(total)

    first = 1.0 / value
    odd = first
    odd_total = odd
    even = 1.0 / value**2
    even_total = even
    previous_odd = abs(odd)
    previous_even = abs(even)
    for index in range(1, 30):
        odd *= -(2 * index) * (2 * index - 1) / value**2
        if abs(odd) > previous_odd:
            break
        odd_total += odd
        previous_odd = abs(odd)
    for index in range(1, 30):
        even *= -(2 * index + 1) * (2 * index) / value**2
        if abs(even) > previous_even:
            break
        even_total += even
        previous_even = abs(even)
    result = np.pi / 2.0 - np.cos(value) * odd_total - np.sin(value) * even_total
    return sign * float(result)


def sine_integral_quotient(argument: float) -> float:
    if abs(argument) < 1e-4:
        square = argument * argument
        return float(
            1.0 - square / 18.0 + square**2 / 600.0 - square**3 / 35280.0
        )
    return float(sine_integral(argument) / argument)


def sine_integral_quotient_derivative(argument: float) -> float:
    if abs(argument) < 1e-4:
        square = argument * argument
        return float(
            -argument / 9.0
            + argument * square / 150.0
            - argument * square**2 / 5880.0
        )
    integral = sine_integral(argument)
    return float((np.sin(argument) - integral) / argument**2)


def sine_integral_quotient_second_derivative(argument: float) -> float:
    if abs(argument) < 1e-4:
        square = argument * argument
        return float(-1.0 / 9.0 + square / 50.0 - square**2 / 1176.0)
    integral = sine_integral(argument)
    numerator = np.sin(argument) - integral
    return float(
        (np.cos(argument) - np.sin(argument) / argument) / argument**2
        - 2.0 * numerator / argument**3
    )


def branch_sum(rho: float) -> float:
    return sine_integral_quotient(TWO_PI * (1.0 + rho)) + sine_integral_quotient(
        TWO_PI * (rho - 1.0)
    )


def branch_sum_derivative(rho: float) -> float:
    return TWO_PI * (
        sine_integral_quotient_derivative(TWO_PI * (1.0 + rho))
        + sine_integral_quotient_derivative(TWO_PI * (rho - 1.0))
    )


def branch_sum_second_derivative(rho: float) -> float:
    return TWO_PI**2 * (
        sine_integral_quotient_second_derivative(TWO_PI * (1.0 + rho))
        + sine_integral_quotient_second_derivative(TWO_PI * (rho - 1.0))
    )


def delta_value(rho: float) -> float:
    if rho <= 0.0:
        raise ValueError("rho must be positive")
    if rho < 1.0:
        return delta_value(1.0 / rho)
    return float(2.0 * np.sqrt(rho) * branch_sum(rho))


def delta_rho_derivative_at_one() -> float:
    rho = 1.0
    return float(
        branch_sum(rho) / np.sqrt(rho)
        + 2.0 * np.sqrt(rho) * branch_sum_derivative(rho)
    )


def qdelta_regular(rho: float) -> float:
    if rho < 1.0:
        rho = 1.0 / rho
    return float(
        -4.0 * rho ** 1.5 * branch_sum_derivative(rho)
        - 2.0 * rho ** 2.5 * branch_sum_second_derivative(rho)
    )


def compact_test(value: float, radius: float) -> float:
    if abs(value) >= radius:
        return 0.0
    normalized = value / radius
    return float((1.0 - normalized**2) ** 4)


def compact_test_second_derivative(value: float, radius: float) -> float:
    if abs(value) >= radius:
        return 0.0
    normalized = value / radius
    return float(
        8.0
        * (1.0 - normalized**2) ** 2
        * (7.0 * normalized**2 - 1.0)
        / radius**2
    )


def gauss_integral(function, radius: float, order: int) -> float:
    nodes, weights = np.polynomial.legendre.leggauss(order)
    points = 0.5 * radius * (nodes + 1.0)
    values = np.asarray([function(float(point)) for point in points])
    return float(0.5 * radius * np.sum(weights * values))


def residue_checks(
    maximum_rho: float, test_radius: float, quadrature_order: int
) -> dict[str, float]:
    right_derivative = delta_rho_derivative_at_one()
    derivative_jump = 2.0 * right_derivative

    weak_left = 2.0 * gauss_integral(
        lambda value: delta_value(np.exp(value))
        * (
            -compact_test_second_derivative(value, test_radius)
            + 0.25 * compact_test(value, test_radius)
        ),
        test_radius,
        quadrature_order,
    )
    weak_right = -2.0 * compact_test(0.0, test_radius) + 2.0 * gauss_integral(
        lambda value: qdelta_regular(np.exp(value))
        * compact_test(value, test_radius),
        test_radius,
        quadrature_order,
    )

    pre_q_scaled = np.sqrt(maximum_rho) * abs(delta_value(maximum_rho))
    post_q_value = qdelta_regular(maximum_rho)
    post_q_half_power_ratio = np.sqrt(maximum_rho) * abs(post_q_value)

    return {
        "right logarithmic derivative error": abs(right_derivative - 1.0),
        "derivative jump error": abs(derivative_jump - 2.0),
        "weak Dirac split error": abs(weak_left - weak_right),
        "pre-Q half-power scaled magnitude": float(pre_q_scaled),
        "post-Q regular value magnitude": float(abs(post_q_value)),
        "post-Q half-power rejection ratio": float(post_q_half_power_ratio),
        "weak test value magnitude": float(abs(weak_left)),
    }


def divided_difference(
    values: np.ndarray, nodes: np.ndarray
) -> np.ndarray:
    difference = nodes[:, None] - nodes[None, :]
    value_difference = values[:, None] - values[None, :]
    result = np.zeros_like(difference, dtype=complex)
    mask = ~np.eye(nodes.size, dtype=bool)
    result[mask] = value_difference[mask] / difference[mask]
    return result


def quantized_differential_checks(size: int) -> dict[str, float]:
    nodes = np.linspace(-4.0, 4.0, size)
    first = np.exp(-0.2 * nodes**2) * (1.0 + 0.1 * nodes)
    second = np.sin(1.3 * nodes) + 0.15 * np.cos(0.7 * nodes)
    identity_values = np.ones_like(nodes)

    difference = nodes[:, None] - nodes[None, :]
    off_diagonal = ~np.eye(size, dtype=bool)
    hilbert = np.zeros((size, size), dtype=complex)
    hilbert[off_diagonal] = -1j / (np.pi * difference[off_diagonal])

    first_diagonal = np.diag(first)
    second_diagonal = np.diag(second)
    first_commutator = hilbert @ first_diagonal - first_diagonal @ hilbert
    second_commutator = hilbert @ second_diagonal - second_diagonal @ hilbert
    expected_first = 1j / np.pi * divided_difference(first, nodes)
    expected_second = 1j / np.pi * divided_difference(second, nodes)

    direct_pairing = np.trace(
        first_commutator.conj().T @ second_commutator
    )
    kernel_pairing = np.sum(
        np.conj(expected_first) * expected_second
    )

    central = 0.37
    step = 2e-5

    def smooth_function(value: float) -> float:
        return float(np.exp(-0.2 * value**2) * (1.0 + 0.1 * value))

    smooth_derivative = float(
        np.exp(-0.2 * central**2)
        * (0.1 - 0.4 * central * (1.0 + 0.1 * central))
    )
    centered_divided_difference = (
        smooth_function(central + step) - smooth_function(central - step)
    ) / (2.0 * step)
    constant_commutator = hilbert @ np.diag(identity_values) - np.diag(
        identity_values
    ) @ hilbert

    return {
        "first divided-difference kernel error": relative_error(
            first_commutator, expected_first
        ),
        "second divided-difference kernel error": relative_error(
            second_commutator, expected_second
        ),
        "double commutator pairing error": float(
            abs(direct_pairing - kernel_pairing)
        ),
        "constant mode commutator magnitude": float(
            np.linalg.norm(constant_commutator)
        ),
        "diagonal removable-singularity error": float(
            abs(centered_divided_difference - smooth_derivative)
        ),
        "quantized pairing magnitude": float(abs(direct_pairing)),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--maximum-rho", type=float, default=1024.0)
    parser.add_argument("--test-radius", type=float, default=2.0)
    parser.add_argument("--matrix-size", type=int, default=36)
    parser.add_argument("--quadrature-order", type=int, default=800)
    parser.add_argument("--tolerance", type=float, default=2e-8)
    parser.add_argument("--post-q-rejection-floor", type=float, default=100.0)
    args = parser.parse_args()

    residue = residue_checks(
        args.maximum_rho, args.test_radius, args.quadrature_order
    )
    quantized = quantized_differential_checks(args.matrix_size)

    print("identity=Q-residue split plus quantized divided difference")
    print("status=naive global strip rejected; source kernel route retained")
    for title, checks in (("residue", residue), ("quantized", quantized)):
        print(f"{title}_checks=BEGIN")
        for label, value in checks.items():
            print(f"{label.replace(' ', '_')}={float(value):.12e}")
        print(f"{title}_checks=END")

    residue_excluded = {
        "pre-Q half-power scaled magnitude",
        "post-Q regular value magnitude",
        "post-Q half-power rejection ratio",
        "weak test value magnitude",
    }
    quantized_excluded = {"quantized pairing magnitude"}
    exact_errors = [
        value
        for label, value in residue.items()
        if label not in residue_excluded
    ] + [
        value
        for label, value in quantized.items()
        if label not in quantized_excluded
    ]
    maximum_exact_error = max(float(value) for value in exact_errors)
    print(f"maximum_exact_error={maximum_exact_error:.12e}")
    if maximum_exact_error > args.tolerance:
        raise SystemExit(
            "Q-residue/divided-difference certificate failed: "
            f"{maximum_exact_error:.6e}"
        )
    if (
        residue["post-Q half-power rejection ratio"]
        < args.post_q_rejection_floor
    ):
        raise SystemExit("post-Q global half-power rejection guard did not fire")

    print("pre_Q_static_half_power=RETAINED")
    print("post_Q_distribution=-2_DIRAC_PLUS_REGULAR")
    print("post_Q_global_half_power=REJECTED")
    print("quantized_divided_difference=EXACT")
    print("diagonal_singularity=REMOVABLE_AFTER_DIFFERENCE")
    print("proof301_contour_successor=REPLACED_BY_QUANTIZED_KERNEL_ROUTE")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
