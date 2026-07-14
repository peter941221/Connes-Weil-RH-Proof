#!/usr/bin/env python3
"""Check the target-zero weighted-Chebyshev pairing from Proof 221.

The script builds one compactly supported complex test h whose bilateral
Laplace transform H satisfies the three source rows

    H(-1/2) = H(0) = H(1/2) = 0

and the off-critical orbit values

    H(u) = 1, H(-conj(u)) = -1, H(conj(u)) = H(-u) = 0.

It independently computes the autocorrelation F_h and checks

    integral exp(v*b) F_h(b) db
      = conj(H(-conj(v))) H(v),

the opposite-pair identity, and the outer minus sign from the zero residue in
the Chebyshev defect.  This is a numerical sign/conjugation guard; the proof is
the residue calculation in the companion note.
"""

from __future__ import annotations

import argparse
import math

import numpy as np
from numpy.polynomial.legendre import leggauss


def parse_sizes(raw: str) -> list[int]:
    return [int(item.strip()) for item in raw.split(",") if item.strip()]


def compact_bump(points: np.ndarray, radius: float) -> np.ndarray:
    values = np.zeros(points.shape, dtype=float)
    scaled = points / radius
    inside = np.abs(scaled) < 1.0
    values[inside] = np.exp(-1.0 / (1.0 - scaled[inside] ** 2))
    return values


def bump_laplace(
    value: complex, radius: float, quadrature_order: int
) -> complex:
    nodes, weights = leggauss(quadrature_order)
    points = radius * nodes
    values = np.exp(-1.0 / (1.0 - nodes**2))
    return radius * np.sum(weights * np.exp(value * points) * values)


def interpolation_data(
    u: complex,
    centers: np.ndarray,
    radius: float,
    quadrature_order: int,
) -> tuple[np.ndarray, np.ndarray, np.ndarray, float]:
    source_nodes = np.array([-0.5, 0.0, 0.5], dtype=complex)
    orbit_nodes = np.array(
        [u, -np.conjugate(u), np.conjugate(u), -u], dtype=complex
    )
    nodes = np.concatenate((source_nodes, orbit_nodes))
    targets = np.array([0, 0, 0, 1, -1, 0, 0], dtype=complex)
    bump_values = np.array(
        [bump_laplace(v, radius, quadrature_order) for v in nodes]
    )
    if np.min(np.abs(bump_values)) < 1e-12:
        raise RuntimeError("base bump transform is too small at a constraint")

    exponential_matrix = np.exp(nodes[:, None] * centers[None, :])
    coefficients = np.linalg.solve(exponential_matrix, targets / bump_values)
    condition_number = float(np.linalg.cond(exponential_matrix))
    return nodes, targets, coefficients, condition_number


def exact_transform(
    value: complex,
    centers: np.ndarray,
    coefficients: np.ndarray,
    radius: float,
    quadrature_order: int,
) -> complex:
    bump_value = bump_laplace(value, radius, quadrature_order)
    return bump_value * np.sum(coefficients * np.exp(value * centers))


def sampled_test(
    points: np.ndarray,
    centers: np.ndarray,
    coefficients: np.ndarray,
    radius: float,
) -> np.ndarray:
    result = np.zeros(points.shape, dtype=complex)
    for center, coefficient in zip(centers, coefficients):
        result += coefficient * compact_bump(points - center, radius)
    return result


def linear_autocorrelation(values: np.ndarray, step: float) -> np.ndarray:
    size = len(values)
    transform_size = 1 << (2 * size - 2).bit_length()
    spectrum = np.fft.fft(values, transform_size)
    circular = np.fft.ifft(spectrum * np.conjugate(spectrum))
    ordered = np.concatenate((circular[-(size - 1) :], circular[:size]))
    return step * ordered


def relative_error(left: complex, right: complex) -> float:
    return float(abs(left - right) / max(1.0, abs(right)))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--sizes", default="1001,2001,4001,8001")
    parser.add_argument("--u-real", type=float, default=0.23)
    parser.add_argument("--u-imag", type=float, default=2.7)
    parser.add_argument("--domain-radius", type=float, default=1.5)
    parser.add_argument("--bump-radius", type=float, default=0.12)
    parser.add_argument("--quadrature-order", type=int, default=256)
    parser.add_argument("--max-relative-error", type=float, default=5e-4)
    args = parser.parse_args()

    sizes = parse_sizes(args.sizes)
    if not sizes or min(sizes) < 101:
        raise ValueError("sizes must contain grid sizes at least 101")
    u = complex(args.u_real, args.u_imag)
    if args.u_real == 0.0 or args.u_imag == 0.0:
        raise ValueError("u must be nonreal and off the centered critical line")

    centers = np.linspace(-1.1, 1.1, 7)
    if np.max(np.abs(centers)) + args.bump_radius >= args.domain_radius:
        raise ValueError("translated bumps must lie strictly inside the domain")

    nodes, targets, coefficients, condition_number = interpolation_data(
        u, centers, args.bump_radius, args.quadrature_order
    )
    transform_values = np.array(
        [
            exact_transform(
                v,
                centers,
                coefficients,
                args.bump_radius,
                args.quadrature_order,
            )
            for v in nodes
        ]
    )
    interpolation_residual = float(np.max(np.abs(transform_values - targets)))

    orbit = np.array(
        [u, -u, np.conjugate(u), -np.conjugate(u)], dtype=complex
    )

    def h_transform(value: complex) -> complex:
        return exact_transform(
            value,
            centers,
            coefficients,
            args.bump_radius,
            args.quadrature_order,
        )

    def phi_product(value: complex) -> complex:
        return np.conjugate(h_transform(-np.conjugate(value))) * h_transform(
            value
        )

    product_zero_sum = sum(phi_product(v) for v in orbit)
    product_defect = -product_zero_sum

    print("identity=target-zero weighted-Chebyshev pairing")
    print(f"u={u.real:+.6g}{u.imag:+.6g}j")
    print(f"interpolation_condition_number={condition_number:.6e}")
    print(f"interpolation_max_residual={interpolation_residual:.6e}")
    print(
        "product_orbit_zero_sum="
        f"{product_zero_sum.real:+.12g}{product_zero_sum.imag:+.12g}j"
    )
    print(
        "product_orbit_defect="
        f"{product_defect.real:+.12g}{product_defect.imag:+.12g}j"
    )

    finest_pair_error = math.inf
    finest_defect_error = math.inf
    previous_pair_error = None
    previous_defect_error = None

    for size in sizes:
        points = np.linspace(-args.domain_radius, args.domain_radius, size)
        step = float(points[1] - points[0])
        values = sampled_test(
            points, centers, coefficients, args.bump_radius
        )
        autocorrelation = linear_autocorrelation(values, step)
        lags = step * np.arange(-(size - 1), size)

        correlation_phi = {
            value: step
            * np.sum(np.exp(value * lags) * autocorrelation)
            for value in orbit
        }
        factorization_error = max(
            relative_error(correlation_phi[v], phi_product(v)) for v in orbit
        )

        midpoint = size - 1
        nonnegative_lags = lags[midpoint:]
        f_positive = autocorrelation[midpoint:]
        f_negative = autocorrelation[midpoint::-1]
        symmetric_correlation = f_positive + f_negative
        pair_integrand = (
            np.exp(u * nonnegative_lags)
            + np.exp(-u * nonnegative_lags)
        ) * symmetric_correlation
        pair_integral = np.trapz(pair_integrand, nonnegative_lags)
        pair_product = phi_product(u) + phi_product(-u)
        pair_error = relative_error(pair_integral, pair_product)

        correlation_zero_sum = sum(correlation_phi[v] for v in orbit)
        correlation_defect = -correlation_zero_sum
        defect_error = relative_error(correlation_defect, 2.0 + 0.0j)

        pair_ratio = (
            previous_pair_error / pair_error
            if previous_pair_error is not None and pair_error > 0
            else float("nan")
        )
        defect_ratio = (
            previous_defect_error / defect_error
            if previous_defect_error is not None and defect_error > 0
            else float("nan")
        )
        print(
            f"size={size} "
            f"factorization_error={factorization_error:.6e} "
            f"pair_error={pair_error:.6e} "
            f"pair_refinement_ratio={pair_ratio:.3f} "
            f"defect={correlation_defect.real:+.10f}"
            f"{correlation_defect.imag:+.3e}j "
            f"defect_error={defect_error:.6e} "
            f"defect_refinement_ratio={defect_ratio:.3f}"
        )

        previous_pair_error = pair_error
        previous_defect_error = defect_error
        finest_pair_error = pair_error
        finest_defect_error = defect_error

    if condition_number > 1e10:
        raise RuntimeError("interpolation system is too ill-conditioned")
    if interpolation_residual > 1e-9:
        raise RuntimeError("orbit/source interpolation residual is too large")
    if relative_error(product_zero_sum, -2.0 + 0.0j) > 1e-9:
        raise RuntimeError("product formula did not give orbit zero sum -2")
    if finest_pair_error > args.max_relative_error:
        raise RuntimeError("opposite-pair identity did not converge sufficiently")
    if finest_defect_error > args.max_relative_error:
        raise RuntimeError("full-orbit defect did not converge to +2")
    print("certificate=PASS")


if __name__ == "__main__":
    main()
