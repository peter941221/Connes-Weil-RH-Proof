#!/usr/bin/env python3
"""Reconnaissance for the CC20 multiplier bound used in Proof 213.

This script is not an interval certificate.  It evaluates

    ell(t) = 2 theta'(t) + delta_hat(t)

from the formulas in CC20 and scans a user-selected compact interval.  It also
checks the cell-decomposition margins with exact rational bounds.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
import math
import warnings

import numpy as np
from scipy.integrate import IntegrationWarning, quad
from scipy.special import digamma, sici


def sine_integral_quotient(argument: float) -> float:
    if abs(argument) < 1e-7:
        return 1.0 - argument * argument / 18.0
    return float(sici(argument)[0] / argument)


def delta_log_coordinate(log_rho: float) -> float:
    rho = math.exp(log_rho)
    return 2.0 * math.exp(log_rho / 2.0) * (
        sine_integral_quotient(2.0 * math.pi * (1.0 + rho))
        + sine_integral_quotient(2.0 * math.pi * (rho - 1.0))
    )


def delta_hat(t: float, integration_cutoff: float) -> tuple[float, float]:
    segment_width = 0.5
    segment_count = math.ceil(integration_cutoff / segment_width)
    value = 0.0
    error = 0.0
    for segment in range(segment_count):
        lower = segment * segment_width
        upper = min(integration_cutoff, (segment + 1) * segment_width)
        segment_value, segment_error = quad(
            delta_log_coordinate,
            lower,
            upper,
            weight="cos",
            wvar=t,
            epsabs=1e-11,
            epsrel=1e-11,
            limit=500,
        )
        value += segment_value
        error += segment_error
    # CC20 proves delta(exp(x))=exp(-x/2)+O(exp(-3x/2)).  Integrate the
    # leading tail exactly; the O(exp(-3x/2)) remainder is intentionally not
    # promoted to a certified error bound in this reconnaissance script.
    alpha = 0.5
    denominator = alpha * alpha + t * t
    leading_tail = math.exp(-alpha * integration_cutoff) * (
        alpha * math.cos(t * integration_cutoff)
        - t * math.sin(t * integration_cutoff)
    ) / denominator
    return 2.0 * (value + leading_tail), 2.0 * error


def cc20_multiplier(t: float, integration_cutoff: float) -> tuple[float, float]:
    two_theta_prime = (
        -math.log(math.pi) + float(digamma(0.25 + 0.5j * t).real)
    )
    delta_value, delta_error = delta_hat(t, integration_cutoff)
    return two_theta_prime + delta_value, delta_error


def exact_cell_margins() -> tuple[Fraction, Fraction]:
    q_upper = Fraction(708, 1000)
    q_lower = Fraction(707, 1000)
    log_two_upper = Fraction(7, 10)
    log_two_lower = Fraction(693, 1000)

    degree_upper = log_two_upper * (
        2 * (q_upper + q_upper**2 + q_upper**3) + q_upper**4
    )
    average_block_upper = (
        degree_upper - 8 * log_two_lower * q_lower**7
    )
    average_margin = 2 - average_block_upper

    poincare_lower = Fraction(3**2, 50) / log_two_upper**2
    residual_margin = 2 - degree_upper + poincare_lower
    return average_margin, residual_margin


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--t-max", type=float, default=50.0)
    parser.add_argument("--step", type=float, default=0.1)
    parser.add_argument("--refine-max", type=float, default=0.5)
    parser.add_argument("--refine-step", type=float, default=0.005)
    parser.add_argument("--integration-cutoff", type=float, default=12.0)
    args = parser.parse_args()

    warnings.filterwarnings("ignore", category=IntegrationWarning)
    coarse = np.arange(0.0, args.t_max + args.step / 2.0, args.step)
    refined = np.arange(
        0.0,
        args.refine_max + args.refine_step / 2.0,
        args.refine_step,
    )
    points = np.unique(np.concatenate((coarse, refined)))

    best_value = math.inf
    best_t = math.nan
    largest_reported_error = 0.0
    for point in points:
        value, error = cc20_multiplier(
            float(point), args.integration_cutoff
        )
        largest_reported_error = max(largest_reported_error, error)
        if value < best_value:
            best_value = value
            best_t = float(point)

    average_margin, residual_margin = exact_cell_margins()
    print(f"scan_points={len(points)}")
    print(f"scan_interval=[0,{args.t_max}]")
    print(f"minimum_sample={best_value:.15f}")
    print(f"minimum_location={best_t:.6f}")
    print(f"sample_margin_over_1_50={best_value - 1 / 50:.15f}")
    print(f"largest_quad_error_estimate={largest_reported_error:.3e}")
    print(f"average_block_rational_margin={average_margin}")
    print(f"average_block_margin={float(average_margin):.15f}")
    print(f"residual_block_rational_margin={residual_margin}")
    print(f"residual_block_margin={float(residual_margin):.15f}")


if __name__ == "__main__":
    main()
