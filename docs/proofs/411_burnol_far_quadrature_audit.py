"""Audit the far-tail quadrature used by Proof 409.

The complete inverse metric is a positive Hermitian compression

    G_S = integral A* U_z A d nu_S(z).

Proof 409 evaluates the far part of this integral with a fixed-order
Gauss-Legendre rule.  The cosine block of A* U_z A contains frequencies
2*pi*exp(abs(z)); the audit therefore records positivity, Hermitian error,
and response variation as the quadrature order and geometric cutoff change.

This is a numerical validity guard.  It does not estimate the continuous
Gate 3U response.
"""

from __future__ import annotations

import argparse
import importlib.util
import math
import sys
from pathlib import Path

import numpy as np


def load_screen_module():
    path = Path(__file__).with_name(
        "409_burnol_near_weighted_gradient_screen.py"
    )
    specification = importlib.util.spec_from_file_location(
        "proof409_screen", path
    )
    if specification is None or specification.loader is None:
        raise RuntimeError(f"cannot load {path.name}")
    module = importlib.util.module_from_spec(specification)
    sys.modules[specification.name] = module
    specification.loader.exec_module(module)
    return module


SCREEN = load_screen_module()


def parse_ints(value: str) -> list[int]:
    return [int(item) for item in value.split(",") if item]


def approximate_metric(
    size: int,
    primes: list[int],
    grid_step: float,
    maximum_power: int,
    integration_order: int,
) -> dict[str, float]:
    evaluator = SCREEN.MomentEvaluator(size, integration_order)
    law, origin, omitted_mass = SCREEN.euler_difference_law(
        primes, grid_step, maximum_power
    )
    displacements = (np.arange(law.size) - origin) * grid_step
    metric = np.zeros((2 * size, 2 * size), dtype=complex)
    for displacement, probability in zip(displacements, law):
        if probability == 0.0:
            continue
        metric += probability * evaluator.moment(float(displacement))

    hermitian_part = (metric + metric.conj().T) / 2.0
    metric_norm = max(float(np.linalg.norm(metric, ord=2)), 1e-30)
    eigenvalues = np.linalg.eigvalsh(hermitian_part)
    return {
        "omitted_mass": float(omitted_mass),
        "maximum_frequency": float(
            2.0 * math.pi * math.exp(float(np.max(np.abs(displacements))))
        ),
        "metric_norm": metric_norm,
        "hermitian_error": float(
            np.linalg.norm(metric - metric.conj().T, ord=2) / metric_norm
        ),
        "minimum_eigenvalue": float(eigenvalues[0]),
        "maximum_eigenvalue": float(eigenvalues[-1]),
        "negative_part": float(max(0.0, -eigenvalues[0])),
        "condition_number": float(np.linalg.cond(metric)),
    }


def response_row(
    size: int,
    primes: list[int],
    radius: float,
    root_quadrature_order: int,
    integration_order: int,
    grid_step: float,
    maximum_power: int,
) -> dict[str, float]:
    row = SCREEN.screen_one(
        primes,
        size,
        radius,
        root_quadrature_order,
        integration_order,
        grid_step,
        maximum_power,
    )
    return {
        "near_response": float(row["near_response"]),
        "normalized_response": float(
            row["near_response_over_root_budget_sq"]
        ),
        "full_condition_number": float(row["full_gram_condition"]),
    }


def print_row(
    maximum_power: int,
    integration_order: int,
    metric: dict[str, float],
    response: dict[str, float],
) -> None:
    print(
        f"power={maximum_power:2d} order={integration_order:3d} "
        f"maxfreq={metric['maximum_frequency']:.3e} "
        f"tail={metric['omitted_mass']:.3e} "
        f"herm_err={metric['hermitian_error']:.3e} "
        f"eig_min={metric['minimum_eigenvalue']:+.3e} "
        f"eig_max={metric['maximum_eigenvalue']:+.3e} "
        f"neg={metric['negative_part']:.3e} "
        f"metric_cond={metric['condition_number']:.3e} "
        f"response={response['near_response']:+.6e} "
        f"normalized={response['normalized_response']:.6e} "
        f"full_cond={response['full_condition_number']:.3e}"
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--size", type=int, default=6)
    parser.add_argument("--primes", default="2,3,5,7")
    parser.add_argument("--grid-step", type=float, default=0.2)
    parser.add_argument("--maximum-powers", default="6,8,10")
    parser.add_argument("--integration-orders", default="32,64,128")
    parser.add_argument("--radius", type=float, default=1.0)
    parser.add_argument("--root-quadrature-order", type=int, default=20)
    args = parser.parse_args()

    primes = parse_ints(args.primes)
    maximum_powers = parse_ints(args.maximum_powers)
    integration_orders = parse_ints(args.integration_orders)
    print("Proof 411 Burnol far-tail quadrature audit")
    print(f"size={args.size} primes={','.join(map(str, primes))}")
    print("exact_metric_should_be=Hermitian_positive_semidefinite")
    print("table=BEGIN")
    for maximum_power in maximum_powers:
        for integration_order in integration_orders:
            metric = approximate_metric(
                args.size,
                primes,
                args.grid_step,
                maximum_power,
                integration_order,
            )
            response = response_row(
                args.size,
                primes,
                args.radius,
                args.root_quadrature_order,
                integration_order,
                args.grid_step,
                maximum_power,
            )
            print_row(maximum_power, integration_order, metric, response)
    print("table=END")
    print("far_cosine_quadrature=UNDER_RESOLVED")
    print("proof409_quantitative_screen=WITHDRAWN_AS_UNCERTIFIED")
    print("continuous_gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
