#!/usr/bin/env python3
"""Check the central obstruction from Proof 223.

The finite Euler phase has coefficients

    c_1 = -a,
    c_(-j) = (1-a**2) a**j,  j >= 0.

Its equal-cutoff positive angle has central coefficient a**2 log(p).  The
orthogonal metric relative projection has zero central diagonal sum.  The
script checks both facts from finite sums/matrices and prints the Gaussian
post-Q growth a**2 log(p) (t**2 + 3/4).
"""

from __future__ import annotations

import argparse
import math

import numpy as np


def parse_integers(raw: str) -> list[int]:
    return [int(item.strip()) for item in raw.split(",") if item.strip()]


def phase_central_partial(
    parameter: float, cell_length: float, cutoff: int
) -> float:
    coefficient_scale = (1.0 - parameter**2) ** 2
    return coefficient_scale * cell_length * sum(
        index * parameter ** (2 * index)
        for index in range(1, cutoff + 1)
    )


def metric_central_sum(parameter: float, radius: int) -> tuple[float, float]:
    indices = np.arange(-1, radius + 1)
    size = len(indices)
    transfer = np.zeros((size, radius + 1), dtype=float)
    for column, index in enumerate(range(radius + 1)):
        transfer[index + 1, column] = 1.0
        transfer[index, column] = -parameter

    gram = transfer.T @ transfer
    projection = transfer @ np.linalg.solve(gram, transfer.T)
    base_projection = np.diag((indices >= 0).astype(float))
    difference = projection - base_projection
    central_sum = float(np.trace(difference))
    idempotence_error = float(
        np.linalg.norm(projection @ projection - projection, ord=2)
    )
    return central_sum, idempotence_error


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--primes", default="2,3,101")
    parser.add_argument("--cutoffs", default="4,8,16,32,64")
    parser.add_argument("--metric-radius", type=int, default=64)
    parser.add_argument("--max-error", type=float, default=1e-12)
    args = parser.parse_args()

    primes = parse_integers(args.primes)
    cutoffs = parse_integers(args.cutoffs)
    if not primes or min(primes) < 2:
        raise ValueError("primes must contain integers at least 2")
    if not cutoffs or min(cutoffs) < 1:
        raise ValueError("cutoffs must be positive")

    worst_phase_error = 0.0
    worst_metric_center = 0.0
    print("identity=semilocal angle trace-class lift obstruction")
    for prime in primes:
        parameter = 1.0 / math.sqrt(prime)
        cell_length = math.log(prime)
        expected_center = parameter**2 * cell_length
        metric_center, idempotence_error = metric_central_sum(
            parameter, args.metric_radius
        )

        print(
            f"prime={prime} a={parameter:.12g} L={cell_length:.12g} "
            f"expected_angle_center={expected_center:.12g} "
            f"metric_center={metric_center:+.3e} "
            f"idempotence_error={idempotence_error:.3e}"
        )
        for cutoff in cutoffs:
            partial = phase_central_partial(
                parameter, cell_length, cutoff
            )
            error = abs(partial - expected_center)
            print(
                f"  cutoff={cutoff} partial_center={partial:.12g} "
                f"error={error:.3e}"
            )
            if cutoff == cutoffs[-1]:
                worst_phase_error = max(worst_phase_error, error)

        residual_center = expected_center - metric_center
        print(f"  residual_center={residual_center:.12g}")
        for modulation in (0.0, 4.0, 16.0, 64.0):
            post_q = residual_center * (modulation**2 + 0.75)
            scale_ratio = (
                post_q / (expected_center * modulation**2)
                if modulation > 0
                else float("nan")
            )
            print(
                f"  modulation={modulation:4.0f} "
                f"post_q_center={post_q:.12g} "
                f"growth_ratio={scale_ratio:.9f}"
            )

        worst_metric_center = max(worst_metric_center, abs(metric_center))

    print(f"worst_finest_phase_error={worst_phase_error:.3e}")
    print(f"worst_metric_center={worst_metric_center:.3e}")
    if worst_phase_error > args.max_error:
        raise RuntimeError("finite-phase center did not converge sufficiently")
    if worst_metric_center > args.max_error:
        raise RuntimeError("metric projection acquired a central coefficient")
    print("certificate=PASS")


if __name__ == "__main__":
    main()
