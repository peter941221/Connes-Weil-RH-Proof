#!/usr/bin/env python3
"""Screen the prime-power crossing Gram of a canonical Xi quotient model.

For a known critical-line zero gamma, use the removable quotient

    H_gamma(t) = xi(1/2+it) / (t^2-gamma^2).

Its normalized autocorrelation is the cosine transform of |H_gamma|^2.  The
same-square crossing Gram at logarithmic prime-power shifts is

    G_ij = min(log q_i, log q_j) F(log q_j-log q_i).

The Euler-log pre-crossing weight for q=p^m is 1/(m sqrt(q)).  The reported
quantity w^T G^-1 w is a numerical Riesz-cost screen.  It is not an RH
certificate and is not a theorem about a hypothetical off-line zero.
"""

from __future__ import annotations

import argparse
import math

import mpmath as mp
import numpy as np
from scipy.integrate import simpson


def prime_powers_up_to(limit: int) -> list[tuple[int, int, int]]:
    result = []
    for candidate in range(2, limit + 1):
        is_prime = all(
            candidate % divisor
            for divisor in range(2, math.isqrt(candidate) + 1)
        )
        if not is_prime:
            continue
        power = candidate
        exponent = 1
        while power <= limit:
            result.append((power, candidate, exponent))
            power *= candidate
            exponent += 1
    return sorted(result)


def completed_xi_on_line(t: float) -> mp.mpc:
    s = mp.mpf("0.5") + 1j * mp.mpf(t)
    return (
        s
        * (s - 1)
        * mp.power(mp.pi, -s / 2)
        * mp.gamma(s / 2)
        * mp.zeta(s)
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--zero-index", type=int, default=1)
    parser.add_argument("--limits", default="11,25,50,100,250")
    parser.add_argument("--t-max", type=float, default=70.0)
    parser.add_argument("--step", type=float, default=0.025)
    parser.add_argument("--dps", type=int, default=40)
    args = parser.parse_args()

    mp.mp.dps = args.dps
    gamma = float(mp.im(mp.zetazero(args.zero_index)))
    grid = np.arange(0.0, args.t_max + 0.5 * args.step, args.step)
    density = np.empty_like(grid)

    for index, t in enumerate(grid):
        denominator = t * t - gamma * gamma
        if abs(denominator) < 1e-10:
            derivative = mp.diff(
                lambda value: completed_xi_on_line(value), mp.mpf(t)
            )
            quotient = derivative / (2 * t)
        else:
            quotient = completed_xi_on_line(t) / denominator
        density[index] = float(abs(quotient) ** 2)

    norm = 2 * simpson(density, x=grid)

    def autocorrelation(shift: float) -> float:
        return float(
            2 * simpson(density * np.cos(grid * shift), x=grid) / norm
        )

    print(f"zero_index={args.zero_index}")
    print(f"gamma={gamma:.15f}")
    print(f"t_max={args.t_max}")
    print(f"step={args.step}")
    print(f"quotient_norm={norm:.17g}")
    for limit in (int(value) for value in args.limits.split(",")):
        channels = prime_powers_up_to(limit)
        shifts = np.log(
            np.asarray([power for power, _, _ in channels], dtype=float)
        )
        weights = np.asarray(
            [
                1 / (exponent * math.sqrt(power))
                for power, _, exponent in channels
            ],
            dtype=float,
        )
        dimension = len(channels)
        gram = np.empty((dimension, dimension))
        for row in range(dimension):
            for column in range(dimension):
                gram[row, column] = min(shifts[row], shifts[column]) * (
                    autocorrelation(shifts[column] - shifts[row])
                )

        eigenvalues = np.linalg.eigvalsh(gram)
        cost = float(weights @ np.linalg.solve(gram, weights))
        condition = float(eigenvalues[-1] / eigenvalues[0])
        print(
            f"limit={limit} channels={dimension} "
            f"cost={cost:.12f} "
            f"min_eigenvalue={eigenvalues[0]:.6e} "
            f"condition={condition:.6e}"
        )


if __name__ == "__main__":
    main()
