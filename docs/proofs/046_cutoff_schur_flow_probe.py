#!/usr/bin/env python3
"""Probe the cutoff-free finite Weil Schur impedance.

This is a rejection tool, not a positivity certificate.  It independently
mirrors the closed forms used by arXiv:2607.02828 and evaluates

    s_N(u) = 1 / <1, Q_N(u)^(-1) 1>,   u = log(c),

away from prime-power events.  The scalar is the Schur complement in the
universal all-ones direction and preserves the coupled pole/Gamma/prime
cancellation which blockwise estimates destroy.
"""

from __future__ import annotations

import argparse
import json
import math

import mpmath as mp


def prime_powers_up_to(x: mp.mpf) -> list[tuple[int, int]]:
    limit = int(mp.floor(x))
    primes: list[int] = []
    for candidate in range(2, limit + 1):
        if all(candidate % prime for prime in primes if prime * prime <= candidate):
            primes.append(candidate)
    result: list[tuple[int, int]] = []
    for prime in primes:
        power = prime
        while power <= limit:
            result.append((power, prime))
            power *= prime
    return result


def geometric_sums(index: int, cutoff: mp.mpf) -> tuple[mp.mpf, ...]:
    frequency = 2 * mp.pi * index / cutoff
    sum_s = mp.mpf(0)
    sum_cc = mp.mpf(0)
    sum_xc1 = mp.mpf(0)
    sum_xc2 = mp.mpf(0)
    threshold = mp.power(10, -(mp.mp.dps - 12))
    for k in range(100_000):
        coefficient = 2 * k + mp.mpf("0.5")
        exponential = mp.exp(-coefficient * cutoff)
        denominator = coefficient * coefficient + frequency * frequency
        sum_s += exponential / denominator
        if index:
            sum_cc += (
                exponential
                * frequency
                * frequency
                / (coefficient * denominator)
            )
        sum_xc1 += exponential * coefficient / denominator
        sum_xc2 += (
            exponential
            * (coefficient * coefficient - frequency * frequency)
            / (denominator * denominator)
        )
        if exponential < threshold and k > 2:
            break
    else:
        raise RuntimeError("geometric sum did not converge")
    return sum_s, sum_cc, sum_xc1, sum_xc2


def closed_forms(
    level: int, cutoff: mp.mpf
) -> tuple[list[mp.mpf], list[mp.mpf], list[mp.mpf]]:
    quarter = mp.mpf("0.25")
    psi_quarter = mp.digamma(quarter)
    source_s: list[mp.mpf] = []
    source_cc: list[mp.mpf] = []
    source_xc: list[mp.mpf] = []
    for index in range(level + 1):
        frequency = 2 * mp.pi * index / cutoff
        argument = quarter + 1j * mp.pi * index / cutoff
        sum_s, sum_cc, sum_xc1, sum_xc2 = geometric_sums(index, cutoff)
        if index == 0:
            source_s.append(mp.mpf(0))
            source_cc.append(mp.mpf(0))
        else:
            source_s.append(mp.im(mp.digamma(argument)) / 2 - frequency * sum_s)
            source_cc.append(
                -(mp.re(mp.digamma(argument)) - psi_quarter) / 2 + sum_cc
            )
        source_xc.append(
            mp.re(mp.polygamma(1, argument)) / 4
            - cutoff * sum_xc1
            - sum_xc2
        )
    return source_s, source_cc, source_xc


def cutoff_free_matrix(level: int, cutoff: mp.mpf) -> mp.matrix:
    source_s, source_cc, source_xc = closed_forms(level, cutoff)
    dimension = 2 * level + 1
    result = mp.matrix(dimension)
    sixteen_pi_squared = 16 * mp.pi * mp.pi
    pole_prefactor = 32 * cutoff * mp.sinh(cutoff / 4) ** 2
    exponential = mp.exp(cutoff)
    kappa = mp.log(4 * mp.pi * (exponential - 1) / (exponential + 1)) + mp.euler
    upper = mp.exp(cutoff / 2)
    source_j = (
        -2 * mp.log(upper + 1)
        + mp.log(upper * upper + 1)
        + 2 * mp.atan(upper)
        + mp.log(2)
        - mp.pi / 2
    )
    prime_data = prime_powers_up_to(exponential)

    def signed_s(index: int) -> mp.mpf:
        return source_s[index] if index >= 0 else -source_s[-index]

    for row, n in enumerate(range(-level, level + 1)):
        for column, m in enumerate(range(-level, level + 1)):
            pole = pole_prefactor * (
                cutoff * cutoff - sixteen_pi_squared * m * n
            ) / (
                (cutoff * cutoff + sixteen_pi_squared * m * m)
                * (cutoff * cutoff + sixteen_pi_squared * n * n)
            )
            if n == m:
                archimedean = (
                    kappa
                    + 2 * source_cc[abs(n)]
                    + source_j
                    - 2 * source_xc[abs(n)] / cutoff
                )
            else:
                archimedean = (signed_s(m) - signed_s(n)) / (mp.pi * (n - m))
            finite_prime = mp.mpf(0)
            for power, prime in prime_data:
                position = mp.log(power)
                weight = mp.log(prime) / mp.sqrt(power)
                if n == m:
                    kernel = 2 * (1 - position / cutoff) * mp.cos(
                        2 * mp.pi * n * position / cutoff
                    )
                else:
                    kernel = (
                        mp.sin(2 * mp.pi * m * position / cutoff)
                        - mp.sin(2 * mp.pi * n * position / cutoff)
                    ) / (mp.pi * (n - m))
                finite_prime += weight * kernel
            result[row, column] = pole - archimedean - finite_prime
    return result


def schur_impedance(level: int, cutoff: mp.mpf) -> mp.mpf:
    matrix = cutoff_free_matrix(level, cutoff)
    ones = mp.matrix([1] * matrix.rows)
    solution = mp.lu_solve(matrix, ones)
    denominator = (ones.T * solution)[0]
    return 1 / denominator


def probe(level: int, cutoff: mp.mpf, step: mp.mpf) -> dict[str, str | int]:
    minus = schur_impedance(level, cutoff - step)
    center = schur_impedance(level, cutoff)
    plus = schur_impedance(level, cutoff + step)
    first = (plus - minus) / (2 * step)
    second = (plus - 2 * center + minus) / (step * step)
    return {
        "N": level,
        "u": mp.nstr(cutoff, 20),
        "s": mp.nstr(center, 30),
        "s_prime": mp.nstr(first, 30),
        "s_second": mp.nstr(second, 30),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--levels", default="1,2,3,4")
    parser.add_argument("--cutoffs", default="1.2,1.5,1.8,2.0,2.3,2.5,2.8,3.1")
    parser.add_argument("--step", default="1e-5")
    parser.add_argument("--digits", type=int, default=80)
    args = parser.parse_args()

    mp.mp.dps = args.digits
    levels = [int(value) for value in args.levels.split(",")]
    cutoffs = [mp.mpf(value) for value in args.cutoffs.split(",")]
    step = mp.mpf(args.step)
    results = [
        probe(level, cutoff, step)
        for level in levels
        for cutoff in cutoffs
    ]
    print(json.dumps(results, indent=2))


if __name__ == "__main__":
    main()
