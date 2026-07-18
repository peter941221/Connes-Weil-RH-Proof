"""Arithmetic certificate for Proof 348's coherent prime-cluster Gram.

The exact continuous identity is equation (PC.5).  This script evaluates its
finite prime-cluster quadratic form for an indicator root with explicit
autocorrelation.  It is not a finite-section model of Gate 3U.
"""

from __future__ import annotations

import argparse
import math


def primes_up_to(limit: int) -> list[int]:
    if limit < 2:
        return []
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[0:2] = b"\x00\x00"
    for candidate in range(2, math.isqrt(limit) + 1):
        if not sieve[candidate]:
            continue
        start = candidate * candidate
        count = (limit - start) // candidate + 1
        sieve[start : limit + 1 : candidate] = b"\x00" * count
    return [value for value in range(2, limit + 1) if sieve[value]]


def indicator_autocorrelation(displacement: float, half_width: float) -> float:
    return max(0.0, 1.0 - abs(displacement) / (2.0 * half_width))


def cluster_statistics(
    lower: int, epsilon: float, half_width: float, all_primes: list[int]
) -> tuple[int, float, float, float]:
    upper = (1.0 + epsilon) * lower
    cluster = [prime for prime in all_primes if lower <= prime <= upper]
    diagonal_energy = sum(math.log(prime) / prime for prime in cluster)

    gram_energy = 0.0
    for prime in cluster:
        log_prime = math.log(prime)
        prime_weight = prime ** -0.5
        for other in cluster:
            log_other = math.log(other)
            correlation = indicator_autocorrelation(
                log_other - log_prime, half_width
            )
            gram_energy += (
                prime_weight
                * other ** -0.5
                * min(log_prime, log_other)
                * correlation
            )

    if cluster:
        minimum_correlation = indicator_autocorrelation(
            math.log(1.0 + epsilon), half_width
        )
        lower_bound = (
            minimum_correlation
            * math.log(lower)
            * len(cluster)
            * len(cluster)
            / ((1.0 + epsilon) * lower)
        )
    else:
        lower_bound = 0.0

    return len(cluster), diagonal_energy, gram_energy, lower_bound


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--scales", default="100,1000,10000,100000,1000000")
    parser.add_argument("--epsilon", type=float, default=0.1)
    parser.add_argument("--root-half-width", type=float, default=0.5)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    scales = [int(value) for value in args.scales.split(",")]
    prime_limit = math.ceil((1.0 + args.epsilon) * max(scales))
    all_primes = primes_up_to(prime_limit)

    print("Proof 348 coherent prime-cluster Gram certificate")
    print(
        f"epsilon={args.epsilon:.6f}, "
        f"root_half_width={args.root_half_width:.6f}, "
        f"prime_limit={prime_limit}"
    )
    print()
    print(
        "X          primes   diagonal_E    Gram_S2^2    "
        "lower_bound   Gram/E       Gram*log(X)/X"
    )

    for lower in scales:
        count, diagonal, gram, lower_bound = cluster_statistics(
            lower, args.epsilon, args.root_half_width, all_primes
        )
        ratio = gram / diagonal if diagonal else float("nan")
        normalized = gram * math.log(lower) / lower
        print(
            f"{lower:9d}  "
            f"{count:7d}  "
            f"{diagonal: .8e}  "
            f"{gram: .8e}  "
            f"{lower_bound: .8e}  "
            f"{ratio: .8e}  "
            f"{normalized: .8e}"
        )


if __name__ == "__main__":
    main()
