"""Certificate for Proof 359's harmonic midpoint-row closure criterion.

The script checks the elementary prime-weight envelope and the abstract common
factor consumer.  It does not construct the route's complete factors B_j and
does not prove Gate 3U or RH.
"""

from __future__ import annotations

import argparse
import math

import numpy as np


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


def random_contraction(
    rows: int, columns: int, rng: np.random.Generator
) -> np.ndarray:
    matrix = rng.normal(size=(rows, columns)) + 1j * rng.normal(
        size=(rows, columns)
    )
    norm = np.linalg.norm(matrix, 2)
    return matrix / max(1.0, norm)


def certificate(
    prime_limit: int,
    source_size: int,
    auxiliary_size: int,
    seed: int,
) -> tuple[dict[str, float], list[tuple[int, float, float]]]:
    rng = np.random.default_rng(seed)
    primes = primes_up_to(prime_limit)
    common_input = rng.normal(size=(source_size, auxiliary_size)) + 1j * rng.normal(
        size=(source_size, auxiliary_size)
    )
    common_energy = float(np.linalg.norm(common_input, "fro") ** 2)

    detector_energy = 0.0
    range_energy = 0.0
    pairing = 0.0 + 0.0j
    for prime in primes:
        detector_factor = random_contraction(source_size, source_size, rng)
        detector_row = detector_factor @ common_input
        range_row = rng.normal(size=detector_row.shape) + 1j * rng.normal(
            size=detector_row.shape
        )
        range_row /= max(1.0, np.linalg.norm(range_row, "fro"))
        detector_energy += float(
            np.linalg.norm(detector_row, "fro") ** 2 / (prime - 1.0)
        )
        range_energy += float(
            (prime - 1.0) * np.linalg.norm(range_row, "fro") ** 2
        )
        pairing += np.vdot(detector_row, range_row)

    weight_sum = sum(1.0 / (prime - 1.0) for prime in primes)
    detector_bound = common_energy * weight_sum
    pairing_bound = math.sqrt(detector_energy * range_energy)
    checks = {
        "detector row violation": max(0.0, detector_energy - detector_bound),
        "pairing violation": max(0.0, abs(pairing) - pairing_bound),
    }

    cohorts = []
    for limit in [10, 100, 1000, 10000, prime_limit]:
        cohort = [prime for prime in primes if prime <= limit]
        harmonic_weight = sum(1.0 / (prime - 1.0) for prime in cohort)
        logarithmic_bound = 1.0 + math.log(max(2, limit))
        cohorts.append((limit, harmonic_weight, logarithmic_bound))
        checks["harmonic bound violation"] = max(
            checks.get("harmonic bound violation", 0.0),
            harmonic_weight - logarithmic_bound,
        )

    checks["detector bound utilization"] = (
        detector_energy / detector_bound if detector_bound else 0.0
    )
    return checks, cohorts


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--prime-limit", type=int, default=10000)
    parser.add_argument("--source-size", type=int, default=20)
    parser.add_argument("--auxiliary-size", type=int, default=8)
    parser.add_argument("--seed", type=int, default=359)
    parser.add_argument("--tolerance", type=float, default=3e-10)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    checks, cohorts = certificate(
        args.prime_limit,
        args.source_size,
        args.auxiliary_size,
        args.seed,
    )
    print("Proof 359 harmonic midpoint-row certificate")
    print("limit      reciprocal_weight   elementary_bound")
    for limit, weight, bound in cohorts:
        print(f"{limit:8d}   {weight: .10e}   {bound: .10e}")
    for label, value in checks.items():
        print(f"{label.replace(' ', '_')}={value:.12e}")
    exact_violations = [
        value for label, value in checks.items() if "utilization" not in label
    ]
    maximum_violation = max(exact_violations)
    if maximum_violation > args.tolerance:
        raise RuntimeError(
            f"harmonic row certificate failed: {maximum_violation:.3e}"
        )
    print(f"maximum_bound_violation={maximum_violation:.12e}")
    print("harmonic_weight_envelope=PASS")
    print("common_factor_consumer=PASS")
    print("route_uniform_factorization=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
