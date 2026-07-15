#!/usr/bin/env python3
"""Certificate for Proof 272's concentration-function prime ledger.

The script checks the coefficient and probability identities behind the
ordered future Euler cloud.  It does not pull that classical law through the
intervening Proof 271 renewal contraction.
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
        if sieve[candidate]:
            start = candidate * candidate
            count = (limit - start) // candidate + 1
            sieve[start : limit + 1 : candidate] = b"\x00" * count
    return [value for value in range(2, limit + 1) if sieve[value]]


def difference_zero_atom(coefficient: float) -> float:
    return (1.0 - coefficient) / (1.0 + coefficient)


def truncated_difference_zero_atom(
    coefficient: float, maximum_mode: int
) -> float:
    return sum(
        ((1.0 - coefficient) * coefficient**mode) ** 2
        for mode in range(maximum_mode + 1)
    )


def local_atom_certificate(maximum_mode: int) -> dict[str, float]:
    maximum_atom_error = 0.0
    maximum_deficit_error = 0.0
    for prime in (2, 3, 5, 11, 101, 1009):
        coefficient = prime**-0.5
        exact_atom = difference_zero_atom(coefficient)
        truncated_atom = truncated_difference_zero_atom(
            coefficient, maximum_mode
        )
        maximum_atom_error = max(
            maximum_atom_error, abs(exact_atom - truncated_atom)
        )
        exact_deficit = 1.0 - exact_atom
        formula_deficit = 2.0 * coefficient / (1.0 + coefficient)
        maximum_deficit_error = max(
            maximum_deficit_error,
            abs(exact_deficit - formula_deficit),
        )
        if formula_deficit + 1e-15 < coefficient:
            raise AssertionError("one-prime concentration deficit is too small")
    return {
        "difference zero-atom truncation error": maximum_atom_error,
        "concentration deficit formula error": maximum_deficit_error,
    }


def mode_energy(
    prime: int, maximum_mode: int, polynomial_degree: int
) -> float:
    logarithm = math.log(prime)
    return sum(
        (1.0 + mode * logarithm) ** (2 * polynomial_degree)
        * prime ** (-mode)
        for mode in range(1, maximum_mode + 1)
    )


def mode_reduction_certificate(
    primes: list[int], maximum_mode: int, polynomial_degree: int
) -> dict[str, float]:
    maximum_ratio = 0.0
    degree_moment = sum(
        mode ** (2 * polynomial_degree) * 2.0 ** (1 - mode)
        for mode in range(1, maximum_mode + 1)
    )
    maximum_excess = 0.0
    for prime in primes:
        energy = mode_energy(prime, maximum_mode, polynomial_degree)
        profile = (
            (1.0 + math.log(prime)) ** (2 * polynomial_degree) / prime
        )
        ratio = energy / profile
        maximum_ratio = max(maximum_ratio, ratio)
        maximum_excess = max(maximum_excess, ratio - degree_moment)
    return {
        "maximum mode-reduction ratio": maximum_ratio,
        "mode-reduction bound excess": maximum_excess,
    }


def stopped_ledger(
    primes: list[int],
    root_width: float,
    maximum_mode: int,
    polynomial_degree: int,
) -> tuple[float, float, float]:
    window = max(1.0, 4.0 * root_width)
    raw = 0.0
    stopped = 0.0
    largest_concentration_proxy = 0.0
    prior_large_prime_deficit = 0.0
    for prime in primes:
        energy = mode_energy(prime, maximum_mode, polynomial_degree)
        raw += energy
        concentration_proxy = (
            1.0
            if prior_large_prime_deficit <= 1.0
            else prior_large_prime_deficit**-0.5
        )
        stopped += energy * concentration_proxy
        largest_concentration_proxy = max(
            largest_concentration_proxy, concentration_proxy
        )
        if math.log(prime) > window:
            coefficient = prime**-0.5
            prior_large_prime_deficit += (
                2.0 * coefficient / (1.0 + coefficient)
            )
    return raw, stopped, largest_concentration_proxy


def ledger_rows(
    maximum_prime: int,
    root_width: float,
    maximum_mode: int,
    polynomial_degree: int,
) -> list[dict[str, float]]:
    cutoffs = [
        cutoff
        for cutoff in (100, 1_000, 10_000, 100_000, 1_000_000)
        if cutoff <= maximum_prime
    ]
    if not cutoffs or cutoffs[-1] != maximum_prime:
        cutoffs.append(maximum_prime)
    all_primes = primes_up_to(maximum_prime)
    rows = []
    for cutoff in cutoffs:
        active = [prime for prime in all_primes if prime <= cutoff]
        raw, stopped, largest_proxy = stopped_ledger(
            active,
            root_width,
            maximum_mode,
            polynomial_degree,
        )
        rows.append(
            {
                "cutoff": float(cutoff),
                "prime_count": float(len(active)),
                "raw": raw,
                "stopped": stopped,
                "largest_proxy": largest_proxy,
            }
        )
    return rows


def print_checks(title: str, checks: dict[str, float]) -> None:
    print(title)
    print("+--------------------------------------------+---------------+")
    print("| check                                      | value         |")
    print("+--------------------------------------------+---------------+")
    for label, value in checks.items():
        print(f"| {label:<42} | {value:>13.6e} |")
    print("+--------------------------------------------+---------------+")


def print_ledgers(rows: list[dict[str, float]]) -> None:
    print("Ordered-future concentration ledger")
    print(
        "+----------+---------+---------------+---------------+---------------+"
    )
    print(
        "| p <=     | count   | raw p^-m     | stopped proxy | max Q proxy   |"
    )
    print(
        "+----------+---------+---------------+---------------+---------------+"
    )
    for row in rows:
        print(
            f"| {int(row['cutoff']):>8d} |"
            f" {int(row['prime_count']):>7d} |"
            f" {row['raw']:>13.6e} |"
            f" {row['stopped']:>13.6e} |"
            f" {row['largest_proxy']:>13.6e} |"
        )
    print(
        "+----------+---------+---------------+---------------+---------------+"
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--maximum-prime", type=int, default=100_000)
    parser.add_argument("--root-width", type=float, default=1.0)
    parser.add_argument("--maximum-mode", type=int, default=24)
    parser.add_argument("--polynomial-degree", type=int, default=1)
    parser.add_argument("--atom-maximum-mode", type=int, default=80)
    parser.add_argument("--tolerance", type=float, default=1e-12)
    args = parser.parse_args()

    if args.maximum_prime < 100:
        raise ValueError("maximum prime must be at least 100")
    if args.root_width < 0.0:
        raise ValueError("root width must be nonnegative")
    if args.maximum_mode < 4 or args.atom_maximum_mode < 16:
        raise ValueError("mode truncation is too small")
    if args.polynomial_degree < 0:
        raise ValueError("polynomial degree must be nonnegative")

    primes = primes_up_to(args.maximum_prime)
    atom_checks = local_atom_certificate(args.atom_maximum_mode)
    reduction_checks = mode_reduction_certificate(
        primes, args.maximum_mode, args.polynomial_degree
    )
    rows = ledger_rows(
        args.maximum_prime,
        args.root_width,
        args.maximum_mode,
        args.polynomial_degree,
    )

    print("identity=concentration-stopped corrected prime ledger")
    print("status=positive square-energy sum closed; signed scalar gain open")
    print_checks("Difference-geometric concentration", atom_checks)
    print()
    print_checks("Prime-mode reduction", reduction_checks)
    print()
    print_ledgers(rows)

    maximum_exact_error = max(
        atom_checks["difference zero-atom truncation error"],
        atom_checks["concentration deficit formula error"],
        reduction_checks["mode-reduction bound excess"],
    )
    print(f"maximum exact-certificate error={maximum_exact_error:.12e}")
    if maximum_exact_error > args.tolerance:
        raise SystemExit(
            f"exact certificate failed: {maximum_exact_error:.6e}"
        )

    print("coefficient_weighted_chirp_square=HARMONIC_WITHOUT_STOPPING")
    print("positive_square_energy_concentration_sum=UNIFORMLY_BOUNDED")
    print("positive_h1_source_lift=REJECTED_BY_PROOF_273")
    print("signed_scalar_local_coefficient=p^(-m/2)")
    print("complete_signed_extra_half_power=OPEN")
    print("signed_paired_source_disintegration=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
