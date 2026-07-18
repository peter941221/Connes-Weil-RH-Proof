#!/usr/bin/env python3
"""Arithmetic certificate for Proof 344's quadratic Euler ledger.

This script verifies only the elementary prime-power sum and its L(1+L)
majorant.  It does not construct the missing root-relative determinant.
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


def quadratic_energy(displacement_cutoff: float) -> tuple[float, int, int]:
    prime_limit = int(math.exp(displacement_cutoff))
    primes = primes_up_to(prime_limit)
    energy = 0.0
    atom_count = 0
    for prime in primes:
        logarithm = math.log(prime)
        max_power = int(displacement_cutoff / logarithm + 1e-14)
        for power in range(1, max_power + 1):
            energy += logarithm * prime ** (-power) / power
            atom_count += 1
    return energy, len(primes), atom_count


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--cutoffs", default="1,2,4,6,8,10,12")
    parser.add_argument("--tolerance", type=float, default=1e-12)
    args = parser.parse_args()

    cutoffs = [float(value) for value in args.cutoffs.split(",")]
    print("identity=near Euler logarithm quadratic ledger")
    print("table=BEGIN")
    maximum_ratio = 0.0
    for cutoff in cutoffs:
        energy, prime_count, atom_count = quadratic_energy(cutoff)
        bound = cutoff * (1.0 + cutoff)
        ratio = energy / bound if bound > 0.0 else 0.0
        maximum_ratio = max(maximum_ratio, ratio)
        print(
            f"L={cutoff:5.1f} primes={prime_count:7d} atoms={atom_count:7d} "
            f"energy={energy:.12e} bound={bound:.12e} ratio={ratio:.6e}"
        )
        if energy > bound + args.tolerance * max(1.0, bound):
            raise RuntimeError(
                f"quadratic ledger exceeded elementary bound at L={cutoff}"
            )
    print("table=END")
    print(f"maximum_energy_to_bound_ratio={maximum_ratio:.12e}")
    print("quadratic_prime_power_ledger=PROVED_ELEMENTARY")
    print("prime_number_theorem_used=FALSE")
    print("root_relative_bogc_owner=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
