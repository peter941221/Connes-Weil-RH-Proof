#!/usr/bin/env python3
"""Certificate for Proof 274's signed-scalar coefficient ledger.

The script compares the coefficient-weighted square energy from Proof 272 with
the single-coefficient scalar ledger that remains after Proof 273 rejects the
positive H1 route.  It uses the same ordered-future Kolmogorov-Rogozin proxy in
both columns.

The finite cutoff values are diagnostics.  The analytic rank envelope in the
accompanying note proves only that the available scalar majorant is not
summable; it does not prove that the signed source response diverges.
"""

from __future__ import annotations

import argparse
import importlib.util
import math
from pathlib import Path
from types import ModuleType


def load_probe(filename: str, module_name: str) -> ModuleType:
    path = Path(__file__).with_name(filename)
    specification = importlib.util.spec_from_file_location(module_name, path)
    if specification is None or specification.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(specification)
    specification.loader.exec_module(module)
    return module


PROOF_272 = load_probe(
    "272_concentration_stopped_prime_sum_probe.py",
    "proof_272_for_274",
)


def scalar_mode_weight(
    prime: int, maximum_mode: int, polynomial_degree: int
) -> float:
    logarithm = math.log(prime)
    return sum(
        (1.0 + mode * logarithm) ** (2 * polynomial_degree)
        * prime ** (-0.5 * mode)
        for mode in range(1, maximum_mode + 1)
    )


def compare_ledgers(
    primes: list[int],
    root_width: float,
    maximum_mode: int,
    polynomial_degree: int,
) -> dict[str, float]:
    window = max(1.0, 4.0 * root_width)
    prior_large_prime_deficit = 0.0
    raw_scalar = 0.0
    stopped_scalar = 0.0
    stopped_square = 0.0

    for prime in primes:
        concentration_proxy = (
            1.0
            if prior_large_prime_deficit <= 1.0
            else prior_large_prime_deficit**-0.5
        )
        scalar_weight = scalar_mode_weight(
            prime, maximum_mode, polynomial_degree
        )
        square_weight = PROOF_272.mode_energy(
            prime, maximum_mode, polynomial_degree
        )
        raw_scalar += scalar_weight
        stopped_scalar += concentration_proxy * scalar_weight
        stopped_square += concentration_proxy * square_weight

        if math.log(prime) > window:
            coefficient = prime**-0.5
            prior_large_prime_deficit += (
                2.0 * coefficient / (1.0 + coefficient)
            )

    return {
        "raw_scalar": raw_scalar,
        "stopped_scalar": stopped_scalar,
        "stopped_square": stopped_square,
    }


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
    all_primes = PROOF_272.primes_up_to(maximum_prime)
    rows = []
    for cutoff in cutoffs:
        active = [prime for prime in all_primes if prime <= cutoff]
        values = compare_ledgers(
            active,
            root_width,
            maximum_mode,
            polynomial_degree,
        )
        rows.append(
            {
                "cutoff": float(cutoff),
                "prime_count": float(len(active)),
                **values,
            }
        )
    return rows


def rank_majorant(maximum_rank: int, polynomial_degree: int) -> float:
    return sum(
        (1.0 + math.log(rank)) ** (2 * polynomial_degree)
        * rank ** (-0.75)
        for rank in range(2, maximum_rank + 1)
    )


def print_rows(rows: list[dict[str, float]]) -> None:
    print("Signed-scalar versus square-energy concentration ledgers")
    print(
        "+----------+---------+---------------+---------------+---------------+"
    )
    print(
        "| p <=     | count   | raw scalar    | stopped scalar| stopped square|"
    )
    print(
        "+----------+---------+---------------+---------------+---------------+"
    )
    for row in rows:
        print(
            f"| {int(row['cutoff']):>8d} |"
            f" {int(row['prime_count']):>7d} |"
            f" {row['raw_scalar']:>13.6e} |"
            f" {row['stopped_scalar']:>13.6e} |"
            f" {row['stopped_square']:>13.6e} |"
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
    parser.add_argument("--maximum-rank", type=int, default=100_000)
    args = parser.parse_args()

    if args.maximum_prime < 100:
        raise ValueError("maximum prime must be at least 100")
    if args.root_width < 0.0:
        raise ValueError("root width must be nonnegative")
    if args.maximum_mode < 4 or args.polynomial_degree < 0:
        raise ValueError("invalid mode or polynomial degree")
    if args.maximum_rank < 100:
        raise ValueError("maximum rank must be at least 100")

    rows = ledger_rows(
        args.maximum_prime,
        args.root_width,
        args.maximum_mode,
        args.polynomial_degree,
    )
    rank_sum = rank_majorant(args.maximum_rank, args.polynomial_degree)

    print("identity=signed scalar coefficient ownership audit")
    print("status=square ledger separated from signed scalar ledger")
    print_rows(rows)
    print(f"rank-three-quarter majorant={rank_sum:.12e}")
    print("coefficient_weighted_chirp_norm=p^(-m/2)")
    print("positive_square_energy=p^(-m)")
    print("signed_scalar_local_coefficient=p^(-m/2)")
    print("levy_concentration_scalar_majorant=NOT_SUMMABLE_BY_THIS_BOUND")
    print("complete_signed_extra_half_power=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
