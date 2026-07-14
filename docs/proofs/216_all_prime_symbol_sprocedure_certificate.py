#!/usr/bin/env python3
"""Arb no-go certificate for the constant PNT-main S-procedure.

At cutoff ``c = 10^6``, two rational frequencies force incompatible bounds
on every constant multiplier in

    k_c(t) <= 2 + (t^2 + 1/4) / 50 + lambda k_0(t).

The certificate evaluates the finite prime-power symbol and the elementary
continuous-main symbol directly with Arb balls.  It assumes no zero-location
statement.
"""

from __future__ import annotations

import argparse
import math

from flint import arb, ctx, fmpq


CUTOFF = 1_000_000
LOWER_FREQUENCY = fmpq(2769, 200)  # 13.845
UPPER_FREQUENCY = fmpq(289, 20)  # 14.45
LOWER_MULTIPLIER = fmpq(51, 50)  # 1.02


def primes_up_to(limit: int) -> list[int]:
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[:2] = b"\x00\x00"
    for prime in range(2, math.isqrt(limit) + 1):
        if sieve[prime]:
            start = prime * prime
            sieve[start : limit + 1 : prime] = b"\x00" * (
                (limit - start) // prime + 1
            )
    return [value for value in range(2, limit + 1) if sieve[value]]


def prime_power_symbol(
    frequency: arb, primes: list[int]
) -> tuple[arb, int]:
    value = arb(0)
    term_count = 0
    for prime in primes:
        log_prime = arb(prime).log()
        prime_power = prime
        exponent = 1
        while prime_power < CUTOFF:
            shift = exponent * log_prime
            weight = log_prime / arb(prime_power).sqrt()
            value += 2 * weight * (frequency * shift).cos()
            prime_power *= prime
            exponent += 1
            term_count += 1
    return value, term_count


def continuous_main_symbol(frequency: arb) -> arb:
    interval_length = arb(CUTOFF).log()
    denominator = frequency**2 + arb(1) / 4
    endpoint_phase = interval_length * frequency
    return 2 * (
        arb(CUTOFF).sqrt()
        * (
            endpoint_phase.cos() / 2
            + frequency * endpoint_phase.sin()
        )
        - arb(1) / 2
    ) / denominator


def scalar_budget(frequency: arb) -> arb:
    return 2 + (frequency**2 + arb(1) / 4) / 50


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--bits", type=int, default=128)
    args = parser.parse_args()
    ctx.prec = args.bits

    primes = primes_up_to(CUTOFF)
    lower_frequency = arb(LOWER_FREQUENCY)
    upper_frequency = arb(UPPER_FREQUENCY)

    lower_prime, lower_count = prime_power_symbol(lower_frequency, primes)
    upper_prime, upper_count = prime_power_symbol(upper_frequency, primes)
    if lower_count != upper_count:
        raise AssertionError("prime-power enumeration changed between points")

    lower_main = continuous_main_symbol(lower_frequency)
    upper_main = continuous_main_symbol(upper_frequency)
    lower_margin = (
        lower_prime
        - scalar_budget(lower_frequency)
        - arb(LOWER_MULTIPLIER) * lower_main
    )
    upper_margin = (
        upper_prime - scalar_budget(upper_frequency) - upper_main
    )

    if not lower_main > 0:
        raise AssertionError(f"expected positive lower main symbol: {lower_main}")
    if not lower_margin > 0:
        raise AssertionError(
            "lower point did not force lambda > 1.02: "
            f"margin={lower_margin}"
        )
    if not upper_main < 0:
        raise AssertionError(f"expected negative upper main symbol: {upper_main}")
    if not upper_margin > 0:
        raise AssertionError(
            "upper point did not force lambda < 1: "
            f"margin={upper_margin}"
        )

    print(f"bits={args.bits}")
    print(f"cutoff={CUTOFF}")
    print(f"prime_count={len(primes)}")
    print(f"prime_power_terms={lower_count}")
    print(f"lower_frequency={lower_frequency}")
    print(f"lower_main_symbol={lower_main}")
    print(f"lower_margin_at_lambda_1.02={lower_margin}")
    print(f"upper_frequency={upper_frequency}")
    print(f"upper_main_symbol={upper_main}")
    print(f"upper_margin_at_lambda_1={upper_margin}")
    print("certificate=lambda > 1.02 and lambda < 1; no constant lambda exists")


if __name__ == "__main__":
    main()
