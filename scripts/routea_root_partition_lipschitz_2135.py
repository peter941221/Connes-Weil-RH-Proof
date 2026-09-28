#!/usr/bin/env python3
"""Record 2135: tighten the fixed-r48 variation enclosure.

The derivative numerator is isolated over Q by record 2066. On each
isolating interval for a root of phi^(48), evaluate phi^(47) at the exact
rational midpoint and enlarge it by a Lipschitz error obtained from an
interval evaluation of phi^(48) on that same interval. The resulting
variation bound is a much tighter candidate than direct interval evaluation
of phi^(47), whose algebraic dependency is severe.

This is still a certificate candidate: mpmath interval rounding and the
endpoint/monotonicity bridge need an independent Arb or Lean audit before it
can be consumed as a producer theorem.
"""

from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path

import mpmath as mp

ROOT = Path(__file__).resolve().parents[1]
INPUT = ROOT / "results" / "2066_exact_root_isolation.json"
OUTPUT = ROOT / "results" / "2135_routea_root_partition_lipschitz.json"
ORDER = 48
K = mp.mpf(30)
MEASURED_N48 = mp.mpf("2.29343747171e73")


def derivative_terms(order: int) -> dict[tuple[int, int, int], Fraction]:
    terms: dict[tuple[int, int, int], Fraction] = {(0, 0, 0): Fraction(1)}
    for _ in range(order):
        updated: dict[tuple[int, int, int], Fraction] = {}
        for (a, b, power), coefficient in terms.items():
            if a >= 1:
                key = (a - 1, b, power)
                updated[key] = updated.get(key, Fraction(0)) + coefficient * a
            if b >= 1:
                key = (a + 1, b + 1, power)
                updated[key] = updated.get(key, Fraction(0)) + coefficient * 2 * b
            key = (a + 1, b + 2, power + 1)
            updated[key] = updated.get(key, Fraction(0)) - coefficient * 2
        terms = {key: value for key, value in updated.items() if value}
    return terms


def rational_text(value: str) -> mp.mpf:
    numerator, denominator = value.split("/")
    return mp.mpf(numerator) / mp.mpf(denominator)


def derivative_value(
    u: mp.mpf, terms: dict[tuple[int, int, int], Fraction]
) -> mp.mpf:
    s = 1 - u * u
    if abs(u) >= 1 or s <= 0:
        return mp.mpf(0)
    polynomial = mp.mpf(0)
    for (a, b, power), coefficient in terms.items():
        polynomial += (
            mp.mpf(coefficient.numerator) / coefficient.denominator
            * K**power * u**a * s**(-b)
        )
    return mp.exp(-K / s) * polynomial


def interval_value(
    left: mp.mpf,
    right: mp.mpf,
    terms: dict[tuple[int, int, int], Fraction],
):
    u = mp.iv.mpf([left, right])
    s = 1 - u * u
    polynomial = mp.iv.mpf(0)
    for (a, b, power), coefficient in terms.items():
        polynomial += (
            mp.iv.mpf(coefficient.numerator) / coefficient.denominator
            * mp.iv.mpf(K) ** power * u**a * s**(-b)
        )
    return mp.iv.exp(-mp.iv.mpf(K) / s) * polynomial


def interval_abs(value) -> mp.mpf:
    return max(abs(mp.mpf(value.a)), abs(mp.mpf(value.b)))


def main() -> None:
    mp.mp.dps = 100
    mp.iv.dps = 100
    source = json.loads(INPUT.read_text(encoding="utf-8"))
    root_intervals = [
        (rational_text(left), rational_text(right))
        for left, right in source["intervals"]
    ]
    if len(root_intervals) != 64:
        raise RuntimeError(f"expected 64 isolated roots, got {len(root_intervals)}")
    if not all(-1 < left < right < 1 for left, right in root_intervals):
        raise RuntimeError("root interval escaped (-1, 1)")

    terms47 = derivative_terms(ORDER - 1)
    terms48 = derivative_terms(ORDER)
    value_intervals = []
    error_terms = []
    for left, right in root_intervals:
        midpoint = (left + right) / 2
        value = derivative_value(midpoint, terms47)
        derivative_bound = interval_abs(interval_value(left, right, terms48))
        error = derivative_bound * (right - left) / 2
        value_intervals.append((value - error, value + error))
        error_terms.append(error)

    variation_upper = mp.mpf(0)
    previous = (mp.mpf(0), mp.mpf(0))
    for current in value_intervals:
        variation_upper += max(
            abs(current[1] - previous[0]),
            abs(current[0] - previous[1]),
        )
        previous = current
    variation_upper += max(abs(previous[0]), abs(previous[1]))

    result = {
        "record": 2135,
        "status": "ROOT-PARTITION-LIPSCHITZ-CANDIDATE",
        "order": ORDER,
        "root_source": "results/2066_exact_root_isolation.json",
        "root_count": len(root_intervals),
        "max_root_interval_width": mp.nstr(
            max(right - left for left, right in root_intervals), 40
        ),
        "max_lipschitz_error": mp.nstr(max(error_terms), 40),
        "variation_upper": mp.nstr(variation_upper, 40),
        "measured_N48": mp.nstr(MEASURED_N48, 40),
        "upper_over_measured": mp.nstr(variation_upper / MEASURED_N48, 40),
        "improvement_over_2068": mp.nstr(
            mp.mpf("1.2466403887652727e81") / variation_upper, 40
        ),
        "nonclaims": [
            "mpmath interval arithmetic is not an independent formal proof",
            "the endpoint and monotonicity bridge needs an Arb or Lean audit",
            "the owner is the one-copy numerical G8-H candidate",
            "no producer theorem or RH claim",
        ],
        "provenance": {
            "script": "scripts/routea_root_partition_lipschitz_2135.py",
            "prior_skeleton": "results/2068_interval_variation_bound.json",
        },
    }
    OUTPUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
