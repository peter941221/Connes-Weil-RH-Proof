#!/usr/bin/env python3
"""Record 2179: independent exact-rational audit of the order-48 tail input.

This is an audit of the mpmath N48 candidate, not a replacement producer
theorem.  It deliberately uses a different engine: Fraction arithmetic and
Horner evaluation of the exact numerator polynomial on the 2066 rational root
intervals.  No termwise absolute expansion is used.  The exponential factor
is safely discarded via exp(-30/(1-u^2)) <= 1, so the result is intentionally
coarse.  The decision is whether this independent coarse N48 remains small
enough for the already enormous 2178 algebraic-tail margin.
"""

from __future__ import annotations

import json
import math
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
INPUT = ROOT / "results" / "2066_exact_root_isolation.json"
OUTPUT = ROOT / "results" / "2179_routea_n48_rational_horner_audit.json"
K = 30
ORDER = 48


def derivative_terms(order: int):
    terms = {(0, 0, 0): Fraction(1)}
    for _ in range(order):
        out = {}
        for (a, b, p), c in terms.items():
            if a >= 1:
                out[(a - 1, b, p)] = out.get((a - 1, b, p), Fraction(0)) + c * a
            if b >= 1:
                out[(a + 1, b + 1, p)] = out.get((a + 1, b + 1, p), Fraction(0)) + c * 2 * b
            out[(a + 1, b + 2, p + 1)] = (
                out.get((a + 1, b + 2, p + 1), Fraction(0)) - c * 2
            )
        terms = {key: value for key, value in out.items() if value}
    return terms


def numerator_coefficients(order: int):
    """Exact coefficients of P_order where phi^(n)=exp(-K/s)P_n/s^(2n)."""
    coeffs = {}
    for (a, b, p), c in derivative_terms(order).items():
        m = 2 * order - b
        for j in range(m + 1):
            degree = a + 2 * j
            term = c * (K**p) * ((-1) ** j) * math.comb(m, j)
            coeffs[degree] = coeffs.get(degree, Fraction(0)) + term
    return {degree: value for degree, value in coeffs.items() if value}


def iv_add(x, y):
    return x[0] + y[0], x[1] + y[1]


def iv_mul(x, y):
    vals = (x[0] * y[0], x[0] * y[1], x[1] * y[0], x[1] * y[1])
    return min(vals), max(vals)


def iv_scale(x, c):
    if c >= 0:
        return x[0] * c, x[1] * c
    return x[1] * c, x[0] * c


def horner_interval(coeffs, left, right):
    degree = max(coeffs)
    value = (Fraction(coeffs.get(degree, 0)), Fraction(coeffs.get(degree, 0)))
    u = (left, right)
    for d in range(degree - 1, -1, -1):
        value = iv_add(iv_mul(value, u), (coeffs.get(d, Fraction(0)),) * 2)
    return value


def horner_point(coeffs, x):
    degree = max(coeffs)
    value = coeffs.get(degree, Fraction(0))
    for d in range(degree - 1, -1, -1):
        value = value * x + coeffs.get(d, Fraction(0))
    return value


def abs_iv(x):
    return max(abs(x[0]), abs(x[1]))


def s_bounds(left, right):
    max_abs = max(abs(left), abs(right))
    min_abs = Fraction(0) if left <= 0 <= right else min(abs(left), abs(right))
    return 1 - max_abs * max_abs, 1 - min_abs * min_abs


def parse_fraction(text: str) -> Fraction:
    n, d = text.split("/")
    return Fraction(int(n), int(d))


def main() -> None:
    source = json.loads(INPUT.read_text(encoding="utf-8"))
    intervals = [
        (parse_fraction(left), parse_fraction(right))
        for left, right in source["intervals"]
    ]
    if len(intervals) != 64 or not all(-1 < l < r < 1 for l, r in intervals):
        raise RuntimeError("root isolation input is not the expected 64 rational intervals")

    coeff47 = numerator_coefficients(ORDER - 1)
    coeff48 = numerator_coefficients(ORDER)
    root_magnitudes = []
    lipschitz_errors = []
    for left, right in intervals:
        s_min, _s_max = s_bounds(left, right)
        if s_min <= 0:
            raise RuntimeError("nonpositive denominator interval")

        midpoint = (left + right) / 2
        p47_mid = abs(horner_point(coeff47, midpoint))
        # exp(-K/s) <= 1: independent exact-rational coarse value bound.
        value_bound = p47_mid / (s_min ** (2 * ORDER - 2))

        p48_iv = horner_interval(coeff48, left, right)
        derivative_bound = abs_iv(p48_iv) / (s_min ** (2 * ORDER))
        error = derivative_bound * (right - left) / 2
        root_magnitudes.append(value_bound)
        lipschitz_errors.append(error)

    # The root values are only enclosed by symmetric magnitude intervals.  A
    # sign-free variation bound is therefore 2*sum |value_i| plus 2*sum errors.
    variation_upper = 2 * sum(root_magnitudes) + 2 * sum(lipschitz_errors)

    # Compare in log10 form to avoid converting giant rationals to float.
    def log10_fraction(value: Fraction) -> float:
        if value == 0:
            return float("-inf")
        return math.log10(abs(value.numerator)) - math.log10(value.denominator)

    log_n = log10_fraction(variation_upper)
    # 2178's two-sided bound scales as N48^4.  Its committed value used
    # N48=2.2934394e73.  Preserve the margin using a log-only stress ratio.
    log_old_n = math.log10(2.2934394233524675e73)
    log_old_tail = math.log10(6.9025590685960082) - 974
    log_new_tail = log_old_tail + 4 * (log_n - log_old_n)
    log_l2 = math.log10(4.412215566637855e10)
    result = {
        "record": 2179,
        "status": "RATIONAL-HORNER-AUDIT",
        "engine": "exact Fraction interval/Horner arithmetic",
        "root_source": "results/2066_exact_root_isolation.json",
        "order": ORDER,
        "root_count": len(intervals),
        "degree_P47": max(coeff47),
        "degree_P48": max(coeff48),
        "variation_upper_log10": log_n,
        "variation_upper_numerator_bits": variation_upper.numerator.bit_length(),
        "variation_upper_denominator_bits": variation_upper.denominator.bit_length(),
        "max_lipschitz_error_log10": max(log10_fraction(x) for x in lipschitz_errors),
        "mpmath_candidate_log10": log_old_n,
        "tail_reprice_log10": log_new_tail,
        "tail_over_l2_log10": log_new_tail - log_l2,
        "checks": {
            "exact_rational_polynomial": True,
            "exact_rational_interval_ops": True,
            "no_mpmath_or_float_interval": True,
            "no_termwise_absolute_expansion": True,
            "exponential_factor_bound": "exp(-30/s) <= 1",
            "sign_free_variation": True,
        },
        "decision": (
            "PASS-MARGIN" if log_new_tail - log_l2 < -20 else "FAIL-MARGIN"
        ),
        "nonclaims": [
            "this is a coarse independent audit, not the final sharp N48 enclosure",
            "root completeness is inherited from the exact rational isolation artifact",
            "the one-copy owner and finite-window signed margin remain open",
            "no producer theorem or RH claim",
        ],
    }
    OUTPUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
