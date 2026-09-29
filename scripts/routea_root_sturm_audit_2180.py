#!/usr/bin/env python3
"""Record 2180: exact rational Sturm audit of the order-48 root partition.

The 2066 intervals came from SymPy's exact isolation.  This independent audit
reconstructs the same rational numerator P_48 and uses a Fraction Sturm chain
to count roots in (-1,1), in every listed interval, and in every gap.  It
settles the root-completeness premise used by records 2135 and 2179 without
floating-point sign tests.
"""

from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
INPUT = ROOT / "results" / "2066_exact_root_isolation.json"
OUTPUT = ROOT / "results" / "2180_routea_root_sturm_audit.json"
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
    coeffs = {}
    for (a, b, p), c in derivative_terms(order).items():
        m = 2 * order - b
        for j in range(m + 1):
            degree = a + 2 * j
            term = c * (K**p) * ((-1) ** j)
            term *= Fraction(__import__("math").comb(m, j))
            coeffs[degree] = coeffs.get(degree, Fraction(0)) + term
    while coeffs and coeffs[max(coeffs)] == 0:
        del coeffs[max(coeffs)]
    degree = max(coeffs)
    return [coeffs.get(i, Fraction(0)) for i in range(degree + 1)]


def trim(poly):
    poly = list(poly)
    while len(poly) > 1 and poly[-1] == 0:
        poly.pop()
    return poly


def poly_derivative(poly):
    return trim([poly[i] * i for i in range(1, len(poly))]) or [Fraction(0)]


def poly_remainder(f, g):
    f = trim(f)
    g = trim(g)
    if len(g) == 1 and g[0] == 0:
        raise ZeroDivisionError("zero polynomial divisor")
    if len(f) < len(g):
        return f
    rem = f[:]
    inv = 1 / g[-1]
    while len(rem) >= len(g) and not (len(rem) == 1 and rem[0] == 0):
        shift = len(rem) - len(g)
        factor = rem[-1] * inv
        for j, coefficient in enumerate(g):
            rem[shift + j] -= factor * coefficient
        rem = trim(rem)
    return rem


def sturm_chain(poly):
    chain = [trim(poly), poly_derivative(poly)]
    while len(chain[-1]) > 1 or chain[-1][0] != 0:
        rem = poly_remainder(chain[-2], chain[-1])
        rem = trim([-x for x in rem])
        if len(rem) == 1 and rem[0] == 0:
            break
        chain.append(rem)
    return chain


def eval_poly(poly, x):
    value = poly[-1]
    for coefficient in reversed(poly[:-1]):
        value = value * x + coefficient
    return value


def variations(chain, x):
    signs = []
    for poly in chain:
        value = eval_poly(poly, x)
        if value > 0:
            signs.append(1)
        elif value < 0:
            signs.append(-1)
    return sum(a != b for a, b in zip(signs, signs[1:]))


def parse_fraction(text: str) -> Fraction:
    n, d = text.split("/")
    return Fraction(int(n), int(d))


def root_count(chain, left, right):
    return variations(chain, left) - variations(chain, right)


def main() -> None:
    source = json.loads(INPUT.read_text(encoding="utf-8"))
    intervals = [
        (parse_fraction(left), parse_fraction(right))
        for left, right in source["intervals"]
    ]
    if len(intervals) != 64:
        raise RuntimeError("expected 64 input intervals")
    polynomial = numerator_coefficients(ORDER)
    chain = sturm_chain(polynomial)
    total = root_count(chain, Fraction(-1), Fraction(1))
    interval_counts = [root_count(chain, left, right) for left, right in intervals]
    gap_counts = []
    gap_edges = [(-1, intervals[0][0])]
    gap_edges.extend((intervals[i][1], intervals[i + 1][0]) for i in range(len(intervals) - 1))
    gap_edges.append((intervals[-1][1], 1))
    for left, right in gap_edges:
        gap_counts.append(root_count(chain, Fraction(left), Fraction(right)))

    result = {
        "record": 2180,
        "status": "STURM-ROOT-COMPLETENESS-PASS" if (
            total == 64 and all(x == 1 for x in interval_counts)
            and all(x == 0 for x in gap_counts)
        ) else "STURM-ROOT-COMPLETENESS-FAIL",
        "engine": "exact Fraction Sturm chain",
        "polynomial_degree": len(polynomial) - 1,
        "sturm_chain_length": len(chain),
        "roots_in_minus1_1": total,
        "input_interval_count": len(intervals),
        "interval_counts": interval_counts,
        "gap_counts": gap_counts,
        "checks": {
            "exact_rational_coefficients": True,
            "exact_rational_endpoint_signs": True,
            "no_float_or_mpmath": True,
            "all_intervals_single_root": all(x == 1 for x in interval_counts),
            "all_gaps_empty": all(x == 0 for x in gap_counts),
        },
        "nonclaims": [
            "this audits root completeness only; it does not sharpen the N48 value bound",
            "the owner remains the one-copy numerical G8-H candidate",
            "finite-window signed C3' margin and producer theorem remain open",
            "no RH claim",
        ],
        "provenance": {
            "input": "results/2066_exact_root_isolation.json",
            "numerator_recursion": "scripts/routea_n48_rational_horner_audit_2179.py",
        },
    }
    OUTPUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
