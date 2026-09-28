import json
from fractions import Fraction
from pathlib import Path
import sympy as sp
from mpmath import iv

ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "results" / "2068_interval_variation_bound.json"
K = iv.mpf(30)


def derivative_terms(n):
    terms = {(0, 0, 0): Fraction(1)}
    for _ in range(n):
        out = {}
        for (a, b, p), c in terms.items():
            if a >= 1:
                out[(a - 1, b, p)] = out.get((a - 1, b, p), 0) + c * a
            if b >= 1:
                out[(a + 1, b + 1, p)] = out.get((a + 1, b + 1, p), 0) + c * 2 * b
            out[(a + 1, b + 2, p + 1)] = out.get((a + 1, b + 2, p + 1), 0) - 2 * c
        terms = {key: value for key, value in out.items() if value}
    return terms


def numerator_poly(n):
    u = sp.symbols("u")
    s = 1 - u * u
    expr = 0
    for (a, b, p), c in derivative_terms(n).items():
        expr += sp.Rational(c.numerator, c.denominator) * 30**p * u**a * s**(2 * n - b)
    return sp.Poly(sp.expand(expr), u, domain=sp.QQ)


def iv_value(n, left, right):
    u = iv.mpf([str(left.p) + "/" + str(left.q), str(right.p) + "/" + str(right.q)])
    s = 1 - u * u
    value = iv.mpf(0)
    for (a, b, p), c in derivative_terms(n).items():
        coeff = iv.mpf(c.numerator) / c.denominator
        value += coeff * K**p * u**a * s**(-b)
    return iv.exp(-K / s) * value


def endpoint(iv_number):
    return float(iv_number.a), float(iv_number.b)


def main():
    poly = numerator_poly(48)
    intervals = poly.intervals(eps=sp.Rational(1, 10**50))
    roots = [(left, right) for (left, right), multiplicity in intervals if left > -1 and right < 1]
    values = [iv_value(47, left, right) for left, right in roots]
    bounds = [endpoint(value) for value in values]
    lower = 0.0
    upper = 0.0
    previous = (0.0, 0.0)
    for current in bounds:
        lower += 0.0
        upper += max(abs(current[1] - previous[0]), abs(current[0] - previous[1]))
        previous = current
    result = {
        "record": 2068,
        "status": "INTERVAL-VARIATION-SKELETON",
        "order": 48,
        "root_count": len(roots),
        "variation_lower_proxy": 0.0,
        "variation_upper_proxy": upper,
        "measured_N48": 2.29343747171e73,
        "upper_over_measured": upper / 2.29343747171e73,
        "nonclaims": [
            "interval dependency remains in the displayed proxy assembly",
            "endpoint zero terms and monotonicity certification are not yet separately discharged",
            "no producer theorem or RH claim",
        ],
    }
    with OUTPUT.open("w", encoding="utf-8", newline="\n") as handle:
        json.dump(result, handle, indent=2)
        handle.write("\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
