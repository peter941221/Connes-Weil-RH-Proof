import json
from pathlib import Path
from fractions import Fraction
import sympy as sp

ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "results" / "2066_exact_root_isolation.json"
K = 30


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
        expr += sp.Rational(c.numerator, c.denominator) * K**p * u**a * s**(2 * n - b)
    return sp.Poly(sp.expand(expr), u, domain=sp.QQ)


def main():
    poly = numerator_poly(48)
    intervals = poly.intervals(eps=sp.Rational(1, 10**40))
    real_intervals = [pair for pair, multiplicity in intervals if pair[0] > -1 and pair[1] < 1]
    result = {
        "record": 2066,
        "status": "EXACT-ROOT-ISOLATION",
        "order": 48,
        "degree": poly.degree(),
        "real_root_intervals_in_minus1_1": len(real_intervals),
        "intervals": [[str(left), str(right)] for left, right in real_intervals],
        "nonclaims": [
            "root isolation only; variation enclosure not assembled",
            "no producer theorem or RH claim",
        ],
    }
    with OUTPUT.open("w", encoding="utf-8", newline="\n") as handle:
        json.dump(result, handle, indent=2)
        handle.write("\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
