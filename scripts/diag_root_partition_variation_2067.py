import json
from fractions import Fraction
from pathlib import Path
import sympy as sp
from mpmath import mp

ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "results" / "2067_root_partition_variation.json"
K = mp.mpf(30)


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


def derivative_value(n, u):
    s = 1 - u * u
    if abs(u) >= 1 or s <= 0:
        return mp.mpf(0)
    value = sum(mp.mpf(c.numerator) / c.denominator * K**p * u**a * s**(-b)
                for (a, b, p), c in derivative_terms(n).items())
    return mp.exp(-K / s) * value


def main():
    mp.dps = 100
    poly = numerator_poly(48)
    intervals = poly.intervals(eps=sp.Rational(1, 10**60))
    roots = []
    widths = []
    for (left, right), multiplicity in intervals:
        if left > -1 and right < 1:
            left_mp = mp.mpf(str(left.p)) / mp.mpf(str(left.q))
            right_mp = mp.mpf(str(right.p)) / mp.mpf(str(right.q))
            roots.append((left_mp + right_mp) / 2)
            widths.append(right_mp - left_mp)
    points = [mp.mpf(-1)] + roots + [mp.mpf(1)]
    values = [derivative_value(47, point) for point in points]
    variation = sum(abs(values[i + 1] - values[i]) for i in range(len(values) - 1))
    measured = mp.mpf('2.29343747171e73')
    result = {
        "record": 2067,
        "status": "ROOT-PARTITION-MEASURED-REPRODUCTION",
        "order": 48,
        "root_count": len(roots),
        "max_root_interval_width": str(max(widths)),
        "variation_midpoint": str(variation),
        "measured_N48": str(measured),
        "ratio_to_measured": str(variation / measured),
        "nonclaims": [
            "midpoints are used inside exact root intervals; endpoint interval propagation is still required",
            "this is not yet a certified total-variation enclosure",
            "no producer theorem or RH claim",
        ],
    }
    with OUTPUT.open('w', encoding='utf-8', newline='\n') as handle:
        json.dump(result, handle, indent=2)
        handle.write('\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
