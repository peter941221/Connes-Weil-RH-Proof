import json
import math
from pathlib import Path
import numpy as np
from mpmath import mp

ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "results" / "2065_root_partition_variation.json"
K = mp.mpf(30)


def derivative_terms(n):
    terms = {(0, 0, 0): mp.mpf(1)}
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


def poly_add_term(poly, term, n):
    a, b, p, coeff = term
    power = 2 * n - b
    base = np.array([1.0])
    factor = np.array([1.0, 0.0, -1.0])
    for _ in range(power):
        base = np.convolve(base, factor)
    shifted = np.pad(base * float(coeff * K ** p), (a, 0))
    if len(poly) < len(shifted):
        poly.extend([0.0] * (len(shifted) - len(poly)))
    for i, value in enumerate(shifted):
        poly[i] += value


def numerator_poly(n):
    poly = []
    for (a, b, p), coeff in derivative_terms(n).items():
        poly_add_term(poly, (a, b, p, coeff), n)
    return np.asarray(poly)


def derivative_value(n, u):
    s = 1 - u * u
    if abs(u) >= 1 or s <= 0:
        return mp.mpf(0)
    value = sum(c * K ** p * u ** a * s ** (-b) for (a, b, p), c in derivative_terms(n).items())
    return mp.e ** (-K / s) * value


def main():
    n = 48
    poly = numerator_poly(n)
    roots = np.roots(poly[::-1])
    real_roots = sorted(float(root.real) for root in roots if abs(root.imag) < 1e-8 and -1 < root.real < 1)
    points = [-1.0] + real_roots + [1.0]
    values = [derivative_value(n - 1, mp.mpf(str(point))) for point in points]
    variation = sum(abs(values[i + 1] - values[i]) for i in range(len(values) - 1))
    result = {
        "record": 2065,
        "status": "ROOT-PARTITION-DIAGNOSTIC",
        "order": n,
        "critical_derivative_order": n,
        "root_count": len(real_roots),
        "variation_root_partition": float(variation),
        "measured_N48": 2.29343747171e73,
        "ratio_to_measured": float(variation) / 2.29343747171e73,
        "root_imag_max": float(max((abs(root.imag) for root in roots if abs(root.imag) < 1e-8), default=0.0)),
        "nonclaims": [
            "numpy roots are not validated intervals",
            "this is a diagnostic for the sign-partition mechanism",
            "no producer theorem or RH claim",
        ],
    }
    with OUTPUT.open("w", encoding="utf-8", newline="\n") as handle:
        json.dump(result, handle, indent=2)
        handle.write("\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
