"""Diagnostic pricing for the proposed D4 sign-partition interface."""
import json
import mpmath as mp
from fractions import Fraction

mp.mp.dps = 60

def transition(u):
    e = mp.exp(-(1 / u - 1 / (1 - u)))
    return e / (1 + e)

def derivative(u, order):
    return mp.diff(transition, u, order)

def main():
    brackets = [(Fraction(1353, 10000), Fraction(1354, 10000)),
                (Fraction(3028, 10000), Fraction(3029, 10000))]
    points = [mp.mpf(1) / 4096, mp.mpf(1353) / 10000,
              mp.mpf(1354) / 10000, mp.mpf(3028) / 10000,
              mp.mpf(3029) / 10000, mp.mpf(1) / 2]
    variations = [abs(derivative(points[i + 1], 3) - derivative(points[i], 3))
                  for i in (0, 2, 4)]
    payload = {
        "record": 2869,
        "zero_brackets": [[str(a), str(b)] for a, b in brackets],
        "d4_at_bracket_endpoints": [
            [str(derivative(mp.mpf(a.numerator) / a.denominator, 4)),
             str(derivative(mp.mpf(b.numerator) / b.denominator, 4))]
            for a, b in brackets],
        "variation_bounds": [str(x) for x in variations],
        "four_times_sum": str(4 * sum(variations)),
        "nonclaims": ["sign proof", "Lean analytic bridge", "SourceRH", "RH"],
    }
    print(json.dumps(payload, indent=2))

if __name__ == "__main__":
    main()
