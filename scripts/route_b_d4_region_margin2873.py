"""Measure D4 sign margins before choosing the next enclosure method.

This is a high-precision diagnostic, not a certificate.  It records the
vanishing endpoint behaviour that makes a uniform sign margin impossible on
the outer regions and therefore guides the formal proof toward monotonicity
or endpoint-factor extraction.
"""
import json
from pathlib import Path
import mpmath as mp

mp.mp.dps = 80


def transition(u):
    return 1 / (1 + mp.exp(1 / u - 1 / (1 - u)))


def main():
    regions = [
        (mp.mpf(1) / 4096, mp.mpf(1353) / 10000, "+"),
        (mp.mpf(1354) / 10000, mp.mpf(3028) / 10000, "-"),
        (mp.mpf(3029) / 10000, mp.mpf(1) / 2, "+"),
    ]
    rows = []
    for left, right, expected in regions:
        values = [
            mp.diff(transition, left + (right - left) * i / 1000, 4)
            for i in range(1001)
        ]
        rows.append({
            "left": str(left),
            "right": str(right),
            "expected_sign": expected,
            "q_left": mp.nstr(transition(left), 30),
            "q_right": mp.nstr(transition(right), 30),
            "d4_min": mp.nstr(min(values), 30),
            "d4_max": mp.nstr(max(values), 30),
            "minimum_absolute_sample": mp.nstr(min(abs(x) for x in values), 30),
        })
    payload = {
        "record": 2873,
        "regions": rows,
        "claims": {
            "high_precision_sample_only": True,
            "uniform_sign_certificate": False,
            "integral_bound_certificate": False,
        },
        "decision": "extract endpoint factors or prove monotonicity; do not seek a uniform sign margin",
    }
    out = Path("results/2873_route_b_d4_region_margin.json")
    out.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(payload, indent=2))


if __name__ == "__main__":
    main()
