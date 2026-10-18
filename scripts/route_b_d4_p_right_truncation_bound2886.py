"""Bound the truncated right-endpoint Taylor polynomial with exact rationals."""
import json
from fractions import Fraction
from pathlib import Path

COEFFICIENTS = [
    Fraction(223, 6), Fraction(1891, 15), Fraction(-386081, 210),
    Fraction(1921426, 567), Fraction(300116387, 62370),
    Fraction(-33344636267, 2027025), Fraction(-1056735076307, 182432250),
    Fraction(429667469015296, 10854718875),
    Fraction(200384116198016, 15864589125),
    Fraction(-3017679254639919616, 38979295480125),
]
X_MAX = Fraction(1, 10000)  # x = t^2 for |t| <= 1/100
lower = COEFFICIENTS[0] - sum(abs(c) * X_MAX**k
                               for k, c in enumerate(COEFFICIENTS[1:], 1))
payload = {
    "record": 2886,
    "domain": "|t| <= 1/100",
    "bound": "P_truncated / t^2 >= c0 - sum(abs(ck) * 10^(-4k))",
    "lower_bound": str(lower),
    "lower_bound_decimal": float(lower),
    "claims": {
        "exact_rational_truncation_bound": True,
        "order_22_remainder_included": False,
        "full_endpoint_sign_certificate": False,
    },
    "next_target": "add a certified order-22 remainder bound",
}
out = Path("results/2886_route_b_d4_p_right_truncation_bound.json")
out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
print(json.dumps(payload, indent=2))
