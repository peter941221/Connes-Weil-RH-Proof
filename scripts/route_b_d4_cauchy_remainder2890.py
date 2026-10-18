"""Assemble the Cauchy geometric remainder from the interval-circle bound."""
import json
import hashlib
from fractions import Fraction
from pathlib import Path

# Conservative rational upper bound for the 256-cell enclosure in record 2889.
M = Fraction(1377903608911726, 10**14)
ratio = Fraction(1, 5)  # r/R = 0.01/0.05
remainder = M * ratio**22 / (1 - ratio)
truncated_lower = Fraction(2828590559115742395042857430835243113655208021407,
                           76131436484619140625000000000000000000000000000)
payload = {
    "record": 2890,
    "generator_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    "formula": "M*(r/R)^22/(1-r/R)",
    "M": str(M),
    "r_over_R": str(ratio),
    "remainder_bound": str(remainder),
    "remainder_bound_decimal": float(remainder),
    "truncated_lower_bound": str(truncated_lower),
    "margin_ratio": float(remainder / truncated_lower),
    "claims": {
        "rational_geometric_assembly": True,
        "complex_circle_interval_source": True,
        "formal_analytic_bridge": False,
        "full_endpoint_sign_certificate": False,
    },
    "next_target": "formalize the Cauchy theorem and connect M to the interval artifact",
}
out = Path("results/2890_route_b_d4_cauchy_remainder.json")
out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
print(json.dumps(payload, indent=2))
