"""Exact radius screen for excluding zeros of the composed cosh denominator."""
import json
from fractions import Fraction
from pathlib import Path

radius = Fraction(1, 20)
argument_bound = 2 * radius / (1 - radius * radius)
payload = {
    "record": 2900,
    "radius": str(radius),
    "argument_bound": str(argument_bound),
    "argument_bound_decimal": float(argument_bound),
    "cosh_zero_modulus_lower_bound": "pi/2",
    "elementary_pi_lower_bound": "3/2",
    "strict_separation_check": argument_bound < Fraction(3, 2),
    "claims": {"elementary_zero_exclusion_screen": True,
               "complex_norm_lean_proof": False,
               "holomorphic_extension_certificate": False},
    "next_target": "formalize complex norm inequality and cosh zero classification in Lean",
}
out = Path("results/2900_route_b_cosh_zero_exclusion.json")
out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
print(json.dumps(payload, indent=2))
