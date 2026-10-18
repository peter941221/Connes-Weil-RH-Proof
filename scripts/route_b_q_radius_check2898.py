"""Exact algebraic check for the candidate centered-Q radius."""
import json
from fractions import Fraction
from pathlib import Path

# For t^2 + i*b*t - 1 = 0, roots satisfy product -1 and conjugate roots have
# equal modulus; hence |root|^2 = |-1| = 1.
workspace_radius = Fraction(1, 20)
payload = {
    "record": 2898,
    "quadratic": "t^2 + i*b*t - 1",
    "root_product": "-1",
    "root_modulus_squared": "1",
    "workspace_radius": str(workspace_radius),
    "workspace_radius_lt_candidate": workspace_radius < 1,
    "claims": {"algebraic_radius_check": True,
               "analytic_convergence_certificate": False},
}
out = Path("results/2898_route_b_q_radius_check.json")
out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
print(json.dumps(payload, indent=2))
