"""Export exact centered power-series coefficients for Q(t)."""
import json
from pathlib import Path
import sympy as s

t = s.symbols("t")
q = (1 + s.tanh(2 * t / (1 - t**2))) / 2
series = s.Poly(s.series(q, t, 0, 22).removeO(), t)
payload = {
    "record": 2896,
    "definition": "Q(t) = (1 + tanh(2*t/(1-t^2)))/2",
    "order": 21,
    "coefficients": {str(k[0]): str(v) for k, v in series.terms()},
    "constant_term": "1/2",
    "claims": {"exact_rational_series": True,
               "convergence_radius_certificate": False,
               "analytic_extension_certificate": False},
    "next_target": "prove the series identity and radius bound in Lean",
}
out = Path("results/2896_route_b_q_center_series.json")
out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
print(json.dumps(payload, indent=2))
