"""Export the exact centred factorisation of the Route B D4 numerator."""
import json
from pathlib import Path
import sympy as s

t, z, u, q = s.symbols("t z u q")
phi = 1 / u - 1 / (1 - u)
velocity = -s.diff(phi, u) * q * (1 - q)
jet = q
for _ in range(4):
    jet = s.factor(s.diff(jet, u) + s.diff(jet, q) * velocity)
num, _ = s.fraction(jet)
centred = s.factor(num.subs({u: (1 + t) / 2, q: (1 + t * z) / 2}))
factor_t = s.factor(centred / t)

payload = {
    "record": 2874,
    "coordinate_change": {
        "t": "2*u - 1",
        "r": "2*q - 1",
        "z": "r/t",
        "logistic_identity": "z = tanh(2*t/(1-t^2))/t",
    },
    "exact_factorisation": str(centred),
    "factor_t_removed": str(factor_t),
    "remaining_variables": ["t^2", "z"],
    "claims": {
        "exact_symbolic_factorisation": True,
        "sign_certificate": False,
        "integral_bound_certificate": False,
    },
    "next_target": "certify the sign of factor_t_removed on the owner-coherent z interval",
}
out = Path("results/2874_route_b_d4_centered_factor.json")
out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
print(json.dumps(payload, indent=2))
