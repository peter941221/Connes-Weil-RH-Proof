"""Export the exact polynomial governing dH/dt on the logistic owner path."""
import json
from pathlib import Path
import sympy as s

t, z = s.symbols("t z")
H = (24*t**10*z**3 + 36*t**10*z**2 + 18*t**10*z + 3*t**10
     + 96*t**8*z**3 + 144*t**8*z**2 + 68*t**8*z + 9*t**8
     + 144*t**6*z**3 + 72*t**6*z**2 - 148*t**6*z - 114*t**6
     + 96*t**4*z**3 - 144*t**4*z**2 - 240*t**4*z + 18*t**4
     + 24*t**2*z**3 - 108*t**2*z**2 + 50*t**2*z + 63*t**2 - 4*z + 21)

# From r = t*z and r' = 2(1+t^2)(1-r^2)/(1-t^2)^2.
z_prime = (2*t*(1+t**2)*(1-t**2*z**2)/(1-t**2)**2 - z) / t
derivative = s.factor(s.diff(H, t) + s.diff(H, z) * z_prime)
numerator, denominator = s.fraction(derivative)
P = s.factor(-numerator / 2)

payload = {
    "record": 2879,
    "z_prime": str(s.factor(z_prime)),
    "derivative_identity": "dH/dt = -2*P(t,z)/(t*(1-t^2)^2)",
    "P_degree_t": int(s.degree(P, t)),
    "P_degree_z": int(s.degree(P, z)),
    "P": str(P),
    "claims": {
        "exact_derivative_polynomial": True,
        "outer_monotonicity_certificate": False,
        "sign_certificate": False,
    },
    "next_target": "certify P sign on owner-coherent outer-region boxes",
}
out = Path("results/2879_route_b_d4_h_derivative_polynomial.json")
out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
print(json.dumps(payload, indent=2))
