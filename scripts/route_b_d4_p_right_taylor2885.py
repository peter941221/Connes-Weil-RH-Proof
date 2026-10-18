"""Export the exact even Taylor polynomial for P on the right owner endpoint."""
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
h = s.factor(num.subs({u: (1 + t) / 2, q: (1 + t * z) / 2}) /
            (t * (t * z - 1) * (t * z + 1)))
zp = (2 * (1 + t**2) * (1 - t**2 * z**2) / (1 - t**2)**2 - z) / t
n, _ = s.fraction(s.factor(s.diff(h, t) + s.diff(h, z) * zp))
p = s.factor(-n / 2)
z_series = s.series(s.tanh(2 * t / (1 - t**2)) / t, t, 0, 22).removeO()
series = s.Poly(s.series(p.subs(z, z_series), t, 0, 22).removeO(), t)
coefficients = {str(k[0]): str(v) for k, v in series.terms()}
payload = {
    "record": 2885,
    "order": 20,
    "coefficients": coefficients,
    "leading_coefficient": "223/6",
    "claims": {"exact_formal_taylor_polynomial": True,
               "remainder_bound": False,
               "endpoint_sign_certificate": False},
    "next_target": "bound the order-22 remainder on the undecided right cells",
}
out = Path("results/2885_route_b_d4_p_right_taylor.json")
out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
print(json.dumps(payload, indent=2))
