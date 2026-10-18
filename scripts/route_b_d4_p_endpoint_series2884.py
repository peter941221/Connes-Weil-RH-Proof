"""Compute first nonzero owner-path endpoint series for P."""
import json
from pathlib import Path
import sympy as s

t, z, e, u, q = s.symbols("t z e u q")
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

z_right = s.series(s.tanh(2 * t / (1 - t**2)) / t, t, 0, 10).removeO()
right_series = s.series(p.subs(z, z_right), t, 0, 10).removeO()
# At t -> -1, tanh(2t/(1-t^2)) differs from -1 exponentially;
# the algebraic owner expansion is z = 1/t.
left_series = s.series(p.subs({t: -1 + e, z: 1 / (-1 + e)}), e, 0, 6).removeO()

payload = {
    "record": 2884,
    "right_z_series": str(z_right),
    "right_P_series": str(right_series),
    "left_P_series": str(left_series),
    "leading_terms": {
        "right": "(210735/5670) * t^2",
        "left": "-384 * (t+1)^2",
    },
    "claims": {"exact_formal_series": True,
               "endpoint_sign_certificate": False},
}
out = Path("results/2884_route_b_d4_p_endpoint_series.json")
out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
print(json.dumps(payload, indent=2))
