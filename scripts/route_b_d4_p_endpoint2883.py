"""Export exact endpoint identities for the derivative polynomial P."""
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

payload = {
    "record": 2883,
    "P_at_t0": str(s.factor(p.subs(t, 0))),
    "P_at_t_minus1": str(s.factor(p.subs(t, -1))),
    "owner_endpoint_values": {
        "P_t0_z2": int(p.subs({t: 0, z: 2})),
        "P_tminus1_z1": int(p.subs({t: -1, z: 1})),
    },
    "partial_derivatives_right": {
        "dPdt_t0_z2": int(s.diff(p, t).subs({t: 0, z: 2})),
        "dPdz_t0_z2": int(s.diff(p, z).subs({t: 0, z: 2})),
    },
    "claims": {"exact_endpoint_factorisation": True,
               "global_P_sign_certificate": False},
}
out = Path("results/2883_route_b_d4_p_endpoint.json")
out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
print(json.dumps(payload, indent=2))
