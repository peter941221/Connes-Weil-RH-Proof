"""Export exact endpoint identities for the centred D4 residual H."""
import json
from pathlib import Path
import sympy as s

y, z = s.symbols("y z")
H = (24*y**5*z**3 + 36*y**5*z**2 + 18*y**5*z + 3*y**5
     + 96*y**4*z**3 + 144*y**4*z**2 + 68*y**4*z + 9*y**4
     + 144*y**3*z**3 + 72*y**3*z**2 - 148*y**3*z - 114*y**3
     + 96*y**2*z**3 - 144*y**2*z**2 - 240*y**2*z + 18*y**2
     + 24*y*z**3 - 108*y*z**2 + 50*y*z + 63*y - 4*z + 21)

payload = {
    "record": 2877,
    "H_at_y0": str(s.factor(H.subs(y, 0))),
    "H_at_y1": str(s.factor(H.subs(y, 1))),
    "owner_endpoint_values": {
        "H_y0_z2": int(H.subs({y: 0, z: 2})),
        "H_y1_z1": int(H.subs({y: 1, z: 1})),
    },
    "partial_y_at_owner_endpoints": {
        "dHdy_y1_z1": int(s.diff(H, y).subs({y: 1, z: 1})),
        "dHdy_y0_z2": int(s.diff(H, y).subs({y: 0, z: 2})),
    },
    "claims": {
        "exact_endpoint_factorisation": True,
        "global_sign_certificate": False,
        "integral_bound_certificate": False,
    },
}
out = Path("results/2877_route_b_d4_h_endpoint.json")
out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
print(json.dumps(payload, indent=2))
