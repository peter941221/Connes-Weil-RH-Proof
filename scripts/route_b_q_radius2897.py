"""Record the nearest complex singularity calculation for centered Q."""
import json
from pathlib import Path
import mpmath as mp

mp.mp.dps = 60
b = 4 / mp.pi
root_re = mp.sqrt(1 + b**2) ** -1
root_im = b * root_re
payload = {
    "record": 2897,
    "nearest_tanh_pole_equation": "2*t/(1-t^2) = i*pi/2",
    "quadratic": "t^2 + (4*i/pi)*t - 1 = 0",
    "root_real_abs": mp.nstr(root_re, 40),
    "root_imag_abs": mp.nstr(root_im, 40),
    "root_modulus": mp.nstr(mp.sqrt(root_re**2 + root_im**2), 40),
    "candidate_convergence_radius": "1",
    "claims": {"nearest_pole_numeric_identification": True,
               "power_series_radius_certificate": False},
    "next_target": "formalize radius-one lower bound and Q series identity",
}
out = Path("results/2897_route_b_q_radius.json")
out.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
print(json.dumps(payload, indent=2))
