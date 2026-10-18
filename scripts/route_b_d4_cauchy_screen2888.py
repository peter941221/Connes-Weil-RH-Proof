"""Screen Cauchy radii for the right endpoint Taylor remainder."""
import json
from pathlib import Path
import mpmath as mp

mp.mp.dps = 50


def z_of(t):
    return mp.tanh(2 * t / (1 - t * t)) / t if t else mp.mpf(2)


def h_of(t, z):
    y = t * t
    return (24*y**5*z**3 + 36*y**5*z**2 + 18*y**5*z + 3*y**5
            + 96*y**4*z**3 + 144*y**4*z**2 + 68*y**4*z + 9*y**4
            + 144*y**3*z**3 + 72*y**3*z**2 - 148*y**3*z - 114*y**3
            + 96*y**2*z**3 - 144*y**2*z**2 - 240*y**2*z + 18*y**2
            + 24*y*z**3 - 108*y*z**2 + 50*y*z + 63*y - 4*z + 21)


def main():
    rows = []
    for radius in (mp.mpf("0.02"), mp.mpf("0.05"), mp.mpf("0.1")):
        values = []
        for k in range(2000):
            t = radius * mp.e**(2j * mp.pi * k / 2000)
            values.append(abs(h_of(t, z_of(t))))
        maximum = max(values)
        rows.append({
            "radius": str(radius),
            "sample_count": 2000,
            "sampled_max": mp.nstr(maximum, 30),
            "order_22_geometric_scale": mp.nstr(maximum * (mp.mpf("0.01") / radius)**22, 30),
        })
    payload = {
        "record": 2888,
        "rows": rows,
        "claims": {
            "complex_circle_sample_screen": True,
            "analytic_circle_bound": False,
            "full_remainder_certificate": False,
        },
        "next_target": "replace sampled maximum by a rigorous complex-circle enclosure",
    }
    out = Path("results/2888_route_b_d4_cauchy_screen.json")
    out.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(payload, indent=2))


if __name__ == "__main__":
    main()
