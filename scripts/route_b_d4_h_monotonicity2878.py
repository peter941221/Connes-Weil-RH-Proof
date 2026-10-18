"""Scan the owner-path derivative of centred residual H."""
import json
from pathlib import Path
import mpmath as mp

mp.mp.dps = 70


def z_of(t):
    return mp.tanh(2 * t / (1 - t * t)) / t if t else mp.mpf(2)


def h_of(t):
    z = z_of(t)
    y = t * t
    return (24*y**5*z**3 + 36*y**5*z**2 + 18*y**5*z + 3*y**5
            + 96*y**4*z**3 + 144*y**4*z**2 + 68*y**4*z + 9*y**4
            + 144*y**3*z**3 + 72*y**3*z**2 - 148*y**3*z - 114*y**3
            + 96*y**2*z**3 - 144*y**2*z**2 - 240*y**2*z + 18*y**2
            + 24*y*z**3 - 108*y*z**2 + 50*y + 63*y - 4*z + 21)


def main():
    regions = [
        (mp.mpf(1) / 4096, mp.mpf(1353) / 10000),
        (mp.mpf(1354) / 10000, mp.mpf(3028) / 10000),
        (mp.mpf(3029) / 10000, mp.mpf(1) / 2),
    ]
    rows = []
    for left, right in regions:
        t0, t1 = 2 * left - 1, 2 * right - 1
        deriv = [mp.diff(h_of, t0 + (t1 - t0) * i / 1000)
                 for i in range(1001)]
        rows.append({
            "u_left": str(left),
            "u_right": str(right),
            "dHdt_min": mp.nstr(min(deriv), 30),
            "dHdt_max": mp.nstr(max(deriv), 30),
            "sampled_sign_changes": sum(a * b < 0 for a, b in zip(deriv, deriv[1:])),
        })
    payload = {
        "record": 2878,
        "rows": rows,
        "claims": {
            "owner_path_derivative_scan": True,
            "monotonicity_certificate": False,
            "sign_certificate": False,
        },
        "next_target": "prove dHdt signs on the two outer regions with interval bounds",
    }
    out = Path("results/2878_route_b_d4_h_monotonicity.json")
    out.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(payload, indent=2))


if __name__ == "__main__":
    main()
