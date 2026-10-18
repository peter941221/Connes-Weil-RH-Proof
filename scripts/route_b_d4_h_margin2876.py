"""Scan the centred residual H(y,z) on the corrected logistic owner path."""
import json
from pathlib import Path
import mpmath as mp

mp.mp.dps = 80


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
    regions = [
        (mp.mpf(1) / 4096, mp.mpf(1353) / 10000, "+"),
        (mp.mpf(1354) / 10000, mp.mpf(3028) / 10000, "-"),
        (mp.mpf(3029) / 10000, mp.mpf(1) / 2, "+"),
    ]
    rows = []
    for left, right, expected in regions:
        t0, t1 = 2 * left - 1, 2 * right - 1
        values = [h_of(t0 + (t1 - t0) * i / 1000,
                       z_of(t0 + (t1 - t0) * i / 1000))
                  for i in range(1001)]
        rows.append({
            "u_left": str(left),
            "u_right": str(right),
            "expected_sign": expected,
            "z_left": mp.nstr(z_of(t0), 30),
            "z_right": mp.nstr(z_of(t1), 30),
            "h_min": mp.nstr(min(values), 30),
            "h_max": mp.nstr(max(values), 30),
        })
    payload = {
        "record": 2876,
        "object": "centered_residual_H",
        "rows": rows,
        "claims": {
            "corrected_owner_path_scan": True,
            "sign_certificate": False,
            "integral_bound_certificate": False,
        },
        "next_target": "prove H sign from y=t^2 and owner bounds on z",
    }
    out = Path("results/2876_route_b_d4_h_margin.json")
    out.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(payload, indent=2))


if __name__ == "__main__":
    main()
