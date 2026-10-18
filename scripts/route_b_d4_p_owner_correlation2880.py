"""Show that P sign certification must preserve the owner t-z correlation."""
import json
from pathlib import Path
import mpmath as mp

mp.mp.dps = 60


def z_of(t):
    return mp.tanh(2 * t / (1 - t * t)) / t if t else mp.mpf(2)


def p_of(t, z):
    # Exact P from record 2879, kept as a direct polynomial evaluator.
    return (
        72*t**15*z**4 + 72*t**15*z**3 + 18*t**15*z**2
        - 84*t**14*z**3 - 144*t**14*z**2 - 81*t**14*z - 15*t**14
        + 360*t**13*z**4 + 360*t**13*z**3 + 14*t**13*z**2 - 72*t**13*z - 18*t**13
        - 72*t**12*z**3 - 144*t**12*z**2 - 76*t**12*z - 6*t**12
        + 720*t**11*z**4 + 432*t**11*z**3 - 440*t**11*z**2 - 360*t**11*z - 86*t**11
        + 180*t**10*z**3 + 576*t**10*z**2 + 765*t**10*z + 399*t**10
        + 720*t**9*z**4 - 144*t**9*z**3 - 1108*t**9*z**2 - 432*t**9*z + 80*t**9
        + 144*t**8*z**3 - 618*t**8*z - 756*t**8
        + 360*t**7*z**4 - 504*t**7*z**3 - 910*t**7*z**2 + 144*t**7*z + 388*t**7
        - 108*t**6*z**3 - 432*t**6*z**2 - 375*t**6*z + 351*t**6
        + 72*t**5*z**4 - 216*t**5*z**3 - 314*t**5*z**2 + 504*t**5*z + 190*t**5
        - 72*t**4*z**3 + 144*t**4*z**2 + 408*t**4*z + 90*t**4
        - 76*t**3*z**2 + 216*t**3*z - 46*t**3
        + 12*t**2*z**3 - 21*t**2*z - 63*t**2 + 4*t - 2*z)


def main():
    regions = [(mp.mpf(1)/4096, mp.mpf('.1353')),
               (mp.mpf('.3029'), mp.mpf('.5'))]
    rows = []
    for left, right in regions:
        t0, t1 = 2*left-1, 2*right-1
        z0, z1 = z_of(t0), z_of(t1)
        owner = [p_of(t0+(t1-t0)*i/1000, z_of(t0+(t1-t0)*i/1000)) for i in range(1001)]
        box = [p_of(t0+(t1-t0)*i/100, z0+(z1-z0)*j/100)
               for i in range(101) for j in range(101)]
        rows.append({"u_left": str(left), "u_right": str(right),
                     "owner_min": mp.nstr(min(owner), 24),
                     "owner_max": mp.nstr(max(owner), 24),
                     "independent_box_min": mp.nstr(min(box), 24),
                     "independent_box_max": mp.nstr(max(box), 24)})
    payload = {"record": 2880, "rows": rows,
               "claims": {"correlation_diagnostic": True,
                          "polynomial_sign_certificate": False},
               "decision": "retain t-z owner correlation in the formal enclosure"}
    out = Path("results/2880_route_b_d4_p_owner_correlation.json")
    out.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(payload, indent=2))


if __name__ == "__main__":
    main()
