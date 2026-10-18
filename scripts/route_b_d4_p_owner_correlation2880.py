"""Show that P sign certification must preserve the owner t-z correlation."""
import json
from pathlib import Path
import mpmath as mp
import sympy as s

T, Z, U, Q = s.symbols("t z u q")
phi = 1 / U - 1 / (1 - U)
velocity = -s.diff(phi, U) * Q * (1 - Q)
jet = Q
for _ in range(4):
    jet = s.factor(s.diff(jet, U) + s.diff(jet, Q) * velocity)
numerator, _ = s.fraction(jet)
H_SYMBOLIC = s.factor(numerator.subs({U: (1 + T) / 2, Q: (1 + T * Z) / 2}) /
                     (T * (T * Z - 1) * (T * Z + 1)))
z_prime = (2*T*(1+T**2)*(1-T**2*Z**2)/(1-T**2)**2-Z)/T
derivative = s.factor(s.diff(H_SYMBOLIC, T) + s.diff(H_SYMBOLIC, Z) * z_prime)
numerator_p, _ = s.fraction(derivative)
P_EVAL = s.lambdify((T, Z), s.factor(-numerator_p / 2), "mpmath")

mp.mp.dps = 60


def z_of(t):
    return mp.tanh(2 * t / (1 - t * t)) / t if t else mp.mpf(2)


def p_of(t, z):
    # Rebuild P from the same exact SymPy derivation as record 2879.
    return P_EVAL(t, z)


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
