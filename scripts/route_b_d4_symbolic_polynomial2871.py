"""Emit an auditable exact-coefficient D4 numerator certificate.

The output is deliberately algebraic: it does not claim that interval
evaluation has proved the three signs.  It freezes the integer polynomial
that a later centred-Taylor or monotonicity proof must certify.
"""
import hashlib
import json
import pathlib
import sympy as s
u, q = s.symbols('u q')
phi = 1/u - 1/(1-u)
v = -s.diff(phi, u) * q * (1-q)
p = q
for _ in range(4):
    p = s.factor(s.diff(p, u) + s.diff(p, q) * v)
num, den = s.fraction(p)
print('D4 =')
print(s.factor(p))
print('numerator degree in q:', s.degree(num, q))
print('numerator degree in u:', s.degree(num, u))

payload = {
    "record": 2872,
    "object": "route_b_logistic_D4_numerator",
    "normal_form": "D4 = q*(q-1)*P(u,q)/(u^8*(u-1)^8)",
    "degree_u": int(s.degree(num, u)),
    "degree_q": int(s.degree(num, q)),
    "coefficients_u_descending_q_descending": [
        [int(c) for c in s.Poly(num, u, q).coeffs()]
    ],
    "expanded_polynomial": str(s.Poly(num, u, q).as_expr()),
    "sign_regions": [
        ["1/4096", "1353/10000", "+"],
        ["1354/10000", "3028/10000", "-"],
        ["3029/10000", "1/2", "+"],
    ],
    "claims": {
        "exact_symbolic_expansion": True,
        "interval_sign_certificate": False,
        "integral_bound_certificate": False,
    },
}
text = json.dumps(payload, indent=2, sort_keys=True) + "\n"
out = pathlib.Path("results/2872_route_b_d4_symbolic_certificate.json")
out.write_text(text, encoding="utf-8")
print("wrote", out)
print("sha256", hashlib.sha256(text.encode()).hexdigest())
