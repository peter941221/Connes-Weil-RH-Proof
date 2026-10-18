# 2872 Route B D4 symbolic certificate

The D4 logistic derivative is now exported as a deterministic JSON artifact
with the exact integer coefficients of its numerator, its `(u,q)` degrees,
the proposed rational sign regions, and explicit nonclaims. The generator is
`scripts/route_b_d4_symbolic_polynomial2871.py`.

This closes the algebraic replay input only. It does not certify the signs of
the polynomial on the three regions and does not certify the D4 integral bound.
The next proof step must use the frozen polynomial with a centred Taylor,
Bernstein, or monotonicity enclosure that keeps `q = T(u)` owner-coherent.

Artifact: `results/2872_route_b_d4_symbolic_certificate.json`

The artifact records `interval_sign_certificate = false` and
`integral_bound_certificate = false` so a later consumer cannot mistake this
algebraic bridge for the missing analytic proof.
