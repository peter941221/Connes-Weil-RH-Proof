# 988 — finite-vanishing test g: exact {0,1/2,1} vanish, but degenerate psi

Date: 2026-08-11. Status: numeric probe (WSL numpy). RH NOT claimed. Evidence only.
Companion: docs/proofs/988_vanishing_probe.py.

## Construction
g = q - Proj_span(q) where q = smooth bump on (0.4,2.2) and span = {1, e^{t/2}, e^t};
this makes M(g,0)=M(g,1/2)=M(g,1)=0 exactly (orthogonal complement). Verified:

    M(g,0)= -4.1e-14   M(g,1/2)= -7.8e-14   M(g,1)= -1.6e-13   (<=> in the vanishing family)
    max|g|=0.51, |g|^2_L2=0.0366  (non-degenerate L2)

## Result: psi NOT decisive (degenerate arch/pole)

    conv-square center  A=g2(0) = -0.0
    arch = -0.0017        pole = -0.0        term2 = -0.0020
    psi = pole - arch - term2 = +0.0036

The test g is supported ONE-SIDED in the additive log coordinate (0.4..2.2 only).
A one-sided g makes the conv-square centre g2(0)=int g(s) g(-s) ds ~ 0 (no negative-s
overlap), so A~0, arch~pole~term2~0.  psi=+0.0036 is driven by near-zero terms, i.e. a
degenerate scale -- it is NOT evidence for any honest sign of the criterion.

## Honest bottom line
Constructing a vanishing test in the correct family is doable (LSQ orth-complement), but a compact
one-sided log test makes the leading arch term trivial.  A decisive C1 sign probe needs a
test that is (a) finite-vanishing, (b) DANGLED both-sided with positive leading A=(g*g)(0),
and (c) whose supporting window overlips the finite-prime sample at 2.  That is not an
assembly step; it is the real analytic construction.  Numerics here neither prove nor refute
the criterion; RH NOT claimed.
