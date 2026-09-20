# 1753 — Finite-span prime-profile quadratic readback

Date: 2026-09-21

## Result

The formal theorem
`signedProfileTerm_spanObj_eq_pair_profile_quadratic` expands the actual
signed profile term at every prime-log coordinate for a finite root span
`spanObj w y`. The convolution-square observable is exactly the double sum of
the pair-basis profiles weighted by the coefficient products `y i * y j`.

This is an equality for the real signed-budget observable, not an equality for
the root test itself. It uses the genuine convolution-square expansion and the
Hermitian bilateral profile, so no pointwise or universal sign assumption is
introduced.

## Route meaning

The remaining detector-specific signed budget can now be attacked as a finite
quadratic-form certificate once the actual OrbitG8 owner is represented by a
finite root span and its pair-profile coefficients are bounded. This leaf
does not provide that representation, a sign certificate, detector health,
semi-local positivity, or RH.

## Evidence

Focused owner plus Audit build:

`build-logs/shortest_route_20260920_span_profile_v3.log`

The log reports `Build completed successfully (3784 jobs)`, zero `error:`
lines, and the Audit axiom list
`[propext, Classical.choice, Quot.sound]`.
