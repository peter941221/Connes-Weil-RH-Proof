Record 2536: local coupled bump envelope through order four
Date: 2026-10-03

The theorem widthBump_iteratedDeriv_abs_le_local2536 bounds the actual
widthBump derivative of any order from zero through four. Its inputs describe
geometry only: a positive radius and bounds near<=|position/radius|<=far,
with 0<=near<1. There is no sampled derivative or numerical upper-bound premise.

The local bound multiplies the absolute-coefficient polynomial at far by
t0^(2*order)*exp(-30*t0)/radius^order, where t0=1/(1-near^2).
The proof keeps the inverse-deficit power and exponential together. It uses
the existing exact derivative identity inside the support and the proved
zero derivative outside, including the flat boundary.

Proof chain:

```text
powerExpUpper2349 at position/lower
  -> powerExp_le_at_lower2536
  -> coupled exponential/inverse-power bound
       + explicit local polynomial magnitude, orders 0..4
       + actual widthBump derivative identity and zero extension
  -> widthBump_iteratedDeriv_abs_le_local2536
```

The module supplies the scaled-bump part of record 2535's analytic envelope.
Weighted complex family composition and numerical tables remain separate
obligations. In particular, this theorem alone does not instantiate 2534's
Lipschitz hypothesis for the weighted third-derivative channel.

Validation uses the paired audit and the project root target. The acceptance
artifact records the build footer, the three axiom reports, and byte identity
of the project import cone between the authoritative sources and build mirror.
All three audited declarations use exactly
[propext, Classical.choice, Quot.sound]. No 2271 manifest-bound source changes.
Final acceptance: 4383 build jobs, zero error lines, 607 byte-identical project
sources across the audit and root import cones. Four pre-existing newline-only
mirror differences were synchronized before the final successful build.

Evidence:
ConnesWeilRH/Dev/C1RouteACoupledBumpEnvelope2536.lean
ConnesWeilRH/Dev/C1RouteACoupledBumpEnvelope2536Audit.lean
scripts/validate_coupled_bump_2536.py
results/2536_coupled_bump_validation.json

Next: compose this local bound with the signed complex exponential derivatives
for the existing weighted external-family function, then supply the concrete
10240-cell numerical inequalities. The exact-owner transfer and full signed
margin remain open.
