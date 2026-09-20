# 1790 — Actual scattering phase second-order regularity

Date: 2026-09-21

## Result

`differentiable_ccm24ArchimedeanScatteringPhase_deriv` proves that the
real-frequency derivative of the concrete CCM24 Archimedean scattering phase
is differentiable. The proof differentiates the exact quotient formula, using
the actual factor's first and second derivative interfaces and the conjugation
chain rule. The denominator is discharged from the factor's exact
nonvanishing theorem.

## Verification and scope

The focused paired build completed successfully in 3554 jobs. The Audit
declaration depends only on `propext`, `Classical.choice`, and `Quot.sound`,
with no `sorryAx`.

This is a regularity interface for the eventual scattering-product W2,1
consumer. It does not prove an L1 bound, the S3 kernel-diagonal majorant,
detector-specific semi-local positivity, or RH. No priority claim is made.
