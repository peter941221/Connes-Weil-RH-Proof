# 1787 — Critical-line second digamma derivative

Date: 2026-09-21

## Result

`hasDerivAt_deriv_digamma_criticalQuarterLine` transports the cubic reciprocal
series for the derivative of `deriv Complex.digamma` from the strict
quarter half-plane to the actual line with real part one quarter. It uses the
digamma recurrence once and differentiates the resulting inverse-square
correction along the real-frequency parameter.

The theorem is the direct critical-line consumer of record 1786 and is the
second-order special-function input for the GammaR scattering-factor chain.

## Verification and scope

The paired focused build completed successfully in 3554 jobs. Its Audit
declaration depends only on `propext`, `Classical.choice`, and `Quot.sound`,
with no `sorryAx`.

This is formal interface evidence only. It does not establish the complete
scattering-product W2,1 estimate, the S3 kernel-diagonal bound,
detector-specific semi-local positivity, or RH. No priority claim is made.
