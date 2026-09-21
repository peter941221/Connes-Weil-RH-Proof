# 1794 — Linear growth of the scattering-phase derivative

Date: 2026-09-21

## Result

`norm_deriv_ccm24ArchimedeanScatteringPhase_le_linear` transfers the linear
growth estimate for the critical GammaR logarithmic derivative to the actual
archimedean scattering phase. The exact quotient derivative cancels the
factor norm because the phase has unit modulus.

## Verification and scope

The focused paired build completed successfully with zero `error:` lines. The
Audit declaration uses only `propext`, `Classical.choice`, and `Quot.sound`,
with no `sorryAx`.

This is a polynomial growth estimate for one factor in the second product
derivative. The complete scattering-phase L1 estimate, S3 positivity,
detector-specific semi-local positivity, and RH remain open. No priority claim
is made.
