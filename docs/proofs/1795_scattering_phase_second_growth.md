# 1795 — Quadratic growth of the scattering-phase second derivative

Date: 2026-09-21

## Result

`deriv_ccm24ArchimedeanScatteringPhase_factorized` rewrites the actual phase
derivative as `phase * Q`, where `Q` is the conjugate-skew GammaR logarithmic
symbol. The theorem
`deriv_deriv_ccm24ArchimedeanScatteringPhase_factorized` then gives the exact
second derivative as `phase * (Q^2 + Q')`.

`norm_deriv_deriv_ccm24ArchimedeanScatteringPhase_le_quadratic` combines this
identity with the unit-modulus phase, the linear GammaR-log growth bound, and
the uniform GammaR-log derivative bound to obtain a quadratic polynomial
majorant.

## Verification and scope

The paired build completed successfully in 3558 jobs with zero `error:` lines.
The Audit module checks all three declarations; each uses only `propext`,
`Classical.choice`, and `Quot.sound`, with no `sorryAx`.

This closes the phase-growth portion of the W2,1 preparation. The four-term
L1 estimate, S3 kernel-diagonal majorant, detector-specific semi-local
positivity, and RH remain open. No priority claim is made.
