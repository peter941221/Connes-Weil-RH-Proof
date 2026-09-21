# 1792 — Uniform critical GammaR logarithmic-derivative bound

Date: 2026-09-21

## Result

`norm_deriv_ccm24CriticalGammaRLogDeriv_le` proves the global real-frequency
bound

`||deriv ccm24CriticalGammaRLogDeriv xi|| <= 18 * pi`.

The proof uses the quarter-line digamma recurrence, the existing uniform
bound for the shifted digamma derivative, and the elementary bound on the
inverse quarter-line argument. It is a formal quantitative input, not a
numerical fit or an appeal to Stirling asymptotics.

## Verification and scope

The focused paired build completed successfully in 3555 jobs. The Audit
declaration uses only `propext`, `Classical.choice`, and `Quot.sound`, with no
`sorryAx`.

This bounds one GammaR-log derivative. It does not yet prove the linear growth
of the log symbol, the scattering-phase L1 estimate, S3 positivity,
detector-specific semi-local positivity, or RH. No priority claim is made.
