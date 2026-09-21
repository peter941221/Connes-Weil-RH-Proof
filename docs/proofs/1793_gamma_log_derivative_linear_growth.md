# 1793 — Linear growth of the critical GammaR logarithmic derivative

Date: 2026-09-21

## Result

`norm_ccm24CriticalGammaRLogDeriv_le_linear` integrates the global derivative
bound from record 1792 with the interval mean-value theorem and proves

`||L(xi)|| <= ||L(0)|| + 18 * pi * |xi|`,

where `L` is the actual critical GammaR logarithmic derivative.

## Verification and scope

The focused paired build completed successfully in 3556 jobs. The Audit
declaration depends only on `propext`, `Classical.choice`, and `Quot.sound`,
with no `sorryAx`.

This is a genuine polynomial growth input for the scattering phase. It does
not yet prove the scattering-phase L1 estimate, S3 positivity,
detector-specific semi-local positivity, or RH. No priority claim is made.
