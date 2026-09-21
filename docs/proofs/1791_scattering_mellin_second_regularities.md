# 1791 — Scattering-weighted Mellin profile second regularity

Date: 2026-09-21

## Result

`differentiable_deriv_ccm24ScatteringMellinProfile` proves that the
derivative of the actual scattering phase multiplied by the concrete critical
Mellin profile is differentiable on the real line. It combines the actual
phase second-order regularity with the profile's exact second chain rule and
records the product-rule interface needed by the annular two-IBP consumer.

## Verification and scope

The focused paired build completed successfully in 3557 jobs. The Audit
declaration depends only on `propext`, `Classical.choice`, and `Quot.sound`,
with no `sorryAx`.

The remaining analytic obligation is an L1 estimate for the four terms in the
second product derivative. This record does not assert that estimate,
detector-specific semi-local positivity, or RH. No priority claim is made.
