# Record 1967: expNegInvGlue derivative constant

Date: 2026-09-24

## Closed

Lean proves:

    norm (deriv expNegInvGlue x) <= 4

for every real x. The proof uses the exact derivative formula supplied by Mathlib and the elementary positive-domain inequality:

    t >= 0 -> t^2 * exp(-t) <= 4

The negative half-line is handled by the zero branch of expNegInvGlue.

## Evidence

- Module: ConnesWeilRH/Dev/C1ExplicitSmoothSeedDerivativeConstants.lean
- Audit: ConnesWeilRH/Dev/C1ExplicitSmoothSeedDerivativeConstantsAudit.lean
- Owning build: lake build ConnesWeilRH.Dev.C1ExplicitSmoothSeedDerivativeConstants
- Paired audit completed successfully.
- Audited declarations use only propext, Classical.choice, and Quot.sound.

## Boundary

The direct product derivative bound for smoothSeedRaw was attempted and removed after compilation exposed an unclosed bridge between the raw real function and the CompactLogTest coercion. Therefore derivativeL1 smoothSeed, the actual cardinalRaw numerical budget, hcorrectionQuadratic, the signed determinant, and RH remain OPEN.
