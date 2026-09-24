# Record 1966: Support-times-sup derivative budget

Date: 2026-09-24

## Result

The theorem derivativeL1_le_of_support_of_norm_le proves that a compact-log test whose derivative is supported in [-B,B] and bounded pointwise by M has derivativeL1 at most (2*B)*M. The theorem is used as the next quantitative interface for the explicit smoothTransition seed.

## Verification

- Module: ConnesWeilRH/Dev/C1ExplicitSmoothSeedDerivativeBudget.lean
- Audit: ConnesWeilRH/Dev/C1ExplicitSmoothSeedDerivativeBudgetAudit.lean
- Owning build and paired audit pass in WSL ext4.
- Audited declarations use only propext, Classical.choice, and Quot.sound.

## Boundary

The theorem does not provide the concrete M for smoothTransition. Therefore the actual cardinalRaw derivative budget, correction quadratic margin, signed determinant, and RH remain OPEN.
