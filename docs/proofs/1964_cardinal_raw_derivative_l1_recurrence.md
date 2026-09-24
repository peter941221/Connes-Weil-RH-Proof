# Record 1964: CardinalRaw derivative/L1 recurrence

Date: 2026-09-24

## Result

The actual finite-node selector used by cardinalRaw now has a checked L1 budget recurrence. For every compact logarithmic test f and complex shift a, the new theorem proves:

    l1Mass (derivativeShift f a)
      <= derivativeL1 f + norm(a) * l1Mass f

where derivativeL1 f is the integral of the norm of the derivative of f.test. Induction over the exact List produced by (nodes.erase z).toList gives l1Mass_cardinalRaw_le.

## Evidence

- Source: ConnesWeilRH/Dev/C1ExplicitSmoothSeedDerivativeBudget.lean
- Audit: ConnesWeilRH/Dev/C1ExplicitSmoothSeedDerivativeBudgetAudit.lean
- Owning module: lake build ConnesWeilRH.Dev.C1ExplicitSmoothSeedDerivativeBudget
- Paired audit: lake env lean ConnesWeilRH/Dev/C1ExplicitSmoothSeedDerivativeBudgetAudit.lean
- Both completed successfully in the WSL ext4 mirror.
- The audit reports only propext, Classical.choice, and Quot.sound.

## Boundary

This is not a numerical closure and not an RH proof. The remaining obligations are explicit derivative/L1 constants for the concrete seed and its exponential weight, a lower bound for the actual nodeProduct denominator, the correction quadratic budget, and the same-owner signed determinant.


## Denominator follow-up

The same module proves a generic lower bound for the actual nodeProduct denominator from a certified separation delta. The proof keeps the exact (nodes.erase z).toList owner and reports only the standard three axioms. The numerical separation delta remains OPEN.
