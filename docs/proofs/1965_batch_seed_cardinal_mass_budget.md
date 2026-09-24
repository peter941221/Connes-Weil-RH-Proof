# Record 1965: Batch seed/cardinalRaw mass-budget closure

Date: 2026-09-24

## Closed

1. The explicit smooth seed has support in [-2,2] and pointwise norm at most 1, hence Lean proves:

    l1Mass smoothSeed <= 4

2. For every complex a, Lean proves:

    l1Mass (exponentialWeight smoothSeed a)
      <= 4 * exp(2 * |a.re|)

3. The actual cardinalRaw recurrence now has an exact budget consumer. Given a budget function over the exact suffix list and a proved one-step derivative recurrence, Lean returns:

    l1Mass (cardinalRaw nodes seed z) <= budget (nodes.erase z).toList

No owner replacement, fixed-prime model, or unsigned determinant shortcut is used.

## Evidence

- Seed mass module: ConnesWeilRH/Dev/C1ExplicitSmoothSeedMassBudget.lean
- Seed mass audit: ConnesWeilRH/Dev/C1ExplicitSmoothSeedMassBudgetAudit.lean
- Cardinal budget module: ConnesWeilRH/Dev/C1ExplicitSmoothSeedDerivativeBudget.lean
- Cardinal budget audit: ConnesWeilRH/Dev/C1ExplicitSmoothSeedDerivativeBudgetAudit.lean
- Owning and paired-audit builds completed successfully.
- All audited declarations use only propext, Classical.choice, and Quot.sound.

## Still open

The result does not provide explicit derivativeL1 constants for the concrete smoothTransition seed, a numerical separation delta for the actual zero owner, the correction quadratic inequality, a negative same-owner signed determinant, or the joint tail margin. Therefore RH remains unproved.
