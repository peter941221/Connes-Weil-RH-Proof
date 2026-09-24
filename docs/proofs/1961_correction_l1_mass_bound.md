# Proof Record 1961: correction L1 mass envelope

## Result

Added `ConnesWeilRH/Dev/C1CorrectionL1MassBound.lean` with
`l1Mass_correction_le`.

For the explicit finite-node correction, the theorem proves the finite-sum
triangle bound

```text
l1Mass(correction nodes seed y)
  <= sum over z in nodes of
       norm(y z / (nodeProduct nodes z z * laplaceAt(seed, 0)))
       * l1Mass(cardinalRaw nodes seed z)
```

The proof expands only the correction test, applies the finite-sum norm
inequality pointwise, then exchanges the finite sum and integral. It does not
assume any sign, numerical bump formula, or determinant estimate.

## Verification

Focused source build and paired audit were run in a WSL ext4 verification copy:

```text
lake build ConnesWeilRH.Dev.C1CorrectionL1MassBound
lake build ConnesWeilRH.Dev.C1CorrectionL1MassBoundAudit
```

The audit reports exactly:

```text
[propext, Classical.choice, Quot.sound]
```

## Map 106 impact

This removes the finite-sum/L1 wrapper from the correction budget. The next
real quantitative obligation is to bound each `l1Mass(cardinalRaw ...)` while
retaining the node-product denominator and the actual finite zero owner.
No `hcorrectionQuadratic`, signed determinant, producer witness, or RH claim
has been discharged by this record.