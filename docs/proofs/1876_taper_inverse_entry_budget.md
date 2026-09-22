# 1876 - Taper inverse entry-budget reduction

Date: 2026-09-23.

Status: Formally verified in Lean; explicit finite-matrix budget reduction.

The theorem `matrix_mulVec_norm_le_entryNormSum` bounds a finite matrix action
on the sup norm by the sum of all entry norms.  Applying it to the inverse
taper Gram matrix gives

```text
seminorm(0,0, taperCorrection)
  <= entryNormSum(taperGramInverse) * ||target|| * windowTaperBound.
```

The bridge is exported as
`windowTaperCorrection_seminorm_zero_zero_le_inverse_entryNormSum` and keeps
the exact `IsUnit` inverse owner in the statement.

Verification: WSL focused build `taper-inverse-budget-1876b.log`; successful
footer for 3551 jobs, zero `error:` lines, zero `sorryAx`, and the paired
Audit declarations use only `[propext, Classical.choice, Quot.sound]`.

This reduces the coefficient problem to a finite inverse-matrix entry budget.
It does not prove that the entry sum is small, establish detector-specific
semi-local positivity, or prove RH.
