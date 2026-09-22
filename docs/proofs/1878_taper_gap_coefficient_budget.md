# 1878 - Taper gap coefficient and seminorm budget

Date: 2026-09-23.

Status: Formally verified in Lean; the taper gap now feeds an explicit
coefficient and owner-seminorm budget.

`windowTaperGram_solve_norm_le_of_gap` proves, for a solved tapered system,

```text
alpha * ||coeff|| <= card(ι) * ||target||.
```

The finite-cardinality factor is intentional: the current coefficient norm is
the function-space sup norm, so this is a conservative but completely
explicit finite-dimensional pairing bound.  The same-owner corollary
`windowTaperCorrection_seminorm_zero_zero_le_of_gap` then gives

```text
alpha * seminorm(0,0,taperCorrection)
  <= card(ι) * ||target|| * windowTaperBound.
```

Verification: WSL focused build `taper-coeff-budget-20260923b.log`; successful
footer for 3551 jobs, zero `error:` lines, zero `sorryAx`, and the paired Audit
declaration uses only `[propext, Classical.choice, Quot.sound]`.

This is now the direct scalar input to the contraction consumer.  It does not
yet prove that the scalar is below the strict threshold, and it does not prove
detector-specific semi-local positivity or RH.
