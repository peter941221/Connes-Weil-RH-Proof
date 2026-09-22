# 1879 - Flat taper inverse-owner budget package

Date: 2026-09-23.

Status: Formally verified in Lean; the taper gap and inverse solve are now
packaged as one same-owner producer interface.

`exists_windowTaperCorrection_seminorm_budget_of_flat_taper` combines:

- the quantitative `windowTaperGram_gap`;
- the existing same-owner `IsUnit` proof for the taper Gram;
- the exact inverse solve `windowTaperGram_solve_mulVec`; and
- `windowTaperCorrection_seminorm_zero_zero_le_of_gap`.

For every admissible flat taper and target, it produces an `alpha > 0` and
the explicit owner inequality

```text
alpha * seminorm(0,0,taperCorrection)
  <= card(ι) * ||target|| * windowTaperBound.
```

Verification: WSL focused build `taper-package-20260923a.log`; successful
footer for 3551 jobs, zero `error:` lines, zero `sorryAx`, and the paired
Audit declaration uses only `[propext, Classical.choice, Quot.sound]`.

This is an interface package, not a numerical threshold or a positivity
theorem.  The remaining analytic task is to supply a strict scalar budget for
the selected owner.
