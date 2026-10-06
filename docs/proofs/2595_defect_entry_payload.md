# 2595 defect-entry payload

## What changed

The 2351 Fraction witness is reconstructed into 900 exact nonnegative rational
entry bounds. The generator checks that the 30 reconstructed row sums equal the
committed `row_bounds_exact` values before writing Lean.

The Lean output now defines one `Fin 30 -> NNReal` row payload per matrix row,
proves each row sum separately, and dispatches the finite-row theorem by
`fin_cases`. This avoids one proof term expanding all 900 entries at once.

## Boundary

This is a data and arithmetic layer only. It does not establish that the
analytic Lean defect matrix is enclosed by these values. The remaining premise
is still an explicit actual-entry bound, together with the actual defect
operator equality.

## Verification

The Python generator completed with 30 rows and 900 entries and reproduced the
committed row-sum strings exactly. The Mathlib `Analysis.Matrix.Normed` cache
entry is now built. The project chain `2590 -> 2593 -> 2595` was started from
a WSL-native source copy but stopped before completion because `2590`
elaboration remained long-running; no Lean pass is claimed.



