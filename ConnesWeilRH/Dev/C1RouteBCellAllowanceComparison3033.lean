import ConnesWeilRH.Dev.C1RouteBSourceCellEnvelope2834

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed

open ConnesWeilRH.Dev

/-! Cell-level bridge used by the 3032 finite-target consumer.

The first premise is the exact-real evaluator-to-rectangle comparison.  The
second is the exported-ledger rounding allowance.  Once both are proved, the
source charge is bounded by the ledger row plus its allowance.
-/
theorem routeBSourceCharge_le_ledger_add_allowance3033
    (i order : ℕ) {norm ledger allowance : ℝ}
    (heval : routeBSourceNorm2834 i order ≤ norm)
    (hrow : 4 * ((2047 : ℝ) / 33554432) * norm ≤ ledger + allowance) :
    routeBSourceCharge2834 i order ≤ ledger + allowance := by
  rw [routeBSourceCharge_eq_width_norm2834]
  exact le_trans
    (mul_le_mul_of_nonneg_left heval (by positivity)) hrow

end ConnesWeilRH.Source.C1ExplicitSmoothSeed
