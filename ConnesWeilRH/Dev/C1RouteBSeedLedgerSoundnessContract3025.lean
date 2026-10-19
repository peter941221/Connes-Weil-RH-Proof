import ConnesWeilRH.Dev.C1RouteBSeedLedgerArithmetic3024
import Mathlib

namespace ConnesWeilRH.Dev

/- The remaining artifact-to-Lean obligation is pointwise: relate the exact
   Lean charge for each cell to the corresponding exported ledger row.  Once
   that relation is supplied, the aggregate inequalities are pure finite
   order arithmetic. -/
theorem routeBSeedLedgerAggregate_of_pointwise_charge_le3025
    {charge4 charge7 : Fin 8192 → ℝ}
    {aggregate4 aggregate7 : ℝ}
    (h4 : ∀ i, charge4 i ≤ aggregate4 / 8192)
    (h7 : ∀ i, charge7 i ≤ aggregate7 / 8192) :
    (∑ i : Fin 8192, charge4 i) ≤ aggregate4 ∧
    (∑ i : Fin 8192, charge7 i) ≤ aggregate7 := by
  constructor
  · calc
      (∑ i : Fin 8192, charge4 i) ≤
          ∑ _i : Fin 8192, aggregate4 / 8192 :=
        Finset.sum_le_sum (fun i _ => h4 i)
      _ = aggregate4 := by
        simp
        field_simp
  · calc
      (∑ i : Fin 8192, charge7 i) ≤
          ∑ _i : Fin 8192, aggregate7 / 8192 :=
        Finset.sum_le_sum (fun i _ => h7 i)
      _ = aggregate7 := by
        simp
        field_simp

end ConnesWeilRH.Dev
