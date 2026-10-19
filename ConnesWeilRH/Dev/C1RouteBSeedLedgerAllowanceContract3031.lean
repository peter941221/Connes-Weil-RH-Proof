import Mathlib

namespace ConnesWeilRH.Dev

/-!
Formal contract for the 3029 directed-rounding allowance.

The numerical replay found a total excess below 2.4e-36 (order 4) and
2.6e-30 (order 7).  Until the interval evaluator is connected to Lean's
exact real semantics, those numbers are represented here by the deliberately
conservative uniform allowance 1/10 per cell.  This file proves the arithmetic
of that contract; it does not assert the missing evaluator soundness premise.
-/

def routeBSeedUniformAllowance3031 : Fin 8192 → ℝ := fun _ => (1 : ℝ) / 10

theorem routeBSeedLedgerAggregate_with_allowance3031
    {charge ledger allowance : Fin 8192 → ℝ}
    {aggregate margin target : ℝ}
    (hpoint : ∀ i, charge i ≤ ledger i + allowance i)
    (hledger : (∑ i : Fin 8192, ledger i) ≤ aggregate)
    (hallow : (∑ i : Fin 8192, allowance i) ≤ margin)
    (htarget : aggregate + margin < target) :
    (∑ i : Fin 8192, charge i) < target := by
  calc
    (∑ i : Fin 8192, charge i) ≤
        ∑ i : Fin 8192, (ledger i + allowance i) :=
      Finset.sum_le_sum (fun i _ => hpoint i)
    _ = (∑ i : Fin 8192, ledger i) + (∑ i : Fin 8192, allowance i) := by
      rw [Finset.sum_add_distrib]
    _ ≤ aggregate + margin := add_le_add hledger hallow
    _ < target := htarget

theorem routeBSeedUniformAllowance_sum3031 :
    (∑ i : Fin 8192, routeBSeedUniformAllowance3031 i) = (4096 : ℝ) / 5 := by
  simp [routeBSeedUniformAllowance3031]
  norm_num

theorem routeBSeedLedger_order4_target3031
    {charge ledger : Fin 8192 → ℝ}
    (hpoint : ∀ i, charge i ≤ ledger i + routeBSeedUniformAllowance3031 i)
    (hledger : (∑ i : Fin 8192, ledger i) ≤ (1400 : ℝ)) :
    (∑ i : Fin 8192, charge i) < (1500 : ℝ) := by
  apply routeBSeedLedgerAggregate_with_allowance3031 hpoint hledger
  · rw [routeBSeedUniformAllowance_sum3031]
    norm_num
  · norm_num

theorem routeBSeedLedger_order7_target3031
    {charge ledger : Fin 8192 → ℝ}
    (hpoint : ∀ i, charge i ≤ ledger i + routeBSeedUniformAllowance3031 i)
    (hledger : (∑ i : Fin 8192, ledger i) ≤ (1999999000 : ℝ)) :
    (∑ i : Fin 8192, charge i) < (2000000000 : ℝ) := by
  apply routeBSeedLedgerAggregate_with_allowance3031 hpoint hledger
  · rw [routeBSeedUniformAllowance_sum3031]
    norm_num
  · norm_num

end ConnesWeilRH.Dev
