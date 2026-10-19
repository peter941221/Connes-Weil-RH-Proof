import ConnesWeilRH.Dev.C1RouteBSeedLedgerAllowanceContract3031
import ConnesWeilRH.Dev.C1RouteBSeedD4D7Aggregate3042

namespace ConnesWeilRH.Dev

noncomputable section

def routeBSeedUniformAllowance3071 : Fin 8192 → ℝ := fun _ =>
  (2 : ℝ) / 10 ^ 10

theorem routeBSeedUniformAllowance_sum3071 :
    (∑ i : Fin 8192, routeBSeedUniformAllowance3071 i) =
      (8192 : ℝ) * ((2 : ℝ) / 10 ^ 10) := by
  simp [routeBSeedUniformAllowance3071, div_eq_mul_inv]

theorem routeBSeedLedger_order4_target3071
    {charge ledger : Fin 8192 → ℝ}
    (hpoint : ∀ i, charge i ≤ ledger i + routeBSeedUniformAllowance3071 i)
    (hledger : (∑ i : Fin 8192, ledger i) ≤ routeBSeedD4Aggregate3042) :
    (∑ i : Fin 8192, charge i) < (1500 : ℝ) := by
  have haggregate : routeBSeedD4Aggregate3042 < 1401 := by
    norm_num [routeBSeedD4Aggregate3042]
  refine routeBSeedLedgerAggregate_with_allowance3031
    (aggregate := routeBSeedD4Aggregate3042) (margin := 1) (target := 1500)
    hpoint hledger ?_ ?_
  · rw [routeBSeedUniformAllowance_sum3071]
    norm_num
  · linarith

theorem routeBSeedLedger_order7_target3071
    {charge ledger : Fin 8192 → ℝ}
    (hpoint : ∀ i, charge i ≤ ledger i + routeBSeedUniformAllowance3071 i)
    (hledger : (∑ i : Fin 8192, ledger i) ≤ routeBSeedD7Aggregate3042) :
    (∑ i : Fin 8192, charge i) < (2000000000 : ℝ) := by
  have haggregate : routeBSeedD7Aggregate3042 < 356408391 := by
    norm_num [routeBSeedD7Aggregate3042]
  refine routeBSeedLedgerAggregate_with_allowance3031
    (aggregate := routeBSeedD7Aggregate3042) (margin := 1)
    (target := 2000000000) hpoint hledger ?_ ?_
  · rw [routeBSeedUniformAllowance_sum3071]
    norm_num
  · linarith

end
end ConnesWeilRH.Dev
