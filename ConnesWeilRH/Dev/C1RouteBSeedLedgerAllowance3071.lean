import ConnesWeilRH.Dev.C1RouteBSeedLedgerAllowanceContract3031
import ConnesWeilRH.Dev.C1RouteBSeedD4D7Aggregate3042
import ConnesWeilRH.Dev.C1D4D7EndpointCharges2756

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Source.C1ExplicitSmoothSeed

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

theorem routeBSeedLedger_order4_full_target3071
    {charge ledger : Fin 8192 → ℝ}
    (hpoint : ∀ i, charge i ≤ ledger i + routeBSeedUniformAllowance3071 i)
    (hledger : (∑ i : Fin 8192, ledger i) ≤ routeBSeedD4Aggregate3042) :
    (∑ i : Fin 8192, charge i) +
      4 * (∫ x in (0 : ℝ)..(1 / 4096),
        ‖iteratedDeriv 4 Real.smoothTransition x‖) < (1500 : ℝ) := by
  have hcore : (∑ i : Fin 8192, charge i) ≤
      routeBSeedD4Aggregate3042 +
        (∑ i : Fin 8192, routeBSeedUniformAllowance3071 i) := by
    calc
      (∑ i : Fin 8192, charge i) ≤
          ∑ i : Fin 8192, (ledger i + routeBSeedUniformAllowance3071 i) :=
        Finset.sum_le_sum (fun i _ => hpoint i)
      _ = (∑ i : Fin 8192, ledger i) +
          (∑ i : Fin 8192, routeBSeedUniformAllowance3071 i) := by
        rw [Finset.sum_add_distrib]
      _ ≤ routeBSeedD4Aggregate3042 +
          (∑ i : Fin 8192, routeBSeedUniformAllowance3071 i) :=
        add_le_add_right hledger _
  have hallow : (∑ i : Fin 8192, routeBSeedUniformAllowance3071 i) < 1 := by
    rw [routeBSeedUniformAllowance_sum3071]
    norm_num
  have hendpoint :
      4 * (∫ x in (0 : ℝ)..(1 / 4096),
        ‖iteratedDeriv 4 Real.smoothTransition x‖) < 1 := by
    exact lt_of_le_of_lt d4d7_endpoint_integral_charges2756.1
      (lt_trans d4d7_endpoint_integral_charges_tiny2756.1 (by norm_num))
  have haggregate : routeBSeedD4Aggregate3042 < 1401 := by
    norm_num [routeBSeedD4Aggregate3042]
  linarith

theorem routeBSeedLedger_order7_full_target3071
    {charge ledger : Fin 8192 → ℝ}
    (hpoint : ∀ i, charge i ≤ ledger i + routeBSeedUniformAllowance3071 i)
    (hledger : (∑ i : Fin 8192, ledger i) ≤ routeBSeedD7Aggregate3042) :
    (∑ i : Fin 8192, charge i) +
      4 * (∫ x in (0 : ℝ)..(1 / 4096),
        ‖iteratedDeriv 7 Real.smoothTransition x‖) < (2000000000 : ℝ) := by
  have hcore : (∑ i : Fin 8192, charge i) ≤
      routeBSeedD7Aggregate3042 +
        (∑ i : Fin 8192, routeBSeedUniformAllowance3071 i) := by
    calc
      (∑ i : Fin 8192, charge i) ≤
          ∑ i : Fin 8192, (ledger i + routeBSeedUniformAllowance3071 i) :=
        Finset.sum_le_sum (fun i _ => hpoint i)
      _ = (∑ i : Fin 8192, ledger i) +
          (∑ i : Fin 8192, routeBSeedUniformAllowance3071 i) := by
        rw [Finset.sum_add_distrib]
      _ ≤ routeBSeedD7Aggregate3042 +
          (∑ i : Fin 8192, routeBSeedUniformAllowance3071 i) :=
        add_le_add_right hledger _
  have hallow : (∑ i : Fin 8192, routeBSeedUniformAllowance3071 i) < 1 := by
    rw [routeBSeedUniformAllowance_sum3071]
    norm_num
  have hendpoint :
      4 * (∫ x in (0 : ℝ)..(1 / 4096),
        ‖iteratedDeriv 7 Real.smoothTransition x‖) < 1 := by
    exact lt_of_le_of_lt d4d7_endpoint_integral_charges2756.2
      (lt_trans d4d7_endpoint_integral_charges_tiny2756.2 (by norm_num))
  have haggregate : routeBSeedD7Aggregate3042 < 356408391 := by
    norm_num [routeBSeedD7Aggregate3042]
  linarith

end
end ConnesWeilRH.Dev
