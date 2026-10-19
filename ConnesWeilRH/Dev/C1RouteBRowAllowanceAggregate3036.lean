import ConnesWeilRH.Dev.C1RouteBSeedLedgerAllowanceContract3031

namespace ConnesWeilRH.Dev

theorem routeBRowAllowance_sum_le_aggregate_margin3036
    {charge ledger allowance : Fin 8192 → ℝ}
    {aggregate margin : ℝ}
    (hrow : ∀ i, charge i ≤ ledger i + allowance i)
    (hledger : (∑ i : Fin 8192, ledger i) ≤ aggregate)
    (hallow : (∑ i : Fin 8192, allowance i) ≤ margin) :
    (∑ i : Fin 8192, charge i) ≤ aggregate + margin := by
  calc
    (∑ i : Fin 8192, charge i) ≤
        ∑ i : Fin 8192, (ledger i + allowance i) :=
      Finset.sum_le_sum (fun i _ => hrow i)
    _ = (∑ i : Fin 8192, ledger i) + (∑ i : Fin 8192, allowance i) := by
      rw [Finset.sum_add_distrib]
    _ ≤ aggregate + margin := add_le_add hledger hallow

end ConnesWeilRH.Dev
