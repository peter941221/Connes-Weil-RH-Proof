import ConnesWeilRH.Dev.C1RouteBSeedLedgerSoundnessContract3025
import Mathlib

namespace ConnesWeilRH.Dev

theorem routeBSeedLedgerAggregate_with_allowance3030
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

end ConnesWeilRH.Dev
