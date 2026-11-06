import ConnesWeilRH.Dev.C1RouteARationalPhysicalTermSignedBudget3412
import ConnesWeilRH.Dev.C1RouteARationalSignedJetFamilyBridge3317

namespace ConnesWeilRH.Dev

open scoped BigOperators

/-
Record 3413 exposes the first composable consumer for the 3412 local term.
At cell 1, family 4 is discharged by the signed physical-term bound `<= 1`.
The other family endpoints remain explicit certificate premises; this theorem
does not claim a complete family aggregate or block certificate.
-/
theorem ratWeightedPhysicalRect3310_cell1_reHi_le_of_partial_family_certificate3413
    (cert : Fin 30 → ℚ) (aggregateUpper : ℚ)
    (hcert : ∀ family : Fin 30, family ≠ 4 →
      (ratWeightedPhysicalTermRect3310 2 1 family).reHi ≤ cert family)
    (hfamily4 : 1 ≤ cert 4)
    (haggregate : (∑ family : Fin 30, cert family : ℚ) ≤ aggregateUpper) :
    (ratWeightedPhysicalRect3310 2 1).reHi ≤ aggregateUpper := by
  rw [ratWeightedPhysicalRect3310_reHi_eq_family_sum]
  calc
    ∑ family : Fin 30, (ratWeightedPhysicalTermRect3310 2 1 family).reHi ≤
        ∑ family : Fin 30, cert family := by
      apply Finset.sum_le_sum
      intro family hmem
      by_cases hfamily : family = 4
      · subst hfamily
        exact le_trans
          ratWeightedPhysicalTermRect_cell1_order2_family4_reHi_le3412
          hfamily4
      · exact hcert family hfamily
    _ ≤ aggregateUpper := haggregate

end ConnesWeilRH.Dev
