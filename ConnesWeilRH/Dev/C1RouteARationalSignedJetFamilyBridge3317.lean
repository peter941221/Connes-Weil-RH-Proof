import ConnesWeilRH.Dev.C1RouteARationalSignedJetRect3310

namespace ConnesWeilRH.Dev

open scoped BigOperators

theorem ratWeightedPhysicalRect3310_reHi_eq_family_sum
    (order cell : ℕ) :
    (ratWeightedPhysicalRect3310 order cell).reHi =
      ∑ family : Fin 30,
        (ratWeightedPhysicalTermRect3310 order cell family).reHi := by
  simp [ratWeightedPhysicalRect3310, RatRect3276.sumFinset]

theorem ratWeightedPhysicalBlockRect3310_reHi_eq_cell_sum
    (order block : ℕ) :
    (ratWeightedPhysicalBlockRect3310 order block).reHi =
      ∑ offset ∈ Finset.range 256,
        (ratWeightedPhysicalRect3310 order (block * 256 + offset)).reHi := by
  simp [ratWeightedPhysicalBlockRect3310, RatRect3276.sumFinset]

theorem ratWeightedPhysicalBlockRect3310_reHi_eq_family_cell_sum
    (order block : ℕ) :
    (ratWeightedPhysicalBlockRect3310 order block).reHi =
      ∑ offset ∈ Finset.range 256,
        ∑ family : Fin 30,
          (ratWeightedPhysicalTermRect3310 order (block * 256 + offset) family).reHi := by
  rw [ratWeightedPhysicalBlockRect3310_reHi_eq_cell_sum]
  apply Finset.sum_congr rfl
  intro offset hoff
  rw [ratWeightedPhysicalRect3310_reHi_eq_family_sum]

end ConnesWeilRH.Dev
