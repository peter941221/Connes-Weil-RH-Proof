import ConnesWeilRH.Dev.C1RouteARationalPhysicalTermSignedBudget3412
import ConnesWeilRH.Dev.C1RouteAConcreteOwnerCellLocalJets3224

namespace ConnesWeilRH.Dev

open scoped BigOperators

/-
Record 3414 is the cell-consumer interface for the signed second-derivative
route. Family 4 is discharged by 3412; the remaining family producers stay
explicit so this theorem cannot hide an incomplete aggregate certificate.
-/
def signedCellFamilyCertificate3414 (familyUpper : Fin 30 → ℝ) : Fin 30 → ℝ :=
  fun family => if family = 4 then 1 else familyUpper family

theorem record2680_cell_second_bound_signed3414
    (familyUpper : Fin 30 → ℝ)
    (hfamily4 :
      (record2680CorrectionCoefficient 4 *
        weightedUnitJet2539 2 (-1 / 2) capturedModulations2584 4
          (record2680Center3212 1)).re ≤ 1)
    (hrest : ∀ family : Fin 30, family ≠ 4 →
      (record2680CorrectionCoefficient family *
        weightedUnitJet2539 2 (-1 / 2) capturedModulations2584 family
          (record2680Center3212 1)).re ≤ familyUpper family) :
    iteratedDeriv 2
      (weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
        capturedModulations2584) (record2680Center3212 1) ≤
      ∑ family : Fin 30, signedCellFamilyCertificate3414 familyUpper family := by
  rw [weightedExternal3201_eq_weightedPhysical2539_re]
  rw [iteratedDeriv_re_eq_re_iteratedDeriv3220
    (weightedPhysical2539 (-1 / 2) record2680CorrectionCoefficient
      capturedModulations2584) 2 (record2680Center3212 1)
    (weightedPhysical2539_contDiff (-1 / 2) record2680CorrectionCoefficient
      capturedModulations2584)]
  rw [weightedPhysical2539_iteratedDeriv]
  change (∑ family : Fin 30,
      (record2680CorrectionCoefficient family *
        weightedUnitJet2539 2 (-1 / 2) capturedModulations2584 family
          (record2680Center3212 1)).re) ≤ _
  apply Finset.sum_le_sum
  intro family hmem
  by_cases hfamily : family = 4
  · subst hfamily
    simpa [signedCellFamilyCertificate3414] using hfamily4
  · simpa [signedCellFamilyCertificate3414, hfamily] using hrest family hfamily

theorem record2680_cell_second_bound_signed3414_from3412
    (familyUpper : Fin 30 → ℝ)
    (hrest : ∀ family : Fin 30, family ≠ 4 →
      (record2680CorrectionCoefficient family *
        weightedUnitJet2539 2 (-1 / 2) capturedModulations2584 family
          (record2680Center3212 1)).re ≤ familyUpper family) :
    iteratedDeriv 2
      (weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
        capturedModulations2584) (record2680Center3212 1) ≤
      ∑ family : Fin 30, signedCellFamilyCertificate3414 familyUpper family := by
  apply record2680_cell_second_bound_signed3414 familyUpper
  · have hmem4 : (ratWeightedPhysicalTermRect3310 2 1 4).Mem
        (record2680CorrectionCoefficient 4 *
          weightedUnitJet2539 2 (-1 / 2) capturedModulations2584 4
            (record2680Center3212 1)) := by
      apply RatRect3276.mem_mul
      · exact ratCoefficientRect_mem3282 4
      · exact ratWeightedUnitJetSumRect_mem3310 (by norm_num) (by norm_num) 4
    have hrect :
        (record2680CorrectionCoefficient 4 *
          weightedUnitJet2539 2 (-1 / 2) capturedModulations2584 4
            (record2680Center3212 1)).re ≤
        ((ratWeightedPhysicalTermRect3310 2 1 4).reHi : ℝ) := hmem4.2.1
    exact hrect.trans (by exact_mod_cast
      ratWeightedPhysicalTermRect_cell1_order2_family4_reHi_le3412)
  · exact hrest

end ConnesWeilRH.Dev
