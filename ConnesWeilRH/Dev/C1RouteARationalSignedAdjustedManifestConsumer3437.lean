import ConnesWeilRH.Dev.C1RouteARationalBlockAdjustedMargin3436
import ConnesWeilRH.Dev.C1RouteARationalSignedCellAggregate3433
import ConnesWeilRH.Dev.C1RouteARationalTightSignedBlockConsumer3305
import ConnesWeilRH.Dev.C1RouteASignedRealJetProvider3306
import ConnesWeilRH.Dev.C1RouteAConcreteOwnerUniformSixth3220

namespace ConnesWeilRH.Dev

open MeasureTheory
open scoped BigOperators

noncomputable def record2680SignedRealSecondUpper3437 (index : ℕ) : ℝ :=
  if index = 1 then
    (1 / 100 : ℝ)
  else
    record2680SignedRealSecondUpper3306 index

noncomputable def record2680SignedRealFourthUpper3437 (index : ℕ) : ℝ :=
  record2680SignedRealFourthUpper3306 index

theorem record2680_signed_real_second_bound3437 {index : ℕ}
    (hindex : index < 40960) :
    iteratedDeriv 2
        (weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
          capturedModulations2584) (record2680Center3212 index) ≤
      record2680SignedRealSecondUpper3437 index := by
  by_cases hcell : index = 1
  · subst hcell
    simpa [record2680SignedRealSecondUpper3437] using
      record2680_cell1_second_bound_3433
  · simpa [record2680SignedRealSecondUpper3437, hcell] using
      record2680_signed_real_second_bound3306 hindex

theorem record2680_signed_real_fourth_bound3437 {index : ℕ}
    (hindex : index < 40960) :
    iteratedDeriv 4
        (weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
          capturedModulations2584) (record2680Center3212 index) ≤
      record2680SignedRealFourthUpper3437 index := by
  simpa [record2680SignedRealFourthUpper3437] using
    record2680_signed_real_fourth_bound3306 hindex

noncomputable def routeASignedJetRectBlockUpper3436Real (block : ℕ) : ℝ :=
  if hblock : block < 160 then
    (routeASignedJetRectBlockUpper3436 ⟨block, hblock⟩ : ℝ)
  else
    0

theorem routeASignedJetRectBlockUpper3436Real_sum_lt_zero :
    Finset.sum (Finset.range 160) routeASignedJetRectBlockUpper3436Real < 0 := by
  have hsum :
      Finset.sum (Finset.range 160) routeASignedJetRectBlockUpper3436Real =
        ∑ block : Fin 160, (routeASignedJetRectBlockUpper3436 block : ℝ) := by
    calc
      Finset.sum (Finset.range 160) routeASignedJetRectBlockUpper3436Real =
          ∑ block : Fin 160, routeASignedJetRectBlockUpper3436Real (block : ℕ) := by
            symm
            exact Fin.sum_univ_eq_sum_range routeASignedJetRectBlockUpper3436Real 160
      _ = ∑ block : Fin 160, (routeASignedJetRectBlockUpper3436 block : ℝ) := by
        apply Finset.sum_congr rfl
        intro block hmem
        simp [routeASignedJetRectBlockUpper3436Real, block.isLt]
  rw [hsum]
  exact_mod_cast routeASignedJetRectBlockUpper3436_sum_lt_zero

theorem intervalIntegral_record2680_40960_strict_upper_of_adjusted_manifest3437
    (hblock : ∀ block < 160,
      Finset.sum (Finset.range 256) (fun offset =>
        record2680CellUpper3209 record2680Grid3212 ratCellValueUpperTight3298
          record2680SignedRealSecondUpper3437
          record2680SignedRealFourthUpper3437
          record2680UniformSixthBound3220 (block * 256 + offset)) ≤
        routeASignedJetRectBlockUpper3436Real block) :
    (∫ position in (-diagnosticRadius3201)..diagnosticRadius3201,
      weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
        capturedModulations2584 position) < 0 := by
  apply intervalIntegral_record2680_40960_strict_upper_of_tight_signed_block_manifest3305
  · intro index hindex
    exact record2680_signed_real_second_bound3437 hindex
  · intro index hindex
    exact record2680_signed_real_fourth_bound3437 hindex
  · intro index hindex coordinate
    exact record2680_uniform_sixth_array_bound3220 hindex coordinate
  · intro index hindex
    exact record2680_uniform_sixth_bound_nonneg3220 index
  · exact hblock
  · exact routeASignedJetRectBlockUpper3436Real_sum_lt_zero

end ConnesWeilRH.Dev
