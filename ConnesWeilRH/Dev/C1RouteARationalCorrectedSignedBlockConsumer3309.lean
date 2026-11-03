import ConnesWeilRH.Dev.C1RouteARationalCorrectedSignedBlockManifest3309
import ConnesWeilRH.Dev.C1RouteARationalTightSignedBlockConsumer3305
import ConnesWeilRH.Dev.C1RouteASignedRealJetProvider3306
import ConnesWeilRH.Dev.C1RouteAConcreteOwnerUniformSixth3220

namespace ConnesWeilRH.Dev

open MeasureTheory
open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

/-
Record 3309 is the corrected signed-real block consumer.

The endpoint remains the tight 3298 endpoint. The second and fourth rows are
the signed-real 3306 provider, while the sixth row remains the uniform 3220
norm bound. The only block-level premises are the 160 explicit hblock
inequalities against the new outward-rounded manifest.
-/

noncomputable def routeACorrectedSignedBlockUpper3309Real (block : ℕ) : ℝ :=
  if hblock : block < 160 then
    (routeACorrectedSignedBlockUpper3309 ⟨block, hblock⟩ : ℝ)
  else
    0

theorem routeACorrectedSignedBlockUpper3309Real_eq
    {block : ℕ} (hblock : block < 160) :
    routeACorrectedSignedBlockUpper3309Real block =
      (routeACorrectedSignedBlockUpper3309 ⟨block, hblock⟩ : ℝ) := by
  simp [routeACorrectedSignedBlockUpper3309Real, hblock]

theorem routeACorrectedSignedBlockUpper3309Real_sum_eq :
    Finset.sum (Finset.range 160) routeACorrectedSignedBlockUpper3309Real =
      ∑ block : Fin 160, (routeACorrectedSignedBlockUpper3309 block : ℝ) := by
  calc
    Finset.sum (Finset.range 160) routeACorrectedSignedBlockUpper3309Real =
        ∑ block : Fin 160, routeACorrectedSignedBlockUpper3309Real (block : ℕ) := by
          symm
          exact Fin.sum_univ_eq_sum_range routeACorrectedSignedBlockUpper3309Real 160
    _ = ∑ block : Fin 160, (routeACorrectedSignedBlockUpper3309 block : ℝ) := by
      apply Finset.sum_congr rfl
      intro block hmem
      exact routeACorrectedSignedBlockUpper3309Real_eq block.isLt

theorem routeACorrectedSignedBlockUpper3309Real_sum_lt_zero :
    Finset.sum (Finset.range 160) routeACorrectedSignedBlockUpper3309Real < 0 := by
  rw [routeACorrectedSignedBlockUpper3309Real_sum_eq]
  exact routeACorrectedSignedBlockUpper3309_real_sum_lt_zero

theorem intervalIntegral_record2680_40960_strict_upper_of_tight_signed_block_manifest3309
    (hblock : ∀ block < 160,
      Finset.sum (Finset.range 256) (fun offset =>
        record2680CellUpper3209 record2680Grid3212 ratCellValueUpperTight3298
          record2680SignedRealSecondUpper3306 record2680SignedRealFourthUpper3306
          record2680UniformSixthBound3220 (block * 256 + offset)) ≤
        routeACorrectedSignedBlockUpper3309Real block) :
    (∫ position in (-diagnosticRadius3201)..diagnosticRadius3201,
      weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
        capturedModulations2584 position) < 0 := by
  apply intervalIntegral_record2680_40960_strict_upper_of_tight_signed_block_manifest3305
  · intro index hindex
    exact record2680_signed_real_second_bound3306 hindex
  · intro index hindex
    exact record2680_signed_real_fourth_bound3306 hindex
  · intro index hindex coordinate
    exact record2680_uniform_sixth_array_bound3220 hindex coordinate
  · intro index hindex
    exact record2680_uniform_sixth_bound_nonneg3220 index
  · exact hblock
  · exact routeACorrectedSignedBlockUpper3309Real_sum_lt_zero

end ConnesWeilRH.Dev
