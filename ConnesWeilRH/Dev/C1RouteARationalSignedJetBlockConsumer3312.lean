import ConnesWeilRH.Dev.C1RouteARationalSignedJetBlockManifest3312
import ConnesWeilRH.Dev.C1RouteARationalTightSignedBlockConsumer3305
import ConnesWeilRH.Dev.C1RouteASignedRealJetProvider3306
import ConnesWeilRH.Dev.C1RouteAConcreteOwnerUniformSixth3220

namespace ConnesWeilRH.Dev

open MeasureTheory
open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

/-
Record 3312 is a conditional consumer boundary for a historical block
manifest. Its generating evaluator was not faithful to 3310; the constants
are not established upper bounds for the corresponding Lean expressions.

The manifest is an exact rational list whose total is proved negative. The
160 block dominance inequalities remain explicit premises here: the generator
has not been imported as an opaque theorem or certificate.
-/

noncomputable def routeASignedJetRectBlockUpper3312Real (block : ℕ) : ℝ :=
  if hblock : block < 160 then
    (routeASignedJetRectBlockUpper3312 ⟨block, hblock⟩ : ℝ)
  else
    0

theorem routeASignedJetRectBlockUpper3312Real_eq
    {block : ℕ} (hblock : block < 160) :
    routeASignedJetRectBlockUpper3312Real block =
      (routeASignedJetRectBlockUpper3312 ⟨block, hblock⟩ : ℝ) := by
  simp [routeASignedJetRectBlockUpper3312Real, hblock]

theorem routeASignedJetRectBlockUpper3312Real_sum_eq :
    Finset.sum (Finset.range 160) routeASignedJetRectBlockUpper3312Real =
      ∑ block : Fin 160, (routeASignedJetRectBlockUpper3312 block : ℝ) := by
  calc
    Finset.sum (Finset.range 160) routeASignedJetRectBlockUpper3312Real =
        ∑ block : Fin 160, routeASignedJetRectBlockUpper3312Real (block : ℕ) := by
          symm
          exact Fin.sum_univ_eq_sum_range routeASignedJetRectBlockUpper3312Real 160
    _ = ∑ block : Fin 160, (routeASignedJetRectBlockUpper3312 block : ℝ) := by
      apply Finset.sum_congr rfl
      intro block hmem
      exact routeASignedJetRectBlockUpper3312Real_eq block.isLt

theorem routeASignedJetRectBlockUpper3312Real_sum_lt_zero :
    Finset.sum (Finset.range 160) routeASignedJetRectBlockUpper3312Real < 0 := by
  rw [routeASignedJetRectBlockUpper3312Real_sum_eq]
  exact routeASignedJetRectBlockUpper3312_real_sum_lt_zero

theorem intervalIntegral_record2680_40960_strict_upper_of_signed_jet_block_manifest3312
    (hblock : ∀ block < 160,
      Finset.sum (Finset.range 256) (fun offset =>
        record2680CellUpper3209 record2680Grid3212 ratCellValueUpperTight3298
          record2680SignedRealSecondUpper3306 record2680SignedRealFourthUpper3306
          record2680UniformSixthBound3220 (block * 256 + offset)) ≤
        routeASignedJetRectBlockUpper3312Real block) :
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
  · exact routeASignedJetRectBlockUpper3312Real_sum_lt_zero

end ConnesWeilRH.Dev
