import ConnesWeilRH.Dev.C1RouteARationalSignedCellSecondBound3414
import ConnesWeilRH.Dev.C1RouteARationalTightCell3298
import ConnesWeilRH.Dev.C1RouteAConcreteOwnerGlobalJetBridge3210
import ConnesWeilRH.Dev.C1RouteAConcreteOwnerUniformSixth3220

namespace ConnesWeilRH.Dev

open MeasureTheory
open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

noncomputable def record2680CellUpperSigned3415
    (familyUpper : Fin 30 → ℝ) : ℝ :=
  (record2680Grid3212 2 - record2680Grid3212 1) *
      ratCellValueUpperTight3298 1 +
    (record2680Grid3212 2 - record2680Grid3212 1) ^ 3 *
      (∑ family : Fin 30, signedCellFamilyCertificate3414 familyUpper family) / 24 +
    (record2680Grid3212 2 - record2680Grid3212 1) ^ 5 *
      record2680CellFourthBound3224 1 / 1920 +
    (record2680Grid3212 2 - record2680Grid3212 1) ^ 7 *
      record2680UniformSixthBound3220 1 / 322560

theorem intervalIntegral_record2680_cell1_upper_signed3415
    (familyUpper : Fin 30 → ℝ)
    (hrest : ∀ family : Fin 30, family ≠ 4 →
      (record2680CorrectionCoefficient family *
        weightedUnitJet2539 2 (-1 / 2) capturedModulations2584 family
          (record2680Center3212 1)).re ≤ familyUpper family) :
    (∫ position in record2680Grid3212 1..record2680Grid3212 2,
      weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
        capturedModulations2584 position) ≤
      record2680CellUpperSigned3415 familyUpper := by
  have hsecond := record2680_cell_second_bound_signed3414_from3412
    familyUpper hrest
  have hvalue := ratCellValueUpperTight3298_spec (by norm_num : 1 < 40960)
  have hfourth := record2680_cell_fourth_bound3224 (by norm_num : 1 < 40960)
  have hderiv : ∀ coordinate,
      ‖iteratedDeriv 6
        (weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
          capturedModulations2584) coordinate‖ ≤
      record2680UniformSixthBound3220 1 := by
    intro coordinate
    exact record2680_uniform_sixth_array_bound3220 (by norm_num) coordinate
  have hsixth := record2680_uniform_sixth_bound_nonneg3220 1
  have hcell := intervalIntegral_record2680_cell_upper_from_global_bounds3210
    (left := record2680Grid3212 1) (right := record2680Grid3212 2)
    (center := record2680Center3212 1)
    (valueUpper := ratCellValueUpperTight3298 1)
    (secondUpper := ∑ family : Fin 30,
      signedCellFamilyCertificate3414 familyUpper family)
    (fourthUpper := record2680CellFourthBound3224 1)
    (sixthBound := record2680UniformSixthBound3220 1)
    (record2680_grid_order3212 (by norm_num))
    (record2680_center_midpoint3212 1)
    hvalue hsecond hfourth hderiv hsixth
  simpa [record2680CellUpperSigned3415] using hcell

theorem record2680CellUpperSigned3415_le_old_of_second_bound
    (familyUpper : Fin 30 → ℝ)
    (hsecond :
      (∑ family : Fin 30, signedCellFamilyCertificate3414 familyUpper family) ≤
        record2680CellSecondBound3224 1) :
    record2680CellUpperSigned3415 familyUpper ≤
      record2680CellUpper3209 record2680Grid3212 ratCellValueUpperTight3298
        record2680CellSecondBound3224 record2680CellFourthBound3224
        record2680UniformSixthBound3220 1 := by
  unfold record2680CellUpperSigned3415 record2680CellUpper3209
  have hstep : 0 ≤ record2680Grid3212 2 - record2680Grid3212 1 := by
    norm_num [record2680Grid3212, diagnosticRadius3201]
  have hstep3 : 0 ≤ (record2680Grid3212 2 - record2680Grid3212 1) ^ 3 := by
    positivity
  have hcoef : 0 ≤ (record2680Grid3212 2 - record2680Grid3212 1) ^ 3 / 24 := by
    positivity
  gcongr

end ConnesWeilRH.Dev
