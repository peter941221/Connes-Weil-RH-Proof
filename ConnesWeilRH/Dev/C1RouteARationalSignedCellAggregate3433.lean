import ConnesWeilRH.Dev.C1RouteARationalCell1InactiveFamilies3432
import ConnesWeilRH.Dev.C1RouteARationalSignedCellUpper3431
import ConnesWeilRH.Dev.C1RouteARationalPhysicalTermTightEndpoint3429
import ConnesWeilRH.Dev.C1RouteARationalTightCell3298
import ConnesWeilRH.Dev.C1RouteAConcreteOwnerGlobalJetBridge3210
import ConnesWeilRH.Dev.C1RouteAConcreteOwnerUniformSixth3220

namespace ConnesWeilRH.Dev

open MeasureTheory
open scoped BigOperators

theorem ratWeightedPhysicalRect3310_cell1_reHi_le3433 :
    (ratWeightedPhysicalRect3310 2 1).reHi ≤ 1 / 100 := by
  rw [ratWeightedPhysicalRect3310_cell1_eq_family4_3432]
  exact ratWeightedPhysicalTermRect_cell1_order2_family4_reHi_le3429

theorem record2680_cell1_second_bound_3433 :
    iteratedDeriv 2
      (weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
        capturedModulations2584) (record2680Center3212 1) ≤
      (1 / 100 : ℝ) := by
  have hmem := ratWeightedPhysicalRect_mem3310
    (order := 2) (cell := 1)
    (horder := by norm_num) (hcell := by norm_num)
  have hrect := hmem.2.1
  rw [weightedPhysical2539_iteratedDeriv] at hrect
  change (∑ family : Fin 30,
      (record2680CorrectionCoefficient family *
        weightedUnitJet2539 2 (-1 / 2) capturedModulations2584 family
          (record2680Center3212 1)).re) ≤
    ((ratWeightedPhysicalRect3310 2 1).reHi : ℝ) at hrect
  have hq := ratWeightedPhysicalRect3310_cell1_reHi_le3433
  have hqR0 : ((ratWeightedPhysicalRect3310 2 1).reHi : ℝ) ≤
      ((1 / 100 : ℚ) : ℝ) := by
    exact_mod_cast hq
  have hqR : ((ratWeightedPhysicalRect3310 2 1).reHi : ℝ) ≤
      (1 / 100 : ℝ) := by
    norm_num at hqR0 ⊢
    exact hqR0
  have hderiv := hrect
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
          (record2680Center3212 1)).re) ≤
    (1 / 100 : ℝ)
  exact hrect.trans hqR

noncomputable def record2680CellUpperSigned3433 : ℝ :=
  (record2680Grid3212 2 - record2680Grid3212 1) *
      ratCellValueUpperTight3298 1 +
    (record2680Grid3212 2 - record2680Grid3212 1) ^ 3 *
      (1 / 100 : ℝ) / 24 +
    (record2680Grid3212 2 - record2680Grid3212 1) ^ 5 *
      record2680CellFourthBound3224 1 / 1920 +
    (record2680Grid3212 2 - record2680Grid3212 1) ^ 7 *
      record2680UniformSixthBound3220 1 / 322560

theorem intervalIntegral_record2680_cell1_upper_signed3433 :
    (∫ position in record2680Grid3212 1..record2680Grid3212 2,
      weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
        capturedModulations2584 position) ≤
      record2680CellUpperSigned3433 := by
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
    (secondUpper := (1 / 100 : ℝ))
    (fourthUpper := record2680CellFourthBound3224 1)
    (sixthBound := record2680UniformSixthBound3220 1)
    (record2680_grid_order3212 (by norm_num))
    (record2680_center_midpoint3212 1)
    hvalue record2680_cell1_second_bound_3433 hfourth hderiv hsixth
  simpa [record2680CellUpperSigned3433] using hcell

theorem record2680CellUpperSigned3433_eq_zero_certificate3433 :
    record2680CellUpperSigned3433 =
      record2680CellUpperSigned3431 (fun _ => 0) := by
  funext
  unfold record2680CellUpperSigned3433 record2680CellUpperSigned3431
  norm_num [signedCellFamilyCertificate3430, Fin.sum_univ_succ]

end ConnesWeilRH.Dev
