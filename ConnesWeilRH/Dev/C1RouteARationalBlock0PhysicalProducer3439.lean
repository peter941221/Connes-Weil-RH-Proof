import ConnesWeilRH.Dev.C1RouteARationalSignedCellAggregate3433
import ConnesWeilRH.Dev.C1RouteARationalSignedJetRect3310
import ConnesWeilRH.Dev.C1RouteAConcreteOwnerAggregateUpper3209

namespace ConnesWeilRH.Dev

open MeasureTheory
open scoped BigOperators

noncomputable def record2680RationalSecondUpper3439 (index : ℕ) : ℝ :=
  if index = 1 then
    (1 / 100 : ℝ)
  else
    (ratWeightedPhysicalRect3310 2 index).reHi

noncomputable def record2680RationalFourthUpper3439 (index : ℕ) : ℝ :=
  (ratWeightedPhysicalRect3310 4 index).reHi

theorem record2680_rational_physical_derivative_bound3439
    {order index : ℕ} (horder : order ≤ 6) (hindex : index < 40960) :
    iteratedDeriv order
        (weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
          capturedModulations2584) (record2680Center3212 index) ≤
      (ratWeightedPhysicalRect3310 order index).reHi := by
  have hmem := ratWeightedPhysicalRect_mem3310 horder hindex
  have hrect := hmem.2.1
  rw [weightedExternal3201_eq_weightedPhysical2539_re]
  rw [iteratedDeriv_re_eq_re_iteratedDeriv3220
    (weightedPhysical2539 (-1 / 2) record2680CorrectionCoefficient
      capturedModulations2584) order (record2680Center3212 index)
    (weightedPhysical2539_contDiff (-1 / 2) record2680CorrectionCoefficient
      capturedModulations2584)]
  exact hrect

theorem record2680_rational_second_bound3439
    {index : ℕ} (hindex : index < 40960) :
    iteratedDeriv 2
        (weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
          capturedModulations2584) (record2680Center3212 index) ≤
      record2680RationalSecondUpper3439 index := by
  by_cases hcell : index = 1
  · subst hcell
    simpa [record2680RationalSecondUpper3439] using
      record2680_cell1_second_bound_3433
  · simpa [record2680RationalSecondUpper3439, hcell] using
      record2680_rational_physical_derivative_bound3439 (order := 2)
        (by norm_num) hindex

theorem record2680_rational_fourth_bound3439
    {index : ℕ} (hindex : index < 40960) :
    iteratedDeriv 4
        (weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
          capturedModulations2584) (record2680Center3212 index) ≤
      record2680RationalFourthUpper3439 index := by
  simpa [record2680RationalFourthUpper3439] using
    record2680_rational_physical_derivative_bound3439 (order := 4)
      (by norm_num) hindex

theorem intervalIntegral_record2680_block0_physical_upper3439
    {sixthUpper : ℝ}
    (hsixth : ∀ coordinate,
      ‖iteratedDeriv 6
        (weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
          capturedModulations2584) coordinate‖ ≤ sixthUpper)
    (hsixth_nonneg : 0 ≤ sixthUpper) :
    (∫ position in record2680Grid3212 0..record2680Grid3212 256,
      weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
        capturedModulations2584 position) ≤
      Finset.sum (Finset.range 256)
        (record2680CellUpper3209 record2680Grid3212
          ratCellValueUpperTight3298 record2680RationalSecondUpper3439
          record2680RationalFourthUpper3439 (fun _ => sixthUpper)) := by
  apply intervalIntegral_record2680_aggregate_upper3209
    (cells := 256)
  · norm_num [record2680Grid3212, diagnosticRadius3201]
  · norm_num [record2680Grid3212, diagnosticRadius3201]
  · intro index hindex
    exact record2680_grid_order3212 (by omega)
  · intro index hindex
    exact record2680_center_midpoint3212 index
  · intro index hindex
    exact ratCellValueUpperTight3298_spec (by omega)
  · intro index hindex
    have hindex40960 : index < 40960 := by omega
    rw [record2680_iteratedDerivWithin_eq_global3210 2 (by norm_num)]
    · exact record2680_rational_second_bound3439 hindex40960
    · rw [record2680_center_midpoint3212 index]
      linarith [record2680_grid_order3212 (by omega : index < 40960)]
    · rw [record2680_center_midpoint3212 index]
      linarith [record2680_grid_order3212 (by omega : index < 40960)]
  · intro index hindex
    have hindex40960 : index < 40960 := by omega
    rw [record2680_iteratedDerivWithin_eq_global3210 4 (by norm_num)]
    · exact record2680_rational_fourth_bound3439 hindex40960
    · rw [record2680_center_midpoint3212 index]
      linarith [record2680_grid_order3212 (by omega : index < 40960)]
    · rw [record2680_center_midpoint3212 index]
      linarith [record2680_grid_order3212 (by omega : index < 40960)]
  · intro index hindex coordinate
    simpa using hsixth coordinate
  · intro index hindex
    exact hsixth_nonneg

end ConnesWeilRH.Dev
