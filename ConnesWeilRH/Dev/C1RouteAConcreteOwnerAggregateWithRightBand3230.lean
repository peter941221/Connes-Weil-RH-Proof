import ConnesWeilRH.Dev.C1RouteAConcreteOwnerInteriorValue3229
import ConnesWeilRH.Dev.C1RouteAConcreteOwnerAggregateWithEndpointValues3227

namespace ConnesWeilRH.Dev

open MeasureTheory
open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

noncomputable def record2680RightBandAwareValueUpper3230
    (valueUpper : ℕ → ℝ) (index : ℕ) : ℝ :=
  if index = 0 then 0
  else if index = 40956 then 0
  else if index = 40957 then 0
  else if index = 40958 then 0
  else if index = 40959 then 0
  else valueUpper index

theorem intervalIntegral_record2680_40960_aggregate_upper_with_right_band3230
    {valueUpper : ℕ → ℝ}
    (hvalue : ∀ index, index < 40960 →
      index ≠ 0 → index ≠ 40956 → index ≠ 40957 → index ≠ 40958 → index ≠ 40959 →
      weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
        capturedModulations2584 (record2680Center3212 index) ≤ valueUpper index) :
    (∫ position in (-diagnosticRadius3201)..diagnosticRadius3201,
      weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
        capturedModulations2584 position) ≤
      Finset.sum (Finset.range 40960)
        (record2680CellUpper3209 record2680Grid3212
          (record2680RightBandAwareValueUpper3230 valueUpper)
          record2680CellSecondBound3224 record2680CellFourthBound3224
          record2680UniformSixthBound3220) := by
  apply intervalIntegral_record2680_40960_aggregate_upper_with_cell_local_jets3225
  intro index hindex
  unfold record2680RightBandAwareValueUpper3230
  by_cases hzero : index = 0
  · simp [hzero]
    exact record2680_first_center_weighted_value_upper3218
  by_cases h56 : index = 40956
  · simp [hzero, h56]
    exact record2680_40956_weighted_value_upper3229
  by_cases h57 : index = 40957
  · simp [hzero, h56, h57]
    exact record2680_40957_weighted_value_upper3229
  by_cases h58 : index = 40958
  · simp [hzero, h56, h57, h58]
    exact record2680_interior_center_weighted_value_upper3228
  by_cases hend : index = 40959
  · simp [hzero, h56, h57, h58, hend]
    exact record2680_last_center_weighted_value_upper3226
  simp [hzero, h56, h57, h58, hend]
  exact hvalue index hindex hzero h56 h57 h58 hend

end ConnesWeilRH.Dev
