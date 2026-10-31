import ConnesWeilRH.Dev.C1RouteAConcreteOwnerAggregateWithCellLocalJets3225
import ConnesWeilRH.Dev.C1RouteAConcreteOwnerOuterValue3226
import ConnesWeilRH.Dev.C1RouteAConcreteOwnerPhaseScaling3218

namespace ConnesWeilRH.Dev

open MeasureTheory
open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

noncomputable def record2680EndpointAwareValueUpper3227
    (valueUpper : ℕ → ℝ) (index : ℕ) : ℝ :=
  if index = 0 then 0 else if index = 40959 then 0 else valueUpper index

theorem intervalIntegral_record2680_40960_aggregate_upper_with_endpoint_values3227
    {valueUpper : ℕ → ℝ}
    (hvalue : ∀ index, 0 < index → index < 40959 →
      weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
        capturedModulations2584 (record2680Center3212 index) ≤ valueUpper index) :
    (∫ position in (-diagnosticRadius3201)..diagnosticRadius3201,
      weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
        capturedModulations2584 position) ≤
      Finset.sum (Finset.range 40960)
        (record2680CellUpper3209 record2680Grid3212
          (record2680EndpointAwareValueUpper3227 valueUpper)
          record2680CellSecondBound3224 record2680CellFourthBound3224
          record2680UniformSixthBound3220) := by
  apply intervalIntegral_record2680_40960_aggregate_upper_with_cell_local_jets3225
  intro index hindex
  unfold record2680EndpointAwareValueUpper3227
  by_cases hzero : index = 0
  · simp [hzero]
    exact record2680_first_center_weighted_value_upper3218
  by_cases hend : index = 40959
  · simp [hzero, hend]
    exact record2680_last_center_weighted_value_upper3226
  · simp [hzero, hend]
    exact hvalue index (by omega) (by omega)

end ConnesWeilRH.Dev
