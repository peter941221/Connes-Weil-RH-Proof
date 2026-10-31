import ConnesWeilRH.Dev.C1RouteAConcreteOwnerAggregateWithRightBand3230
import ConnesWeilRH.Dev.C1RouteAWeightedTaxiBallBridge3241

namespace ConnesWeilRH.Dev

open MeasureTheory
open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

noncomputable def record2680WeightedMiddlePointAwareValueUpper3240
    (valueUpper : ℕ → ℝ) (index : ℕ) : ℝ :=
  if index = 17168 then
    record2680MiddlePointWeightedAggregateBall3239.center.re +
      record2680MiddlePointWeightedAggregateBall3239.radius
  else
    record2680RightBandAwareValueUpper3230 valueUpper index

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem intervalIntegral_record2680_40960_aggregate_upper_with_weighted_middle_point3240
    {valueUpper : ℕ → ℝ}
    (hvalue : ∀ index, index < 40960 →
      index ≠ 0 → index ≠ 40956 → index ≠ 40957 → index ≠ 40958 →
      index ≠ 40959 → index ≠ 17168 →
      weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
        capturedModulations2584 (record2680Center3212 index) ≤ valueUpper index) :
    (∫ position in (-diagnosticRadius3201)..diagnosticRadius3201,
      weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
        capturedModulations2584 position) ≤
      Finset.sum (Finset.range 40960)
        (record2680CellUpper3209 record2680Grid3212
          (record2680WeightedMiddlePointAwareValueUpper3240 valueUpper)
          record2680CellSecondBound3224 record2680CellFourthBound3224
          record2680UniformSixthBound3220) := by
  refine intervalIntegral_record2680_40960_aggregate_upper_with_right_band3230
    (valueUpper := record2680WeightedMiddlePointAwareValueUpper3240 valueUpper) ?_
  intro index hindex hzero h56 h57 h58 hend
  unfold record2680WeightedMiddlePointAwareValueUpper3240
  by_cases hmid : index = 17168
  · simp [hmid]
    exact record2680_middle_point_weighted_value_upper_via_bridge3241
  · simp [record2680RightBandAwareValueUpper3230, hzero, h56, h57, h58,
      hend, hmid]
    exact hvalue index hindex hzero h56 h57 h58 hend hmid

end ConnesWeilRH.Dev
