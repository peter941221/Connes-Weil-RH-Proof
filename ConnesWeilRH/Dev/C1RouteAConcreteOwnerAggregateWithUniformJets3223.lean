import ConnesWeilRH.Dev.C1RouteAConcreteOwnerUniformJets3222
import ConnesWeilRH.Dev.C1RouteAConcreteOwnerAggregateWithUniformSixth3221

namespace ConnesWeilRH.Dev

open MeasureTheory
open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

theorem intervalIntegral_record2680_40960_aggregate_upper_with_uniform_jets3223
    {valueUpper : ℕ → ℝ}
    (hvalue : ∀ index < 40960,
      weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
        capturedModulations2584 (record2680Center3212 index) ≤ valueUpper index) :
    (∫ position in (-diagnosticRadius3201)..diagnosticRadius3201,
      weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
        capturedModulations2584 position) ≤
      Finset.sum (Finset.range 40960)
        (record2680CellUpper3209 record2680Grid3212 valueUpper
          record2680UniformSecondBound3222 record2680UniformFourthBound3222
          record2680UniformSixthBound3220) := by
  apply intervalIntegral_record2680_40960_aggregate_upper_with_uniform_sixth3221
    (valueUpper := valueUpper)
    (secondUpper := record2680UniformSecondBound3222)
    (fourthUpper := record2680UniformFourthBound3222)
  · exact hvalue
  · intro index hindex
    exact record2680_uniform_second_bound3222 hindex (record2680Center3212 index)
  · intro index hindex
    exact record2680_uniform_fourth_bound3222 hindex (record2680Center3212 index)

end ConnesWeilRH.Dev
