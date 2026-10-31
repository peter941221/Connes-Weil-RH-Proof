import ConnesWeilRH.Dev.C1RouteAConcreteOwnerUniformSixth3220
import ConnesWeilRH.Dev.C1RouteAConcreteOwner40960AggregateUpper3213

namespace ConnesWeilRH.Dev

open MeasureTheory
open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

theorem intervalIntegral_record2680_40960_aggregate_upper_with_uniform_sixth3221
    {valueUpper secondUpper fourthUpper : ℕ → ℝ}
    (hvalue : ∀ index < 40960,
      weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
        capturedModulations2584 (record2680Center3212 index) ≤ valueUpper index)
    (hsecond : ∀ index < 40960,
      iteratedDeriv 2
        (weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
          capturedModulations2584) (record2680Center3212 index) ≤ secondUpper index)
    (hfourth : ∀ index < 40960,
      iteratedDeriv 4
        (weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
          capturedModulations2584) (record2680Center3212 index) ≤ fourthUpper index) :
    (∫ position in (-diagnosticRadius3201)..diagnosticRadius3201,
      weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
        capturedModulations2584 position) ≤
      Finset.sum (Finset.range 40960)
        (record2680CellUpper3209 record2680Grid3212 valueUpper secondUpper fourthUpper
          record2680UniformSixthBound3220) := by
  apply intervalIntegral_record2680_40960_global_aggregate_upper3213
    (valueUpper := valueUpper) (secondUpper := secondUpper)
    (fourthUpper := fourthUpper) (sixthBound := record2680UniformSixthBound3220)
  · exact hvalue
  · exact hsecond
  · exact hfourth
  · intro index hindex coordinate
    exact record2680_uniform_sixth_array_bound3220 hindex coordinate
  · intro index hindex
    exact record2680_uniform_sixth_bound_nonneg3220 index

end ConnesWeilRH.Dev
