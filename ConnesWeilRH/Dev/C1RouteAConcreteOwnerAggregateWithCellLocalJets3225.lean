import ConnesWeilRH.Dev.C1RouteAConcreteOwnerCellLocalJets3224

namespace ConnesWeilRH.Dev

open MeasureTheory
open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

theorem intervalIntegral_record2680_40960_aggregate_upper_with_cell_local_jets3225
    {valueUpper : ℕ → ℝ}
    (hvalue : ∀ index < 40960,
      weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
        capturedModulations2584 (record2680Center3212 index) ≤ valueUpper index) :
    (∫ position in (-diagnosticRadius3201)..diagnosticRadius3201,
      weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
        capturedModulations2584 position) ≤
      Finset.sum (Finset.range 40960)
        (record2680CellUpper3209 record2680Grid3212 valueUpper
          record2680CellSecondBound3224 record2680CellFourthBound3224
          record2680UniformSixthBound3220) := by
  apply intervalIntegral_record2680_40960_global_aggregate_upper3213
    (valueUpper := valueUpper)
    (secondUpper := record2680CellSecondBound3224)
    (fourthUpper := record2680CellFourthBound3224)
    (sixthBound := record2680UniformSixthBound3220)
  · exact hvalue
  · intro index hindex
    exact record2680_cell_second_bound3224 hindex
  · intro index hindex
    exact record2680_cell_fourth_bound3224 hindex
  · intro index hindex coordinate
    exact record2680_uniform_sixth_array_bound3220 hindex coordinate
  · intro index hindex
    exact record2680_uniform_sixth_bound_nonneg3220 index

end ConnesWeilRH.Dev
