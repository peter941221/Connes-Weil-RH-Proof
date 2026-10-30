import ConnesWeilRH.Dev.C1RouteAConcreteOwnerGrid3212

namespace ConnesWeilRH.Dev

open MeasureTheory
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

theorem intervalIntegral_record2680_40960_global_aggregate_upper3213
    {valueUpper secondUpper fourthUpper sixthBound : ℕ → ℝ}
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
          capturedModulations2584) (record2680Center3212 index) ≤ fourthUpper index)
    (hderiv : ∀ index < 40960, ∀ coordinate,
      ‖iteratedDeriv 6
        (weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
          capturedModulations2584) coordinate‖ ≤ sixthBound index)
    (hsixthBound : ∀ index < 40960, 0 ≤ sixthBound index) :
    (∫ position in (-diagnosticRadius3201)..diagnosticRadius3201,
      weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
        capturedModulations2584 position) ≤
      Finset.sum (Finset.range 40960)
        (record2680CellUpper3209 record2680Grid3212 valueUpper secondUpper
          fourthUpper sixthBound) := by
  apply intervalIntegral_record2680_global_aggregate_upper3211
    (grid := record2680Grid3212) (center := record2680Center3212)
    (cells := 40960) record2680_grid_left3212 record2680_grid_right3212
  · intro index hindex
    exact record2680_grid_order3212 hindex
  · intro index hindex
    exact record2680_center_midpoint3212 index
  · exact hvalue
  · exact hsecond
  · exact hfourth
  · exact hderiv
  · exact hsixthBound

end ConnesWeilRH.Dev
