import ConnesWeilRH.Dev.C1RouteAOwnerWeightedIntervalIntegrable3206
import ConnesWeilRH.Dev.C1RouteARepairedOwnerCorrectionM02680
import ConnesWeilRH.Dev.C1RouteACorrectionCaptureParameters2584
import ConnesWeilRH.Dev.C1RouteATaylor6IntegralBridge3197

namespace ConnesWeilRH.Dev

open MeasureTheory
open scoped BigOperators ContDiff
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

theorem record2680_weightedExternal_contDiff3208 (sigma : ℝ) :
    ContDiff ℝ 6 (weightedExternal3201 sigma record2680CorrectionCoefficient
      capturedModulations2584) := by
  rw [weightedExternal3201_eq_weightedPhysical2539_re]
  exact (Complex.reCLM.contDiff.comp
    (weightedPhysical2539_contDiff sigma record2680CorrectionCoefficient
      capturedModulations2584)).of_le (by decide)

theorem intervalIntegral_record2680_cell_upper3208
    {left right center valueUpper secondUpper fourthUpper sixthBound : ℝ}
    (horder : left < right)
    (hcenter : center = (left + right) / 2)
    (hvalue : weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
        capturedModulations2584 center ≤ valueUpper)
    (hsecond : iteratedDerivWithin 2
        (weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
          capturedModulations2584) (Set.Icc left right) center ≤ secondUpper)
    (hfourth : iteratedDerivWithin 4
        (weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
          capturedModulations2584) (Set.Icc left right) center ≤ fourthUpper)
    (hderiv : ∀ coordinate,
      ‖iteratedDeriv 6
        (weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
          capturedModulations2584) coordinate‖ ≤ sixthBound)
    (hsixthBound : 0 ≤ sixthBound) :
    (∫ position in left..right,
      weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
        capturedModulations2584 position) ≤
      (right - left) * valueUpper +
        (right - left) ^ 3 * secondUpper / 24 +
        (right - left) ^ 5 * fourthUpper / 1920 +
        (right - left) ^ 7 * sixthBound / 322560 := by
  have hfunction := weightedExternal3201_intervalIntegrable
    (-1 / 2) record2680CorrectionCoefficient capturedModulations2584 left right
  have hTaylor := intervalIntegral_taylor6_upper_from_global3197
    (function := weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
      capturedModulations2584)
    horder hcenter (record2680_weightedExternal_contDiff3208 (-1 / 2)) hderiv
    hsixthBound hfunction
  have hstep : 0 ≤ right - left := le_of_lt (sub_pos.mpr horder)
  calc
    (∫ position in left..right,
        weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
          capturedModulations2584 position) ≤
        (right - left) * weightedExternal3201 (-1 / 2)
            record2680CorrectionCoefficient capturedModulations2584 center +
          (right - left) ^ 3 * iteratedDerivWithin 2
            (weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
              capturedModulations2584) (Set.Icc left right) center / 24 +
          (right - left) ^ 5 * iteratedDerivWithin 4
            (weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
              capturedModulations2584) (Set.Icc left right) center / 1920 +
          (right - left) ^ 7 * sixthBound / 322560 := hTaylor
    _ ≤ (right - left) * valueUpper +
          (right - left) ^ 3 * secondUpper / 24 +
          (right - left) ^ 5 * fourthUpper / 1920 +
          (right - left) ^ 7 * sixthBound / 322560 := by
      gcongr

end ConnesWeilRH.Dev
