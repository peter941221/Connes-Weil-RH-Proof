import ConnesWeilRH.Dev.C1RouteAConcreteOwnerCellUpper3208

namespace ConnesWeilRH.Dev

open MeasureTheory
open scoped BigOperators ContDiff
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

theorem record2680_iteratedDerivWithin_eq_global3210
    (order : ℕ) (horder : order ≤ 6)
    {left right center : ℝ}
    (hleft : left < center) (hright : center < right) :
    iteratedDerivWithin order
        (weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
          capturedModulations2584) (Set.Icc left right) center =
      iteratedDeriv order
        (weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
          capturedModulations2584) center := by
  apply iteratedDerivWithin_eq_iteratedDeriv
    (uniqueDiffOn_Icc (lt_trans hleft hright))
  · exact ((record2680_weightedExternal_contDiff3208 (-1 / 2)).of_le
      (by exact_mod_cast horder)).contDiffAt
  · exact ⟨le_of_lt hleft, le_of_lt hright⟩

theorem intervalIntegral_record2680_cell_upper_from_global_bounds3210
    {left right center valueUpper secondUpper fourthUpper sixthBound : ℝ}
    (horder : left < right)
    (hcenter : center = (left + right) / 2)
    (hvalue : weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
        capturedModulations2584 center ≤ valueUpper)
    (hsecond : iteratedDeriv 2
        (weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
          capturedModulations2584) center ≤ secondUpper)
    (hfourth : iteratedDeriv 4
        (weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
          capturedModulations2584) center ≤ fourthUpper)
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
  have hleft : left < center := by
    rw [hcenter]
    linarith
  have hright : center < right := by
    rw [hcenter]
    linarith
  apply intervalIntegral_record2680_cell_upper3208 horder hcenter hvalue
  · rw [record2680_iteratedDerivWithin_eq_global3210 2 (by norm_num) hleft hright]
    exact hsecond
  · rw [record2680_iteratedDerivWithin_eq_global3210 4 (by norm_num) hleft hright]
    exact hfourth
  · exact hderiv
  · exact hsixthBound

end ConnesWeilRH.Dev
