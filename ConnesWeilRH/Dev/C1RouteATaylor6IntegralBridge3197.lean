import ConnesWeilRH.Dev.C1RouteATaylor5Integral3196

namespace ConnesWeilRH.Dev

open MeasureTheory

theorem intervalIntegral_taylor6_upper_from_global3197
    {function : ℝ → ℝ} {left right center sixthBound : ℝ}
    (horder : left < right)
    (hcenter : center = (left + right) / 2)
    (hsmooth : ContDiff ℝ 6 function)
    (hderiv : ∀ coordinate,
      ‖iteratedDeriv 6 function coordinate‖ ≤ sixthBound)
    (hsixthBound : 0 ≤ sixthBound)
    (hfunction : IntervalIntegrable function volume left right) :
    (∫ position in left..right, function position) ≤
      (right - left) * function center +
        (right - left) ^ 3 * iteratedDerivWithin 2 function
          (Set.Icc left right) center / 24 +
        (right - left) ^ 5 * iteratedDerivWithin 4 function
          (Set.Icc left right) center / 1920 +
        (right - left) ^ 7 * sixthBound / 322560 := by
  have hleft : left < center := by
    rw [hcenter]
    linarith
  have hright : center < right := by
    rw [hcenter]
    linarith
  apply intervalIntegral_taylor5_upper_cancel_odd3196
    (function := function) (left := left) (right := right) (center := center)
    (value := function center)
    (first := derivWithin function (Set.Icc left right) center)
    (second := iteratedDerivWithin 2 function (Set.Icc left right) center)
    (third := iteratedDerivWithin 3 function (Set.Icc left right) center)
    (fourth := iteratedDerivWithin 4 function (Set.Icc left right) center)
    (fifth := iteratedDerivWithin 5 function (Set.Icc left right) center)
    (sixth := sixthBound) horder hcenter ?_ hfunction
  intro position hposition
  have hupper := taylor5_upper_on_cell3195
    (left := left) (center := center) (right := right)
    (position := position) (sixthBound := sixthBound)
    hleft hright hsmooth hderiv hsixthBound hposition
  rw [taylor_within_apply] at hupper
  convert hupper using 1 <;> simp [Finset.sum_range_succ, Nat.factorial, smul_eq_mul] <;> ring

end ConnesWeilRH.Dev
