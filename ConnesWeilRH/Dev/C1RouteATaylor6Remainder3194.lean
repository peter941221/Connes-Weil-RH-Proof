import ConnesWeilRH.Dev.C1RouteATaylor6CellPanel3193
import Mathlib.Analysis.Calculus.Taylor

namespace ConnesWeilRH.Dev

open MeasureTheory

theorem taylor5_upper_on_right_half3194
    {function : ℝ → ℝ} {center right position sixthBound : ℝ}
    (horder : center ≤ right)
    (hsmooth : ContDiff ℝ 6 function)
    (hderiv : ∀ coordinate,
      ‖iteratedDeriv 6 function coordinate‖ ≤ sixthBound)
    (hsixthBound : 0 ≤ sixthBound)
    (hposition : position ∈ Set.Icc center right) :
    function position ≤
      taylorWithinEval function 5 (Set.Icc center right) center position +
        sixthBound * (position - center) ^ 6 / 720 := by
  rcases hposition with ⟨hcenter_position, hposition_right⟩
  by_cases hpos : position = center
  · subst position
    simp
  have hpos' : center ≠ position := Ne.symm hpos
  have hlocal_smooth : ContDiffOn ℝ 6 function (Set.uIcc center position) :=
    hsmooth.contDiffOn
  obtain ⟨witness, hwitness, hremainder⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv
      (x := position) (x₀ := center) (n := 5) hpos' hlocal_smooth
  have hwitness_bound : ‖iteratedDeriv 6 function witness‖ ≤ sixthBound :=
    hderiv witness
  have hremainder' :
      function position - taylorWithinEval function 5
          (Set.uIcc center position) center position =
        iteratedDeriv 6 function witness * (position - center) ^ 6 / 720 := by
    simpa [taylor_within_apply, Nat.factorial] using hremainder
  have hbound' :
      |function position - taylorWithinEval function 5
          (Set.uIcc center position) center position| ≤
        sixthBound * (position - center) ^ 6 / 720 := by
    rw [hremainder']
    rw [abs_div, abs_mul, abs_pow]
    have hfactor : 0 ≤ (position - center) ^ 6 := by positivity
    have hbase : 0 ≤ position - center := sub_nonneg.mpr hcenter_position
    rw [abs_of_nonneg hbase]
    norm_num
    have hfactorial : Nat.factorial 6 = 720 := by norm_num [Nat.factorial]
    have habs : |iteratedDeriv 6 function witness| ≤ sixthBound := by
      simpa [Real.norm_eq_abs] using hwitness_bound
    apply div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right habs hfactor) <;> norm_num
  have htayloreq :
      taylorWithinEval function 5 (Set.uIcc center position) center position =
        taylorWithinEval function 5 (Set.Icc center right) center position := by
    rw [Set.uIcc_of_le hcenter_position]
    rw [taylor_within_apply, taylor_within_apply]
    apply Finset.sum_congr rfl
    intro order horder'
    congr 1
    have horder_lt : order < 6 := Finset.mem_range.mp horder'
    have hcont6 : ContDiffAt ℝ 6 function center := hsmooth.contDiffAt
    have horder_le_nat : order ≤ 6 :=
      (Nat.le_of_lt horder_lt).trans (by norm_num)
    have horder_le : (order : WithTop ℕ∞) ≤ 6 := by
      exact_mod_cast horder_le_nat
    have hcont : ContDiffAt ℝ order function center :=
      hcont6.of_le horder_le
    rw [iteratedDerivWithin_eq_iteratedDeriv
      (uniqueDiffOn_Icc (lt_of_le_of_ne hcenter_position hpos'))
      hcont ⟨le_rfl, hcenter_position⟩]
    rw [iteratedDerivWithin_eq_iteratedDeriv
      (uniqueDiffOn_Icc (lt_of_lt_of_le
        (lt_of_le_of_ne hcenter_position hpos') hposition_right))
      hcont ⟨le_rfl, horder⟩]
  rw [htayloreq] at hbound'
  have hupper := (le_abs_self
    (function position - taylorWithinEval function 5
      (Set.Icc center right) center position)).trans hbound'
  have hnonneg : 0 ≤ sixthBound * (position - center) ^ 6 / 720 := by
    positivity
  linarith

end ConnesWeilRH.Dev
