import ConnesWeilRH.Dev.C1RouteATaylor6Remainder3194
import Mathlib.Analysis.Calculus.Taylor

namespace ConnesWeilRH.Dev

theorem taylor5_upper_on_cell3195
    {function : ℝ → ℝ} {left center right position sixthBound : ℝ}
    (hleft : left < center)
    (hright : center < right)
    (hsmooth : ContDiff ℝ 6 function)
    (hderiv : ∀ coordinate,
      ‖iteratedDeriv 6 function coordinate‖ ≤ sixthBound)
    (hsixthBound : 0 ≤ sixthBound)
    (hposition : position ∈ Set.Icc left right) :
    function position ≤
      taylorWithinEval function 5 (Set.Icc left right) center position +
        sixthBound * (position - center) ^ 6 / 720 := by
  rcases hposition with ⟨hposition_left, hposition_right⟩
  by_cases hpos : position = center
  · subst position
    simp
  have hpos_center : center ≠ position := Ne.symm hpos
  have hlocal_smooth : ContDiffOn ℝ 6 function (Set.uIcc center position) :=
    hsmooth.contDiffOn
  obtain ⟨witness, hwitness, hremainder⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv
      (x := position) (x₀ := center) (n := 5) hpos_center hlocal_smooth
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
    rw [hremainder', abs_div, abs_mul, abs_pow]
    have hfactor : 0 ≤ (position - center) ^ 6 := by positivity
    have hpow_abs : |position - center| ^ 6 = (position - center) ^ 6 := by
      rw [← abs_pow, abs_of_nonneg hfactor]
    rw [hpow_abs]
    norm_num
    have habs : |iteratedDeriv 6 function witness| ≤ sixthBound := by
      simpa [Real.norm_eq_abs] using hwitness_bound
    apply div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right habs hfactor) <;> norm_num
  have htayloreq :
      taylorWithinEval function 5 (Set.uIcc center position) center position =
        taylorWithinEval function 5 (Set.Icc left right) center position := by
    rcases le_total center position with hcp | hpc
    · rw [Set.uIcc_of_le hcp]
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
        (uniqueDiffOn_Icc (lt_of_le_of_ne hcp hpos_center))
        hcont ⟨le_rfl, hcp⟩]
      rw [iteratedDerivWithin_eq_iteratedDeriv
        (uniqueDiffOn_Icc (hleft.trans hright))
        hcont ⟨hleft.le, hright.le⟩]
    · have hpc' : position ≤ center := hpc
      rw [Set.uIcc_of_ge hpc']
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
        (uniqueDiffOn_Icc (lt_of_le_of_ne hpc' hpos))
        hcont ⟨hpc', le_rfl⟩]
      rw [iteratedDerivWithin_eq_iteratedDeriv
        (uniqueDiffOn_Icc (hleft.trans hright))
        hcont ⟨hleft.le, hright.le⟩]
  rw [htayloreq] at hbound'
  have hupper := (le_abs_self
    (function position - taylorWithinEval function 5
      (Set.Icc left right) center position)).trans hbound'
  have hnonneg : 0 ≤ sixthBound * (position - center) ^ 6 / 720 := by
    positivity
  linarith

end ConnesWeilRH.Dev
