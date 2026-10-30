import ConnesWeilRH.Dev.C1RouteAOwnerDerivativeBudget
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace ConnesWeilRH.Dev

open MeasureTheory

noncomputable def symmetricTaylor6Majorant3193
    (center value second fourth sixth position : ℝ) : ℝ :=
  value + second / 2 * (position - center) ^ 2 +
    fourth / 24 * (position - center) ^ 4 +
    sixth / 720 * (position - center) ^ 6

theorem intervalIntegral_symmetricTaylor6_upper3193
    {function : ℝ → ℝ} {left right center value second fourth sixth : ℝ}
    (horder : left < right)
    (hcenter : center = (left + right) / 2)
    (hpointwise : ∀ position ∈ Set.Icc left right,
      function position ≤
        symmetricTaylor6Majorant3193 center value second fourth sixth position)
    (hfunction : IntervalIntegrable function volume left right) :
    (∫ position in left..right, function position) ≤
      (right - left) * value +
        (right - left) ^ 3 * second / 24 +
        (right - left) ^ 5 * fourth / 1920 +
        (right - left) ^ 7 * sixth / 322560 := by
  let majorant := symmetricTaylor6Majorant3193 center value second fourth sixth
  have hmajorant : Continuous majorant := by
    change Continuous (fun position : ℝ =>
      value + second / 2 * (position - center) ^ 2 +
        fourth / 24 * (position - center) ^ 4 +
        sixth / 720 * (position - center) ^ 6)
    fun_prop
  have hmono := intervalIntegral.integral_mono_on horder.le hfunction
    (hmajorant.intervalIntegrable (μ := volume) left right) hpointwise
  refine hmono.trans_eq ?_
  have hwidth : 0 < right - left := sub_pos.mpr horder
  have hcenter' : left - center = -(right - left) / 2 := by
    rw [hcenter]
    ring
  have hcenter'' : right - center = (right - left) / 2 := by
    rw [hcenter]
    ring
  have hpow (power : ℕ) :
      (∫ position in left..right, (position - center) ^ power) =
        (((right - left) / 2) ^ (power + 1) -
          (-(right - left) / 2) ^ (power + 1)) / (power + 1) := by
    calc
      (∫ position in left..right, (position - center) ^ power) =
          ∫ position in left - center..right - center, position ^ power := by
        exact intervalIntegral.integral_comp_sub_right
          (f := fun position : ℝ => position ^ power) center
      _ = (((right - left) / 2) ^ (power + 1) -
          (-(right - left) / 2) ^ (power + 1)) / (power + 1) := by
        rw [integral_pow, hcenter', hcenter'']
  have hterm (coefficient : ℝ) (power : ℕ) :
      IntervalIntegrable (fun position : ℝ =>
        coefficient * (position - center) ^ power) volume left right := by
    exact (continuous_const.mul ((continuous_id.sub continuous_const).pow power))
      |>.intervalIntegrable left right
  have hzero : IntervalIntegrable (fun _ : ℝ => value) volume left right :=
    intervalIntegrable_const
  have hzeroSecond : IntervalIntegrable
      (fun position : ℝ => value + second / 2 * (position - center) ^ 2)
      volume left right :=
    hzero.add (hterm (second / 2) 2)
  have hzeroSecondFourth : IntervalIntegrable
      (fun position : ℝ =>
        value + second / 2 * (position - center) ^ 2 +
          fourth / 24 * (position - center) ^ 4)
      volume left right :=
    hzeroSecond.add (hterm (fourth / 24) 4)
  dsimp [majorant, symmetricTaylor6Majorant3193]
  rw [intervalIntegral.integral_add hzeroSecondFourth (hterm (sixth / 720) 6)]
  rw [intervalIntegral.integral_add hzeroSecond (hterm (fourth / 24) 4)]
  rw [intervalIntegral.integral_add hzero (hterm (second / 2) 2)]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  rw [hpow 2, hpow 4, hpow 6]
  rw [intervalIntegral.integral_const]
  norm_num [hwidth.ne']
  ring

end ConnesWeilRH.Dev
