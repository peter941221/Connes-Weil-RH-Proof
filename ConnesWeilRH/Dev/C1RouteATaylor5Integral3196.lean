import ConnesWeilRH.Dev.C1RouteATaylor5CellUpper3195
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace ConnesWeilRH.Dev

open MeasureTheory

theorem intervalIntegral_taylor5_upper_cancel_odd3196
    {function : ℝ → ℝ} {left right center value first second third fourth fifth sixth : ℝ}
    (horder : left < right)
    (hcenter : center = (left + right) / 2)
    (hpointwise : ∀ position ∈ Set.Icc left right,
      function position ≤
        value + first * (position - center) + second / 2 * (position - center) ^ 2 +
          third / 6 * (position - center) ^ 3 + fourth / 24 * (position - center) ^ 4 +
          fifth / 120 * (position - center) ^ 5 + sixth / 720 * (position - center) ^ 6)
    (hfunction : IntervalIntegrable function volume left right) :
    (∫ position in left..right, function position) ≤
      (right - left) * value +
        (right - left) ^ 3 * second / 24 +
        (right - left) ^ 5 * fourth / 1920 +
        (right - left) ^ 7 * sixth / 322560 := by
  let majorant := fun position : ℝ =>
    value + first * (position - center) + second / 2 * (position - center) ^ 2 +
      third / 6 * (position - center) ^ 3 + fourth / 24 * (position - center) ^ 4 +
      fifth / 120 * (position - center) ^ 5 + sixth / 720 * (position - center) ^ 6
  have hmajorant : Continuous majorant := by
    change Continuous (fun position : ℝ =>
      value + first * (position - center) + second / 2 * (position - center) ^ 2 +
        third / 6 * (position - center) ^ 3 + fourth / 24 * (position - center) ^ 4 +
        fifth / 120 * (position - center) ^ 5 + sixth / 720 * (position - center) ^ 6)
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
  have hfirst : IntervalIntegrable
      (fun position : ℝ => first * (position - center)) volume left right := by
    simpa [pow_one] using hterm first 1
  have hsum1 : IntervalIntegrable
      (fun position : ℝ => value + first * (position - center)) volume left right :=
    hzero.add hfirst
  have hsum2 : IntervalIntegrable
      (fun position : ℝ => value + first * (position - center) +
        second / 2 * (position - center) ^ 2) volume left right :=
    hsum1.add (hterm (second / 2) 2)
  have hsum3 : IntervalIntegrable
      (fun position : ℝ => value + first * (position - center) +
        second / 2 * (position - center) ^ 2 +
        third / 6 * (position - center) ^ 3) volume left right :=
    hsum2.add (hterm (third / 6) 3)
  have hsum4 : IntervalIntegrable
      (fun position : ℝ => value + first * (position - center) +
        second / 2 * (position - center) ^ 2 +
        third / 6 * (position - center) ^ 3 +
        fourth / 24 * (position - center) ^ 4) volume left right :=
    hsum3.add (hterm (fourth / 24) 4)
  have hsum5 : IntervalIntegrable
      (fun position : ℝ => value + first * (position - center) +
        second / 2 * (position - center) ^ 2 +
        third / 6 * (position - center) ^ 3 +
        fourth / 24 * (position - center) ^ 4 +
        fifth / 120 * (position - center) ^ 5) volume left right :=
    hsum4.add (hterm (fifth / 120) 5)
  dsimp [majorant]
  rw [intervalIntegral.integral_add hsum5 (hterm (sixth / 720) 6)]
  rw [intervalIntegral.integral_add hsum4 (hterm (fifth / 120) 5)]
  rw [intervalIntegral.integral_add hsum3 (hterm (fourth / 24) 4)]
  rw [intervalIntegral.integral_add hsum2 (hterm (third / 6) 3)]
  rw [intervalIntegral.integral_add hsum1 (hterm (second / 2) 2)]
  rw [intervalIntegral.integral_add hzero hfirst]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hpow1 :
      (∫ position in left..right, position - center) =
        (((right - left) / 2) ^ (1 + 1) -
          (-(right - left) / 2) ^ (1 + 1)) / (1 + 1) := by
    simpa [pow_one] using hpow 1
  rw [hpow1, hpow 2, hpow 3, hpow 4, hpow 5, hpow 6]
  rw [intervalIntegral.integral_const]
  norm_num [hwidth.ne']
  ring

end ConnesWeilRH.Dev
