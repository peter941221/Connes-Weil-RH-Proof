import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

namespace ConnesWeilRH.Dev

theorem powerExpUpper2349 {position decay : ℝ} {order : ℕ}
    (hposition : 1 ≤ position) (horder : (order : ℝ) ≤ decay) :
    position ^ order * Real.exp (-decay * position) ≤ Real.exp (-decay) := by
  have hpositive : 0 < position := by linarith
  have hlog := Real.log_le_sub_one_of_pos hpositive
  have hlogScaled := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg order : (0 : ℝ) ≤ order)
  have horderScaled := mul_le_mul_of_nonneg_right horder (by linarith : 0 ≤ position - 1)
  calc
    position ^ order * Real.exp (-decay * position) =
        Real.exp ((order : ℝ) * Real.log position + -decay * position) := by
      rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log hpositive]
    _ ≤ Real.exp (-decay) := Real.exp_le_exp.mpr (by nlinarith)

theorem polynomialAbsUpper2349 {Index : Type*} (terms : Finset Index)
    (coefficient : Index → ℝ) (power : Index → ℕ) {position : ℝ}
    (hposition : |position| ≤ 1) :
    |∑ index ∈ terms, coefficient index * position ^ power index| ≤
      ∑ index ∈ terms, |coefficient index| := by
  calc
    _ ≤ ∑ index ∈ terms, |coefficient index * position ^ power index| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := Finset.sum_le_sum fun index hindex => by
      rw [abs_mul, abs_pow]
      exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (abs_nonneg _) hposition)

theorem polynomialExpUpper2349 {Index : Type*} (terms : Finset Index)
    (coefficient : Index → ℝ) (power : Index → ℕ) {position inverseDeficit : ℝ}
    {order : ℕ} (hposition : |position| ≤ 1) (hdeficit : 1 ≤ inverseDeficit)
    (horder : (order : ℝ) ≤ 30) :
    |Real.exp (-30 * inverseDeficit) * inverseDeficit ^ order *
      (∑ index ∈ terms, coefficient index * position ^ power index)| ≤
      Real.exp (-30) * (∑ index ∈ terms, |coefficient index|) := by
  have hdeficitNonneg : 0 ≤ inverseDeficit := by linarith
  have hcoeff : 0 ≤ ∑ index ∈ terms, |coefficient index| :=
    Finset.sum_nonneg fun index hindex => abs_nonneg _
  rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _),
    abs_of_nonneg (pow_nonneg hdeficitNonneg _)]
  calc
    _ ≤ Real.exp (-30 * inverseDeficit) * inverseDeficit ^ order *
        (∑ index ∈ terms, |coefficient index|) :=
      mul_le_mul_of_nonneg_left (polynomialAbsUpper2349 terms coefficient power hposition)
        (mul_nonneg (Real.exp_nonneg _) (pow_nonneg hdeficitNonneg _))
    _ = (inverseDeficit ^ order * Real.exp (-30 * inverseDeficit)) *
        (∑ index ∈ terms, |coefficient index|) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (powerExpUpper2349 hdeficit horder) hcoeff

end ConnesWeilRH.Dev

