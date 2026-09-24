import ConnesWeilRH.Dev.C1ExplicitSmoothSeed
import ConnesWeilRH.Dev.C1ExplicitSmoothSeedDerivativeBudget
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed

open Real
open Polynomial
open expNegInvGlue
open ConnesWeilRH.Source.C1ExplicitFiniteNodeCorrection

noncomputable section

lemma expNegInvGlue_sq_mul_exp_neg_le_four {t : ℝ} (ht : 0 ≤ t) :
    t ^ 2 * Real.exp (-t) ≤ 4 := by
  have h := Real.add_one_le_exp (t / 2)
  have hsq : (1 + t / 2) ^ 2 ≤ Real.exp t := by
    calc
      (1 + t / 2) ^ 2 ≤ Real.exp (t / 2) ^ 2 :=
        (sq_le_sq₀ (by positivity : (0 : ℝ) ≤ 1 + t / 2)
          (Real.exp_nonneg _)).2 (by simpa [add_comm] using h)
      _ = Real.exp ((t / 2) + (t / 2)) := by
        rw [Real.exp_add]
        ring
      _ = Real.exp t := by congr 1 <;> ring
  have hpoly : t ^ 2 ≤ 4 * (1 + t / 2) ^ 2 := by
    nlinarith
  have hte : t ^ 2 ≤ 4 * Real.exp t := hpoly.trans (mul_le_mul_of_nonneg_left hsq (by positivity))
  calc
    t ^ 2 * Real.exp (-t) ≤ 4 * Real.exp t * Real.exp (-t) :=
      mul_le_mul_of_nonneg_right hte (Real.exp_nonneg _)
    _ = 4 := by
      rw [Real.exp_neg]
      field_simp [Real.exp_ne_zero]

theorem norm_deriv_expNegInvGlue_le_four (x : ℝ) :
    ‖deriv expNegInvGlue x‖ ≤ 4 := by
  have hd := hasDerivAt_polynomial_eval_inv_mul (1 : ℝ[X]) x
  have hformula :
      deriv expNegInvGlue x =
        ((Polynomial.X ^ 2).eval x⁻¹) * expNegInvGlue x := by
    simpa [expNegInvGlue, Polynomial.eval_one, Polynomial.derivative_one] using hd.deriv
  rw [hformula]
  by_cases hx : x ≤ 0
  · rw [zero_of_nonpos hx]
    simp
  · have hx' : 0 < x := lt_of_not_ge hx
    simp only [Polynomial.eval_pow, Polynomial.eval_X, one_mul]
    simp only [expNegInvGlue, hx, ↓reduceIte]
    rw [Real.norm_eq_abs]
    rw [abs_of_nonneg (mul_nonneg (sq_nonneg (x⁻¹)) (Real.exp_nonneg (-x⁻¹)))]
    exact expNegInvGlue_sq_mul_exp_neg_le_four (le_of_lt (inv_pos.mpr hx'))


end
end ConnesWeilRH.Source.C1ExplicitSmoothSeed
