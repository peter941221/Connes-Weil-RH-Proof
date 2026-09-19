/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.CCM24ArchimedeanCarrier

/-!
# Quantitative Fourier tail rate for the Hardy-tail consumer

The qualitative translated-tail theorem only gives convergence to zero.  This
file records the next analytic rate: two integrable derivatives give a
quadratic pointwise Fourier decay.  Its square is summable on unit annuli, so
this is the rate needed by the live G8 Hardy-tail consumer once the concrete
source vector is placed in this Sobolev class.
-/

namespace ConnesWeilRH
namespace Dev

open MeasureTheory
open Source
open Source.CC20Concrete
open scoped FourierTransform

theorem fourier_norm_mul_sq_le_integral_norm_second_deriv
    (g : ℝ → ℂ)
    (hg : Integrable g volume)
    (hgDiff : Differentiable ℝ g)
    (hgDeriv : Integrable (deriv g) volume)
    (hderivDiff : Differentiable ℝ (deriv g))
    (hsecond : Integrable (deriv (deriv g)) volume) (x : ℝ) :
    ‖x‖ ^ 2 * ‖𝓕 g x‖ ≤ ∫ t : ℝ, ‖deriv (deriv g) t‖ ∂volume := by
  let C2 : ℝ := ∫ t : ℝ, ‖deriv (deriv g) t‖ ∂volume
  have hfirst := congrFun (Real.fourier_deriv hg hgDiff hgDeriv) x
  have hsecond' := congrFun
    (Real.fourier_deriv hgDeriv hderivDiff hsecond) x
  have hfirst_norm :
      ‖(2 * Real.pi : ℂ) * Complex.I * (x : ℂ)‖ * ‖𝓕 g x‖ =
        ‖𝓕 (deriv g) x‖ := by
    simpa only [norm_smul] using (congrArg norm hfirst).symm
  have hsecond_norm :
      ‖(2 * Real.pi : ℂ) * Complex.I * (x : ℂ)‖ *
          ‖𝓕 (deriv g) x‖ ≤ C2 := by
    calc
      _ = ‖(2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) •
          𝓕 (deriv g) x‖ := by rw [norm_smul]
      _ = ‖𝓕 (deriv (deriv g)) x‖ := by rw [← hsecond']
      _ ≤ C2 := VectorFourier.norm_fourierIntegral_le_integral_norm
        𝐞 volume (innerₗ ℝ) (deriv (deriv g)) x
  have hpi : 1 ≤ 2 * Real.pi := by
    nlinarith [Real.one_le_pi_div_two]
  have hscale :
      ‖x‖ ^ 2 * ‖𝓕 g x‖ ≤
        ‖(2 * Real.pi : ℂ) * Complex.I * (x : ℂ)‖ *
          ‖𝓕 (deriv g) x‖ := by
    have hscalar :
        ‖(2 * Real.pi : ℂ) * Complex.I * (x : ℂ)‖ =
          (2 * Real.pi) * ‖x‖ := by
      simp only [norm_mul, Complex.norm_real, Complex.norm_I,
        Complex.norm_natCast, Complex.norm_ofNat, Real.norm_eq_abs]
      rw [abs_of_pos Real.pi_pos]
      ring
    rw [hscalar]
    have hfirst_norm' := hfirst_norm
    rw [hscalar] at hfirst_norm'
    rw [← hfirst_norm']
    have hcoef : 1 ≤ (2 * Real.pi) ^ 2 := by nlinarith [hpi]
    have hnonneg : 0 ≤ ‖x‖ ^ 2 * ‖𝓕 g x‖ :=
      mul_nonneg (sq_nonneg _) (norm_nonneg _)
    have hmul := mul_le_mul_of_nonneg_right hcoef hnonneg
    calc
      ‖x‖ ^ 2 * ‖𝓕 g x‖ ≤ (2 * Real.pi) ^ 2 *
          (‖x‖ ^ 2 * ‖𝓕 g x‖) := by simpa using hmul
      _ = (2 * Real.pi * ‖x‖) *
          (2 * Real.pi * ‖x‖ * ‖𝓕 g x‖) := by ring
  dsimp [C2] at hsecond_norm ⊢
  exact hscale.trans hsecond_norm

theorem summable_normSq_of_quadratic_decay
    {E : Type*} [SeminormedAddCommGroup E]
    (u : ℕ → E) {C : ℝ} (hC : 0 ≤ C)
    (hdecay : ∀ n : ℕ,
      ‖u n‖ ≤ C * (((n + 1 : ℕ) : ℝ) ^ (-2 : ℝ))) :
    Summable (fun n : ℕ => ‖u n‖ ^ 2) := by
  have hnat : Summable (fun n : ℕ => (n : ℝ) ^ (-2 : ℝ)) := by
    apply Real.summable_nat_rpow.mpr
    norm_num
  have hshift : Summable
      (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-2 : ℝ)) := by
    simpa using
      (summable_nat_add_iff
        (f := fun n : ℕ => (n : ℝ) ^ (-2 : ℝ)) 1).mpr hnat
  have hmajor : Summable (fun n : ℕ =>
      C ^ 2 * (((n + 1 : ℕ) : ℝ) ^ (-2 : ℝ))) :=
    hshift.mul_left (C ^ 2)
  refine Summable.of_nonneg_of_le
    (fun n => sq_nonneg (‖u n‖)) ?_ hmajor
  intro n
  let z : ℝ := (((n + 1 : ℕ) : ℝ) ^ (-2 : ℝ))
  have hz0 : 0 ≤ z := by
    dsimp [z]
    positivity
  have hz1 : z ≤ 1 := by
    dsimp [z]
    exact Real.rpow_le_one_of_one_le_of_nonpos
      (by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))) (by norm_num)
  have hsq : z ^ 2 ≤ z := by nlinarith
  have hscaled : C ^ 2 * z ^ 2 ≤ C ^ 2 * z :=
    mul_le_mul_of_nonneg_left hsq (sq_nonneg C)
  have hnorm : ‖u n‖ ^ 2 ≤ (C * z) ^ 2 := by
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC hz0)).2 (hdecay n)
  calc
    ‖u n‖ ^ 2 ≤ (C * z) ^ 2 := hnorm
    _ = C ^ 2 * z ^ 2 := by ring
    _ ≤ C ^ 2 * z := hscaled
    _ = C ^ 2 * (((n + 1 : ℕ) : ℝ) ^ (-2 : ℝ)) := by rfl

end Dev
end ConnesWeilRH
