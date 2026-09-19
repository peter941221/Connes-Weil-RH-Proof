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

end Dev
end ConnesWeilRH
