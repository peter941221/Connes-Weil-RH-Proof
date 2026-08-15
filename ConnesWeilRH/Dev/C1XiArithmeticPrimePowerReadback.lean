import ConnesWeilRH.Dev.C1XiArithmeticIntervalReadback
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# C1XiArithmeticPrimePowerReadback - prime-power Fourier readback

The right-line von Mangoldt term is a Fourier transform of an exponentially
weighted compact-log test.  Fourier inversion therefore reads one complete
vertical-line integral back to the corresponding finite prime-power value.
This module proves that bridge for one index before assembling the finite
visible-prime sum.
-/

namespace ConnesWeilRH
namespace Source
namespace C1XiArithmeticPrimePowerReadback

open MeasureTheory
open Complex
open CC20YoshidaConvolution
open CCM25Concrete.CompactLogConvolution
open C1XiArithmeticIntervalReadback
open C1XiVerticalFunctional
open scoped FourierTransform LSeries.notation Topology

noncomputable section

/-- The unweighted Fourier profile used by a vertical-line Laplace value. -/
noncomputable def fourierLaplace
    (f : TestFunction) (t : Real) : Complex :=
  ∫ u : Real,
    Complex.exp ((t : Complex) * (u : Complex) * Complex.I) * f u

theorem fourierLaplace_eq_fourier
    (f : TestFunction) (t : Real) :
    fourierLaplace f t =
      (𝓕 f) (-(t / (2 * Real.pi))) := by
  unfold fourierLaplace
  rw [SchwartzMap.fourier_coe, Real.fourier_eq']
  apply integral_congr_ae
  filter_upwards with u
  simp only [smul_eq_mul, Real.inner_apply]
  congr 2
  push_cast
  field_simp [Real.pi_ne_zero]

set_option maxHeartbeats 800000 in
private theorem integral_fourierLaplace_mul_character
    (f : TestFunction) (x : Real) :
    ∫ t : Real,
        fourierLaplace f t *
          Complex.exp (-((t : Complex) * (x : Complex) * Complex.I)) =
      (2 * (Real.pi : Complex)) * f x := by
  let h : Real → Complex := fun t =>
    fourierLaplace f t *
      Complex.exp (-((t : Complex) * (x : Complex) * Complex.I))
  have hinv : 𝓕⁻ (𝓕 f) x = f x := by
    simpa only [SchwartzMap.fourierInv_coe, SchwartzMap.fourier_coe] using
      (f.integrable.fourierInv_fourier_eq (𝓕 f).integrable
        f.continuous.continuousAt)
  have hchange := Measure.integral_comp_mul_left h (-2 * Real.pi)
  have hscale : |((-2 * Real.pi)⁻¹ : Real)| = (2 * Real.pi)⁻¹ := by
    have harg : (-2 * Real.pi : Real) = -(2 * Real.pi) := by ring
    have harg_neg : (-2 * Real.pi : Real) < 0 := by nlinarith [Real.pi_pos]
    rw [abs_of_neg (inv_lt_zero.mpr harg_neg), harg, inv_neg]
    simp
  have hchange' :
      ∫ ξ : Real, h ((-2 * Real.pi) * ξ) =
        ((2 * Real.pi : Real)⁻¹ : Complex) * ∫ t : Real, h t := by
    simpa only [hscale, Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_mul] using hchange
  have hinv' := Real.fourierInv_eq' ((𝓕 f : TestFunction) : Real → Complex) x
  have hscaled :
      ∫ ξ : Real, h ((-2 * Real.pi) * ξ) = 𝓕⁻ (𝓕 f) x := by
    rw [SchwartzMap.fourierInv_coe, hinv']
    apply integral_congr_ae
    filter_upwards with ξ
    simp only [h]
    rw [fourierLaplace_eq_fourier]
    simp only [smul_eq_mul]
    have harg : -((-2 * Real.pi * ξ) / (2 * Real.pi)) = ξ := by
      field_simp [Real.pi_ne_zero]
    rw [harg]
    have hexp :
        Complex.exp (-(((-2 * Real.pi * ξ : Real) : Complex) *
          (x : Complex) * Complex.I)) =
          Complex.exp ((↑(2 * Real.pi * (inner ℝ ξ x)) : Complex) * Complex.I) := by
      congr 1
      simp only [Real.inner_apply, Complex.ofReal_mul, Complex.ofReal_neg]
      push_cast
      ring
    rw [hexp]
    ring
  rw [hscaled, hinv] at hchange'
  have hpi_ne : (2 * (Real.pi : Complex)) ≠ 0 := by
    exact mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hchange'' :
      f x = (2 * (Real.pi : Complex))⁻¹ * ∫ t : Real, h t := by
    simpa only [Complex.ofReal_mul] using hchange'
  calc
    ∫ t : Real, h t =
        (2 * (Real.pi : Complex)) *
          ((2 * (Real.pi : Complex))⁻¹ * ∫ t : Real, h t) := by
      field_simp
    _ = (2 * (Real.pi : Complex)) * f x := by rw [← hchange'']

end
end C1XiArithmeticPrimePowerReadback
end Source
end ConnesWeilRH
