/- Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.CCM24HardyTitchmarsh

/-!
# Paley-Wiener spectral layer, part 1: the positive-frequency half-line

The inner/outer construction (docs/1002, docs/proofs/1003 sub-gates A2-A3)
needs the Paley-Wiener spectral projections onto the positive / negative
halves of the log-Fourier axis on the carrier `cc20GlobalLogCrossingL2`.  Each
is the conjugated indicator-multiplier F-inverse (1_[0,inf) .) F.  This module
builds the positive-frequency part as a bounded linear operator and its kernel.
No Hardy machinery exists in mathlib v4.30.0, so the layer is built here from
the Fourier isometry `Lp.fourierTransform_l_i`, mirroring how
`ccm24ArchimedeanHardyTitchmarsh` threads Fourier and the scattering multiplier.
-/

namespace ConnesWeilRH
namespace Source
namespace CC20Concrete

open MeasureTheory Set Filter
open scoped ComplexConjugate ENNReal

/-- The positive half-line of the log-Fourier centre. -/
noncomputable def ccm24FreqPositiveHalf : Set Real :=
  Set.Ici (0 : Real)

theorem measurableSet_ccm24FreqPositiveHalf :
    MeasurableSet ccm24FreqPositiveHalf := by
  exact measurableSet_Ici

/-- The indicator `1_[0,inf) : Real -> Complex`, as a concrete function. -/
noncomputable def ccm24FreqPositiveIndicatorFunction : Real -> Complex :=
  (ccm24FreqPositiveHalf : Set Real).indicator (fun _ => (1 : Complex))

theorem stronglyMeasurable_ccm24FreqPositiveIndicator :
    StronglyMeasurable ccm24FreqPositiveIndicatorFunction := by
  exact StronglyMeasurable.indicator
    (stronglyMeasurable_const : StronglyMeasurable (fun _ : Real => (1 : Complex)))
    measurableSet_ccm24FreqPositiveHalf

theorem norm_ccm24FreqPositiveIndicatorFunction (x : Real) :
    norm (ccm24FreqPositiveIndicatorFunction x) <= 1 := by
  rw [ccm24FreqPositiveIndicatorFunction]
  by_cases hx : x ∈ ccm24FreqPositiveHalf
  · simp [hx]
  · simp [hx]

theorem memLp_ccm24FreqPositiveIndicatorFunction :
    MemLp ccm24FreqPositiveIndicatorFunction ∞ (volume : Measure Real) := by
  exact memLp_top_of_bound (μ := volume)
    (stronglyMeasurable_ccm24FreqPositiveIndicator.aestronglyMeasurable) 1
    (Filter.Eventually.of_forall (norm_ccm24FreqPositiveIndicatorFunction))

/-- The indicator as an element of the log-Fourier L-inf space. -/
noncomputable def ccm24FreqPositiveHalfLp : Lp Complex ∞ (volume : Measure Real) :=
  memLp_ccm24FreqPositiveIndicatorFunction.toLp ccm24FreqPositiveIndicatorFunction

theorem ccm24FreqPositiveHalfLp_coeFn :
    (ccm24FreqPositiveHalfLp : Real -> Complex) =ᵐ[volume]
      ccm24FreqPositiveIndicatorFunction :=
  memLp_ccm24FreqPositiveIndicatorFunction.coeFn_toLp


/-- Multiplication by the positive-frequency indicator on the log-Fourier
`L2` carrier: the bounded multiplier `u -> 1_{[0,inf)} * u`. -/
noncomputable def ccm24FreqPositiveMultiplier :
    cc20GlobalLogCrossingL2 →ₗ[ℂ] cc20GlobalLogCrossingL2 where
  toFun u := ccm24FreqPositiveHalfLp • u
  map_add' := Lp.add_smul ccm24FreqPositiveHalfLp
  map_smul' c u := by
    exact (Lp.smul_comm c ccm24FreqPositiveHalfLp u).symm

/-- The Paley--Wiener positive-frequency projection `P+ = F-inverse
(1_{[0,inf)} .) F` on the log-Fourier `L2` carrier. -/
noncomputable def ccm24PositiveFrequencyProjection :
    cc20GlobalLogCrossingL2 →ₗ[ℂ] cc20GlobalLogCrossingL2 :=
  (Lp.fourierTransformₗᵢ ℝ ℂ).symm.toLinearMap.comp
    (ccm24FreqPositiveMultiplier.comp (Lp.fourierTransformₗᵢ ℝ ℂ).toLinearMap)


/-- Spectral readback: the Fourier image of the positive-frequency projection is
exactly the positive-frequency indicator acting on the Fourier image. -/
theorem ccm24PositiveFrequencyProjection_fourier_readback
    (u : cc20GlobalLogCrossingL2) :
    Lp.fourierTransformₗᵢ ℝ ℂ (ccm24PositiveFrequencyProjection u) =
      ccm24FreqPositiveHalfLp • (Lp.fourierTransformₗᵢ ℝ ℂ u) := by
  simp [ccm24PositiveFrequencyProjection, ccm24FreqPositiveMultiplier]

/-- The positive-frequency indicator idempotence formula, pointwise. -/
theorem ccm24FreqPositiveIndicatorFunction_idem (x : ℝ) :
    ccm24FreqPositiveIndicatorFunction x * ccm24FreqPositiveIndicatorFunction x =
      ccm24FreqPositiveIndicatorFunction x := by
  rw [ccm24FreqPositiveIndicatorFunction]
  by_cases hx : x ∈ ccm24FreqPositiveHalf
  · simp [hx]
  · simp [hx]




/-- Scalar idempotence of the indicator on the complex module: multiplying
twice by `1_{[0,inf)} (x)` is the same as multiplying once. -/
theorem ccm24FreqPositiveIndicator_smul_idem (x : Real) (z : Complex) :
    ccm24FreqPositiveIndicatorFunction x • (ccm24FreqPositiveIndicatorFunction x • z) =
      ccm24FreqPositiveIndicatorFunction x • z := by
  simp only [smul_eq_mul]
  rw [← mul_assoc, ccm24FreqPositiveIndicatorFunction_idem x]

/-- The positive-frequency projection `P+` is idempotent: `P+ (P+ u) = P+ u`. -/
theorem ccm24PositiveFrequencyProjection_idempotent
    (u : cc20GlobalLogCrossingL2) :
    ccm24PositiveFrequencyProjection (ccm24PositiveFrequencyProjection u) =
      ccm24PositiveFrequencyProjection u := by
  -- The indicator idempotent applies to the log-Fourier L-infinity space.
  have hf : ccm24FreqPositiveHalfLp • ccm24FreqPositiveHalfLp = ccm24FreqPositiveHalfLp := by
    rw [Lp.ext_iff]
    filter_upwards
      [Lp.coeFn_lpSMul (p := ∞) (q := ∞) (r := ∞) ccm24FreqPositiveHalfLp ccm24FreqPositiveHalfLp,
       ccm24FreqPositiveHalfLp_coeFn] with x hsm hf
    rw [hsm]
    simpa [smul_eq_mul, hf] using ccm24FreqPositiveIndicatorFunction_idem x
  apply (Lp.fourierTransformₗᵢ ℝ ℂ).injective
  rw [ccm24PositiveFrequencyProjection_fourier_readback]
  rw [ccm24PositiveFrequencyProjection_fourier_readback]
  rw [Lp.ext_iff]
  filter_upwards
    [Lp.coeFn_lpSMul (p := ∞) (q := 2) (r := 2) ccm24FreqPositiveHalfLp
       (ccm24FreqPositiveHalfLp • (Lp.fourierTransformₗᵢ ℝ ℂ u)),
     Lp.coeFn_lpSMul (p := ∞) (q := 2) (r := 2) ccm24FreqPositiveHalfLp
       (Lp.fourierTransformₗᵢ ℝ ℂ u),
     ccm24FreqPositiveHalfLp_coeFn] with x h1 h2 hfE
  rw [h1]
  simp only [Pi.smul_apply']
  rw [h2]
  simp only [Pi.smul_apply']
  rw [hfE]
  exact ccm24FreqPositiveIndicator_smul_idem x (Lp.fourierTransformₗᵢ ℝ ℂ u x)

end CC20Concrete
end Source
end ConnesWeilRH
