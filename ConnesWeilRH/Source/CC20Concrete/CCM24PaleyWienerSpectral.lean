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

/-- The non-positive half-line of the log-Fourier centre: `(-inf,0)`. -/
noncomputable def ccm24FreqNegativeHalf : Set ℝ :=
  Set.Iio (0 : ℝ)

theorem measurableSet_ccm24FreqNegativeHalf :
    MeasurableSet ccm24FreqNegativeHalf := by
  exact measurableSet_Iio

/-- The negative-frequency indicator `1_{(-inf,0)} : Real -> Complex`. -/
noncomputable def ccm24FreqNegativeIndicatorFunction : ℝ → ℂ :=
  (ccm24FreqNegativeHalf : Set ℝ).indicator (fun _ => (1 : ℂ))

theorem stronglyMeasurable_ccm24FreqNegativeIndicator :
    StronglyMeasurable ccm24FreqNegativeIndicatorFunction := by
  exact StronglyMeasurable.indicator
    (stronglyMeasurable_const : StronglyMeasurable (fun _ : ℝ => (1 : ℂ)))
    measurableSet_ccm24FreqNegativeHalf

theorem norm_ccm24FreqNegativeIndicatorFunction (x : ℝ) :
    norm (ccm24FreqNegativeIndicatorFunction x) <= 1 := by
  rw [ccm24FreqNegativeIndicatorFunction]
  by_cases hx : x ∈ ccm24FreqNegativeHalf
  · simp [hx]
  · simp [hx]

theorem memLp_ccm24FreqNegativeIndicatorFunction :
    MemLp ccm24FreqNegativeIndicatorFunction ∞ (volume : Measure ℝ) := by
  exact memLp_top_of_bound (μ := volume)
    (stronglyMeasurable_ccm24FreqNegativeIndicator.aestronglyMeasurable) 1
    (Filter.Eventually.of_forall (norm_ccm24FreqNegativeIndicatorFunction))

/-- The negative indicator as the log-Fourier `L-infinity` element. -/
noncomputable def ccm24FreqNegativeHalfLp : Lp ℂ ∞ (volume : Measure ℝ) :=
  memLp_ccm24FreqNegativeIndicatorFunction.toLp ccm24FreqNegativeIndicatorFunction

theorem ccm24FreqNegativeHalfLp_coeFn :
    (ccm24FreqNegativeHalfLp : ℝ → ℂ) =ᵐ[volume]
      ccm24FreqNegativeIndicatorFunction :=
  memLp_ccm24FreqNegativeIndicatorFunction.coeFn_toLp

/-- Multiplication by the negative-frequency indicator on the log-Fourier
`L2` carrier: the bounded multiplier `u -> 1_{(-inf,0)} * u`. -/
noncomputable def ccm24FreqNegativeMultiplier :
    cc20GlobalLogCrossingL2 →ₗ[ℂ] cc20GlobalLogCrossingL2 where
  toFun u := ccm24FreqNegativeHalfLp • u
  map_add' := Lp.add_smul ccm24FreqNegativeHalfLp
  map_smul' c u := by
    exact (Lp.smul_comm c ccm24FreqNegativeHalfLp u).symm

/-- The Paley--Wiener negative-frequency projection `P- = F-inverse
(1_{(-inf,0)} .) F` on the log-Fourier `L2` carrier. -/
noncomputable def ccm24NegativeFrequencyProjection :
    cc20GlobalLogCrossingL2 →ₗ[ℂ] cc20GlobalLogCrossingL2 :=
  (Lp.fourierTransformₗᵢ ℝ ℂ).symm.toLinearMap.comp
    (ccm24FreqNegativeMultiplier.comp (Lp.fourierTransformₗᵢ ℝ ℂ).toLinearMap)

/-- Spectral readback of the negative-frequency projection: its Fourier image
is exactly the negative-frequency indicator acting on the Fourier image. -/
theorem ccm24NegativeFrequencyProjection_fourier_readback
    (u : cc20GlobalLogCrossingL2) :
    Lp.fourierTransformₗᵢ ℝ ℂ (ccm24NegativeFrequencyProjection u) =
      ccm24FreqNegativeHalfLp • (Lp.fourierTransformₗᵢ ℝ ℂ u) := by
  simp [ccm24NegativeFrequencyProjection, ccm24FreqNegativeMultiplier]

/-- The two half-line indicators, weighted by a complex scalar, sum to the scalar
pointwise: `1_[0,inf)(x) * c + 1_(-inf,0)(x) * c = c`. -/
theorem ccm24HalfIndicator_add_pointwise (x : ℝ) (c : ℂ) :
    ccm24FreqPositiveIndicatorFunction x * c + ccm24FreqNegativeIndicatorFunction x * c = c := by
  by_cases hx : x < 0
  · rw [ccm24FreqPositiveIndicatorFunction, ccm24FreqNegativeIndicatorFunction]
    have hpos : x ∉ ccm24FreqPositiveHalf := by
      simpa [ccm24FreqPositiveHalf] using (not_le_of_gt hx)
    have hmem : x ∈ ccm24FreqNegativeHalf := by
      simpa [ccm24FreqNegativeHalf] using hx
    simp [hpos, hmem]
  · rw [ccm24FreqPositiveIndicatorFunction, ccm24FreqNegativeIndicatorFunction]
    have hge : (0 : ℝ) ≤ x := le_of_not_gt hx
    have hpos : x ∈ ccm24FreqPositiveHalf := by simpa [ccm24FreqPositiveHalf] using hge
    have hnegg : x ∉ ccm24FreqNegativeHalf := by
      simpa [ccm24FreqNegativeHalf] using (not_lt_of_ge hge)
    simp [hpos, hnegg]

/-- The two half-line projectors are complementary: `P+ u + P- u = u`. -/
theorem ccm24PositiveFrequencyProjection_add_negative
    (u : cc20GlobalLogCrossingL2) :
    ccm24PositiveFrequencyProjection u + ccm24NegativeFrequencyProjection u = u := by
  apply (Lp.fourierTransformₗᵢ ℝ ℂ).injective
  rw [map_add]
  rw [ccm24PositiveFrequencyProjection_fourier_readback,
      ccm24NegativeFrequencyProjection_fourier_readback]
  rw [Lp.ext_iff]
  filter_upwards
    [Lp.coeFn_add (ccm24FreqPositiveHalfLp • (Lp.fourierTransformₗᵢ ℝ ℂ u))
       (ccm24FreqNegativeHalfLp • (Lp.fourierTransformₗᵢ ℝ ℂ u)),
     Lp.coeFn_lpSMul (p := ∞) (q := 2) (r := 2) ccm24FreqPositiveHalfLp
       (Lp.fourierTransformₗᵢ ℝ ℂ u),
     Lp.coeFn_lpSMul (p := ∞) (q := 2) (r := 2) ccm24FreqNegativeHalfLp
       (Lp.fourierTransformₗᵢ ℝ ℂ u),
     ccm24FreqPositiveHalfLp_coeFn,
     ccm24FreqNegativeHalfLp_coeFn] with x hadd hps hns hpe hnn
  rw [hadd]
  rw [Pi.add_apply]
  rw [hps, hns]
  simp only [Pi.smul_apply']
  rw [hpe, hnn]
  simpa [smul_eq_mul] using (ccm24HalfIndicator_add_pointwise x (Lp.fourierTransformₗᵢ ℝ ℂ u x))
/-- The non-negative-frequency Hardy half-space `H+ = { u : P- u = 0 }`.  Because
`P- P+ u = 0` for every `u`, this is equivalently `ker (I - P+)`. -/
noncomputable def ccm24HardyPositiveSubspace : Submodule ℂ cc20GlobalLogCrossingL2 :=
  ccm24NegativeFrequencyProjection.ker

/-- The strictly-negative-frequency Hardy half-space `H- = { u : P+ u = 0 }`, the kernel
of the positive-frequency projection. -/
noncomputable def ccm24HardyNegativeSubspace : Submodule ℂ cc20GlobalLogCrossingL2 :=
  ccm24PositiveFrequencyProjection.ker

theorem mem_ccm24HardyPositiveSubspace_iff (u : cc20GlobalLogCrossingL2) :
    u ∈ ccm24HardyPositiveSubspace ↔ ccm24NegativeFrequencyProjection u = 0 := by
  simp [ccm24HardyPositiveSubspace, LinearMap.mem_ker]

theorem mem_ccm24HardyNegativeSubspace_iff (u : cc20GlobalLogCrossingL2) :
    u ∈ ccm24HardyNegativeSubspace ↔ ccm24PositiveFrequencyProjection u = 0 := by
  simp [ccm24HardyNegativeSubspace, LinearMap.mem_ker]

/-- The two half-line indicators are pointwise orthogonal as scalar factors. -/
theorem ccm24HalfProjectors_mult_zero_pointwise (x : ℝ) (c : ℂ) :
    ccm24FreqNegativeIndicatorFunction x * (ccm24FreqPositiveIndicatorFunction x * c) = 0 := by
  rw [ccm24FreqNegativeIndicatorFunction, ccm24FreqPositiveIndicatorFunction]
  by_cases hx : x < 0
  · have hpos : x ∉ ccm24FreqPositiveHalf := by
      simpa [ccm24FreqPositiveHalf] using (not_le_of_gt hx)
    simp [hpos]
  · have hge : 0 ≤ x := le_of_not_gt hx
    have hpos : x ∈ ccm24FreqPositiveHalf := by
      simpa [ccm24FreqPositiveHalf] using hge
    have hneg : x ∉ ccm24FreqNegativeHalf := by
      simpa [ccm24FreqNegativeHalf] using (not_lt_of_ge hge)
    simp [hpos, hneg]

end CC20Concrete
end Source
end ConnesWeilRH
