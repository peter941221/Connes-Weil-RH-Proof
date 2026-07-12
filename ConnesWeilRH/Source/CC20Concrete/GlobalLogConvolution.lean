/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.GlobalLogCrossing
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.MeasureTheory.Function.Holder

/-!
# Bounded convolution by one Schwartz kernel on global logarithmic L2

The operator is defined through Plancherel: Fourier transform, multiplication
by the bounded Fourier transform of the kernel, and inverse Fourier transform.
The final theorem identifies this extension with Schwartz convolution on the
dense Schwartz subspace.
-/

namespace ConnesWeilRH
namespace Source
namespace CC20Concrete

open MeasureTheory
open scoped FourierTransform

noncomputable def cc20FourierMultiplier
    (h : SchwartzMap ℝ ℂ) :
    cc20GlobalLogCrossingL2 →L[ℂ] cc20GlobalLogCrossingL2 := by
  let multiplier : Lp ℂ ⊤ (volume : Measure ℝ) := (𝓕 h).toLp ⊤
  let linear : cc20GlobalLogCrossingL2 →ₗ[ℂ] cc20GlobalLogCrossingL2 :=
    { toFun := fun u => multiplier • u
      map_add' := fun u v => Lp.add_smul multiplier u v
      map_smul' := fun c u => (Lp.smul_comm c multiplier u).symm }
  exact LinearMap.mkContinuous linear ‖multiplier‖ fun u =>
    Lp.norm_smul_le multiplier u

theorem cc20FourierMultiplier_apply
    (h : SchwartzMap ℝ ℂ) (u : cc20GlobalLogCrossingL2) :
    cc20FourierMultiplier h u = (𝓕 h).toLp ⊤ • u := by
  rfl

noncomputable def cc20GlobalLogConvolution
    (h : SchwartzMap ℝ ℂ) :
    cc20GlobalLogCrossingL2 →L[ℂ] cc20GlobalLogCrossingL2 :=
  let F : cc20GlobalLogCrossingL2 ≃ₗᵢ[ℂ] cc20GlobalLogCrossingL2 :=
    Lp.fourierTransformₗᵢ ℝ ℂ
  F.symm.toLinearIsometry.toContinuousLinearMap.comp
    ((cc20FourierMultiplier h).comp
      F.toLinearIsometry.toContinuousLinearMap)

theorem cc20GlobalLogConvolution_apply
    (h : SchwartzMap ℝ ℂ) (u : cc20GlobalLogCrossingL2) :
    cc20GlobalLogConvolution h u =
      𝓕⁻ (cc20FourierMultiplier h (𝓕 u)) := by
  change (Lp.fourierTransformₗᵢ ℝ ℂ).symm
      (cc20FourierMultiplier h ((Lp.fourierTransformₗᵢ ℝ ℂ) u)) = _
  rfl

theorem cc20FourierMultiplier_toLp
    (h g : SchwartzMap ℝ ℂ) :
    cc20FourierMultiplier h ((𝓕 g).toLp 2) =
      (SchwartzMap.pairing (ContinuousLinearMap.mul ℝ ℂ)
        (𝓕 h) (𝓕 g)).toLp 2 := by
  rw [cc20FourierMultiplier_apply]
  rw [Lp.ext_iff]
  filter_upwards
    [Lp.coeFn_lpSMul (r := 2) ((𝓕 h).toLp ⊤) ((𝓕 g).toLp 2),
      SchwartzMap.coeFn_toLp (𝓕 h) ⊤,
      SchwartzMap.coeFn_toLp (𝓕 g) 2,
      SchwartzMap.coeFn_toLp
        (SchwartzMap.pairing (ContinuousLinearMap.mul ℝ ℂ)
          (𝓕 h) (𝓕 g)) 2] with x hmul hh hg hpair
  rw [hmul]
  change (((𝓕 h).toLp ⊤ : ℝ → ℂ) x) *
      (((𝓕 g).toLp 2 : ℝ → ℂ) x) = _
  rw [hh, hg, hpair]
  rfl

theorem cc20GlobalLogConvolution_toLp
    (h g : SchwartzMap ℝ ℂ) :
    cc20GlobalLogConvolution h (g.toLp 2) =
      (SchwartzMap.convolution (ContinuousLinearMap.mul ℝ ℂ) h g).toLp 2 := by
  apply (Lp.fourierTransformₗᵢ ℝ ℂ).injective
  rw [cc20GlobalLogConvolution_apply]
  have hinv (v : cc20GlobalLogCrossingL2) :
      (Lp.fourierTransformₗᵢ ℝ ℂ) (𝓕⁻ v) = v := by
    change (Lp.fourierTransformₗᵢ ℝ ℂ)
        ((Lp.fourierTransformₗᵢ ℝ ℂ).symm v) = v
    exact (Lp.fourierTransformₗᵢ ℝ ℂ).apply_symm_apply v
  have hfourier (f : SchwartzMap ℝ ℂ) :
      (Lp.fourierTransformₗᵢ ℝ ℂ) (f.toLp 2) = (𝓕 f).toLp 2 := by
    change 𝓕 (f.toLp 2) = (𝓕 f).toLp 2
    exact SchwartzMap.toLp_fourier_eq f
  rw [hinv]
  rw [SchwartzMap.toLp_fourier_eq, cc20FourierMultiplier_toLp]
  rw [hfourier]
  rw [SchwartzMap.fourier_convolution]

end CC20Concrete
end Source
end ConnesWeilRH
