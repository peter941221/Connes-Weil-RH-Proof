/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.CCM24LogRadialSupport
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.MeasureTheory.Function.Holder

/-!
# The archimedean Hardy--Titchmarsh transform on the logarithmic carrier

CCM24 uses the even additive Fourier transform, transported through the
half-density map `w_infinity` and the logarithmic coordinate. In the
Plancherel coordinate used by Mathlib this is the unitary operator

`F⁻¹ (m(2 * pi * xi) * (F u)(-xi))`,

where

`m(s) = Gamma_R(1 / 2 - I * s) / Gamma_R(1 / 2 + I * s)`.

For real `s`, the denominator is the complex conjugate of the numerator.
The definition below uses that conjugate form directly, making the unit
modulus needed for the `L2` multiplier explicit. This is the actual
Hardy--Titchmarsh/scattering transform, not Mathlib's additive Fourier
transform by itself.
-/

namespace ConnesWeilRH
namespace Source
namespace CC20Concrete

open MeasureTheory
open scoped ComplexConjugate ENNReal

/-- The archimedean local factor on Mathlib's normalized log-Fourier
frequency. Mathlib uses `exp (-2 * pi * I * t * xi)`, hence CCM24's spectral
variable is `s = 2 * pi * xi`. -/
noncomputable def ccm24ArchimedeanFactor (xi : ℝ) : ℂ :=
  Complex.Gammaℝ
    ((1 / 2 : ℂ) - Complex.I * (2 * Real.pi * xi : ℝ))

theorem ccm24ArchimedeanFactor_ne_zero (xi : ℝ) :
    ccm24ArchimedeanFactor xi ≠ 0 := by
  apply Complex.Gammaℝ_ne_zero_of_re_pos
  simp

/-- Deligne's real archimedean Gamma factor respects complex conjugation
away from no point: its defining Gamma and positive-real complex power both
respect conjugation. -/
theorem ccm24_GammaR_conj (z : ℂ) :
    Complex.Gammaℝ (conj z) = conj (Complex.Gammaℝ z) := by
  rw [Complex.Gammaℝ_def, Complex.Gammaℝ_def, map_mul]
  congr 1
  · have harg : Complex.arg (Real.pi : ℂ) ≠ Real.pi := by
      rw [Complex.arg_ofReal_of_nonneg Real.pi_pos.le]
      exact ne_of_lt Real.pi_pos
    calc
      (Real.pi : ℂ) ^ (-conj z / 2) =
          (Real.pi : ℂ) ^ conj (-z / 2) := by
            congr 1
            rw [RCLike.conj_div, map_neg, RCLike.conj_ofNat]
      _ = conj (conj (Real.pi : ℂ) ^ (-z / 2)) :=
        Complex.cpow_conj (Real.pi : ℂ) (-z / 2) harg
      _ = conj ((Real.pi : ℂ) ^ (-z / 2)) := by simp
  · rw [← Complex.Gamma_conj]
    congr 1
    rw [RCLike.conj_div, RCLike.conj_ofNat]

theorem ccm24ArchimedeanFactor_neg (xi : ℝ) :
    ccm24ArchimedeanFactor (-xi) = conj (ccm24ArchimedeanFactor xi) := by
  rw [ccm24ArchimedeanFactor, ccm24ArchimedeanFactor,
    ← ccm24_GammaR_conj]
  congr 1
  apply Complex.ext <;> simp

theorem continuous_ccm24ArchimedeanFactor :
    Continuous ccm24ArchimedeanFactor := by
  rw [continuous_iff_continuousAt]
  intro xi
  change ContinuousAt
    (fun x : ℝ =>
      (Real.pi : ℂ) ^
          (-((1 / 2 : ℂ) - Complex.I * (2 * Real.pi * x : ℝ)) / 2) *
        Complex.Gamma
          (((1 / 2 : ℂ) - Complex.I * (2 * Real.pi * x : ℝ)) / 2)) xi
  apply ContinuousAt.mul
  · exact (continuousAt_const_cpow
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)).comp (by fun_prop)
  · apply (Complex.continuousAt_Gamma _ (fun m h => by
        have hre := congrArg Complex.re h
        simp at hre
        have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
        have hquarter : (0 : ℝ) < 2⁻¹ / 2 := by positivity
        linarith)).comp
    fun_prop

/-- The unit-modulus archimedean scattering phase. The conjugate denominator
is `Gamma_R(1 / 2 + I * s)` for real `s`. -/
noncomputable def ccm24ArchimedeanScatteringPhase (xi : ℝ) : ℂ :=
  ccm24ArchimedeanFactor xi /
    conj (ccm24ArchimedeanFactor xi)

theorem norm_ccm24ArchimedeanScatteringPhase (xi : ℝ) :
    ‖ccm24ArchimedeanScatteringPhase xi‖ = 1 := by
  rw [ccm24ArchimedeanScatteringPhase, norm_div, Complex.norm_conj]
  exact div_self (norm_ne_zero_iff.mpr
    (ccm24ArchimedeanFactor_ne_zero xi))

theorem continuous_ccm24ArchimedeanScatteringPhase :
    Continuous ccm24ArchimedeanScatteringPhase := by
  exact continuous_ccm24ArchimedeanFactor.div
    (Complex.continuous_conj.comp continuous_ccm24ArchimedeanFactor)
    (fun xi => by simpa using ccm24ArchimedeanFactor_ne_zero xi)

theorem ccm24ArchimedeanScatteringPhase_conj_mul (xi : ℝ) :
    conj (ccm24ArchimedeanScatteringPhase xi) *
        ccm24ArchimedeanScatteringPhase xi = 1 := by
  rw [← Complex.normSq_eq_conj_mul_self,
    Complex.normSq_eq_norm_sq,
    norm_ccm24ArchimedeanScatteringPhase]
  norm_num

theorem ccm24ArchimedeanScatteringPhase_mul_conj (xi : ℝ) :
        ccm24ArchimedeanScatteringPhase xi *
        conj (ccm24ArchimedeanScatteringPhase xi) = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq,
    norm_ccm24ArchimedeanScatteringPhase]
  norm_num

theorem ccm24ArchimedeanScatteringPhase_neg (xi : ℝ) :
    ccm24ArchimedeanScatteringPhase (-xi) =
      conj (ccm24ArchimedeanScatteringPhase xi) := by
  rw [ccm24ArchimedeanScatteringPhase,
    ccm24ArchimedeanScatteringPhase,
    ccm24ArchimedeanFactor_neg, RCLike.conj_div]

/-- Read the phase in the paper's local-factor orientation:
`Gamma_R(1/2-is) / Gamma_R(1/2+is)`. -/
theorem ccm24ArchimedeanScatteringPhase_eq_factor_ratio (xi : ℝ) :
    ccm24ArchimedeanScatteringPhase xi =
      ccm24ArchimedeanFactor xi / ccm24ArchimedeanFactor (-xi) := by
  rw [ccm24ArchimedeanScatteringPhase,
    ccm24ArchimedeanFactor_neg]

theorem memLp_ccm24ArchimedeanScatteringPhase :
    MemLp ccm24ArchimedeanScatteringPhase ∞ (volume : Measure ℝ) :=
  memLp_top_of_bound
    continuous_ccm24ArchimedeanScatteringPhase.aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun xi =>
      (norm_ccm24ArchimedeanScatteringPhase xi).le)

theorem memLp_conj_ccm24ArchimedeanScatteringPhase :
    MemLp (fun xi => conj (ccm24ArchimedeanScatteringPhase xi)) ∞
      (volume : Measure ℝ) :=
  memLp_top_of_bound
    (Complex.continuous_conj.comp
      continuous_ccm24ArchimedeanScatteringPhase).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun xi => by
      rw [Complex.norm_conj, norm_ccm24ArchimedeanScatteringPhase])

noncomputable def ccm24ArchimedeanScatteringPhaseLp :
    Lp ℂ ∞ (volume : Measure ℝ) :=
  memLp_ccm24ArchimedeanScatteringPhase.toLp
    ccm24ArchimedeanScatteringPhase

noncomputable def ccm24ArchimedeanScatteringPhaseInvLp :
    Lp ℂ ∞ (volume : Measure ℝ) :=
  memLp_conj_ccm24ArchimedeanScatteringPhase.toLp
    (fun xi => conj (ccm24ArchimedeanScatteringPhase xi))

theorem ccm24ArchimedeanScatteringPhaseLp_coeFn :
    (ccm24ArchimedeanScatteringPhaseLp : ℝ → ℂ) =ᵐ[volume]
      ccm24ArchimedeanScatteringPhase :=
  memLp_ccm24ArchimedeanScatteringPhase.coeFn_toLp

theorem ccm24ArchimedeanScatteringPhaseInvLp_coeFn :
    (ccm24ArchimedeanScatteringPhaseInvLp : ℝ → ℂ) =ᵐ[volume]
      fun xi => conj (ccm24ArchimedeanScatteringPhase xi) :=
  memLp_conj_ccm24ArchimedeanScatteringPhase.coeFn_toLp

/-- Multiplication by the actual archimedean scattering phase on the
log-Fourier `L2` carrier. -/
noncomputable def ccm24ArchimedeanScatteringMultiplierLinearEquiv :
    cc20GlobalLogCrossingL2 ≃ₗ[ℂ] cc20GlobalLogCrossingL2 where
  toFun u := ccm24ArchimedeanScatteringPhaseLp • u
  invFun u := ccm24ArchimedeanScatteringPhaseInvLp • u
  left_inv u := by
    rw [Lp.ext_iff]
    filter_upwards
      [Lp.coeFn_lpSMul (p := ∞) (q := 2) (r := 2)
        ccm24ArchimedeanScatteringPhaseInvLp
        (ccm24ArchimedeanScatteringPhaseLp • u),
       Lp.coeFn_lpSMul (p := ∞) (q := 2) (r := 2)
        ccm24ArchimedeanScatteringPhaseLp u,
       ccm24ArchimedeanScatteringPhaseLp_coeFn,
       ccm24ArchimedeanScatteringPhaseInvLp_coeFn] with
        xi hout hin hphase hphaseInv
    simp only [Pi.smul_apply'] at hout hin
    rw [hout, hin, hphase, hphaseInv]
    simp only [smul_eq_mul]
    rw [← mul_assoc, ccm24ArchimedeanScatteringPhase_conj_mul, one_mul]
  right_inv u := by
    rw [Lp.ext_iff]
    filter_upwards
      [Lp.coeFn_lpSMul (p := ∞) (q := 2) (r := 2)
        ccm24ArchimedeanScatteringPhaseLp
        (ccm24ArchimedeanScatteringPhaseInvLp • u),
       Lp.coeFn_lpSMul (p := ∞) (q := 2) (r := 2)
        ccm24ArchimedeanScatteringPhaseInvLp u,
       ccm24ArchimedeanScatteringPhaseLp_coeFn,
       ccm24ArchimedeanScatteringPhaseInvLp_coeFn] with
        xi hout hin hphase hphaseInv
    simp only [Pi.smul_apply'] at hout hin
    rw [hout, hin, hphase, hphaseInv]
    simp only [smul_eq_mul]
    rw [← mul_assoc, ccm24ArchimedeanScatteringPhase_mul_conj, one_mul]
  map_add' u v := Lp.add_smul ccm24ArchimedeanScatteringPhaseLp u v
  map_smul' c u := by
    exact (Lp.smul_comm (𝕜' := ℂ) (𝕜 := ℂ) (E := ℂ)
      (p := ∞) (q := 2) (r := 2) c
      ccm24ArchimedeanScatteringPhaseLp u).symm

theorem norm_ccm24ArchimedeanScatteringMultiplierLinearEquiv
    (u : cc20GlobalLogCrossingL2) :
    ‖ccm24ArchimedeanScatteringMultiplierLinearEquiv u‖ = ‖u‖ := by
  change ‖ccm24ArchimedeanScatteringPhaseLp • u‖ = ‖u‖
  rw [Lp.norm_def, Lp.norm_def]
  apply congrArg ENNReal.toReal
  apply eLpNorm_congr_norm_ae
  filter_upwards
    [Lp.coeFn_lpSMul (p := ∞) (q := 2) (r := 2)
      ccm24ArchimedeanScatteringPhaseLp u,
     ccm24ArchimedeanScatteringPhaseLp_coeFn] with xi hmul hphase
  rw [hmul, Pi.smul_apply', hphase, smul_eq_mul, norm_mul,
    norm_ccm24ArchimedeanScatteringPhase, one_mul]

noncomputable def ccm24ArchimedeanScatteringMultiplier :
    cc20GlobalLogCrossingL2 ≃ₗᵢ[ℂ] cc20GlobalLogCrossingL2 where
  toLinearEquiv := ccm24ArchimedeanScatteringMultiplierLinearEquiv
  norm_map' := norm_ccm24ArchimedeanScatteringMultiplierLinearEquiv

theorem ccm24ArchimedeanScatteringMultiplier_coeFn
    (u : cc20GlobalLogCrossingL2) :
    (ccm24ArchimedeanScatteringMultiplier u : ℝ → ℂ) =ᵐ[volume]
      fun xi => ccm24ArchimedeanScatteringPhase xi * u xi := by
  change ((ccm24ArchimedeanScatteringPhaseLp • u :
    cc20GlobalLogCrossingL2) : ℝ → ℂ) =ᵐ[volume]
      fun xi => ccm24ArchimedeanScatteringPhase xi * u xi
  filter_upwards
    [Lp.coeFn_lpSMul (p := ∞) (q := 2) (r := 2)
      ccm24ArchimedeanScatteringPhaseLp u,
     ccm24ArchimedeanScatteringPhaseLp_coeFn] with xi hmul hphase
  rw [hmul, Pi.smul_apply', hphase, smul_eq_mul]

/-- Reflection of the log-Fourier frequency `xi -> -xi`. -/
noncomputable def ccm24LogSpectralReflectionLinearIsometry :
    cc20GlobalLogCrossingL2 →ₗᵢ[ℂ] cc20GlobalLogCrossingL2 :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun xi : ℝ => -xi)
    (Measure.measurePreserving_neg volume)

theorem ccm24LogSpectralReflection_coeFn
    (u : cc20GlobalLogCrossingL2) :
    (ccm24LogSpectralReflectionLinearIsometry u : ℝ → ℂ) =ᵐ[volume]
      fun xi => u (-xi) :=
  Lp.coeFn_compMeasurePreserving u (Measure.measurePreserving_neg volume)

theorem ccm24LogSpectralReflection_involutive :
    Function.Involutive ccm24LogSpectralReflectionLinearIsometry := by
  intro u
  rw [Lp.ext_iff]
  have hinner := (Measure.measurePreserving_neg volume).quasiMeasurePreserving.ae_eq
    (ccm24LogSpectralReflection_coeFn u)
  filter_upwards
    [ccm24LogSpectralReflection_coeFn
      (ccm24LogSpectralReflectionLinearIsometry u), hinner] with xi hout hin
  rw [hout]
  simpa using hin

noncomputable def ccm24LogSpectralReflection :
    cc20GlobalLogCrossingL2 ≃ₗᵢ[ℂ] cc20GlobalLogCrossingL2 where
  toLinearEquiv := LinearEquiv.ofInvolutive
    ccm24LogSpectralReflectionLinearIsometry.toLinearMap
    ccm24LogSpectralReflection_involutive
  norm_map' := ccm24LogSpectralReflectionLinearIsometry.norm_map

theorem ccm24LogSpectralReflectionEquiv_coeFn
    (u : cc20GlobalLogCrossingL2) :
    (ccm24LogSpectralReflection u : ℝ → ℂ) =ᵐ[volume]
      fun xi => u (-xi) :=
  ccm24LogSpectralReflection_coeFn u

/-- The spectral operator `phi(xi) -> m(xi) * phi(-xi)` is an involution. -/
theorem ccm24ArchimedeanSpectralScattering_involutive
    (u : cc20GlobalLogCrossingL2) :
    ccm24ArchimedeanScatteringMultiplier
        (ccm24LogSpectralReflection
          (ccm24ArchimedeanScatteringMultiplier
            (ccm24LogSpectralReflection u))) = u := by
  rw [Lp.ext_iff]
  have hinnerMul :=
    (Measure.measurePreserving_neg volume).quasiMeasurePreserving.ae_eq
      (ccm24ArchimedeanScatteringMultiplier_coeFn
        (ccm24LogSpectralReflection u))
  have hinnerReflect :=
    (Measure.measurePreserving_neg volume).quasiMeasurePreserving.ae_eq
      (ccm24LogSpectralReflectionEquiv_coeFn u)
  filter_upwards
    [ccm24ArchimedeanScatteringMultiplier_coeFn
      (ccm24LogSpectralReflection
        (ccm24ArchimedeanScatteringMultiplier
          (ccm24LogSpectralReflection u))),
     ccm24LogSpectralReflectionEquiv_coeFn
      (ccm24ArchimedeanScatteringMultiplier
        (ccm24LogSpectralReflection u)),
     hinnerMul, hinnerReflect] with xi houterMul houterReflect
        hinnerMulAt hinnerReflectAt
  simp only [Function.comp_apply] at hinnerMulAt hinnerReflectAt
  rw [houterMul, houterReflect, hinnerMulAt, hinnerReflectAt]
  rw [ccm24ArchimedeanScatteringPhase_neg]
  ring_nf
  rw [ccm24ArchimedeanScatteringPhase_mul_conj]
  simp

/-- The concrete CCM24 archimedean Hardy--Titchmarsh transform on the common
logarithmic `L2` carrier. -/
noncomputable def ccm24ArchimedeanHardyTitchmarsh :
    cc20GlobalLogCrossingL2 ≃ₗᵢ[ℂ] cc20GlobalLogCrossingL2 :=
  (Lp.fourierTransformₗᵢ ℝ ℂ).trans
    (ccm24LogSpectralReflection.trans
      (ccm24ArchimedeanScatteringMultiplier.trans
        (Lp.fourierTransformₗᵢ ℝ ℂ).symm))

/-- Spectral readback of the concrete Hardy--Titchmarsh transform. This is
the exact `m(2*pi*xi) * phi(-xi)` formula. -/
theorem ccm24ArchimedeanHardyTitchmarsh_fourier_readback
    (u : cc20GlobalLogCrossingL2) :
    Lp.fourierTransformₗᵢ ℝ ℂ (ccm24ArchimedeanHardyTitchmarsh u) =
      ccm24ArchimedeanScatteringMultiplier
        (ccm24LogSpectralReflection (Lp.fourierTransformₗᵢ ℝ ℂ u)) := by
  simp [ccm24ArchimedeanHardyTitchmarsh]

/-- The concrete Hardy--Titchmarsh transform has square one, as the even
additive Fourier transform does. -/
theorem ccm24ArchimedeanHardyTitchmarsh_involutive
    (u : cc20GlobalLogCrossingL2) :
    ccm24ArchimedeanHardyTitchmarsh
        (ccm24ArchimedeanHardyTitchmarsh u) = u := by
  apply (Lp.fourierTransformₗᵢ ℝ ℂ).injective
  rw [ccm24ArchimedeanHardyTitchmarsh_fourier_readback,
    ccm24ArchimedeanHardyTitchmarsh_fourier_readback]
  exact ccm24ArchimedeanSpectralScattering_involutive
    (Lp.fourierTransformₗᵢ ℝ ℂ u)

/-- The actual source Fourier-support condition: the archimedean
Hardy--Titchmarsh transform vanishes below `log lambda`. -/
noncomputable def ccm24ArchimedeanFourierSupportClosedSubspace
    (lambda : CCM24SoninScale) :
    ClosedSubmodule ℂ cc20GlobalLogCrossingL2 :=
  ClosedSubmodule.comap
    ccm24ArchimedeanHardyTitchmarsh.toContinuousLinearEquiv.toContinuousLinearMap
    (ccm24LogRadialSupportClosedSubspace lambda)

theorem mem_ccm24ArchimedeanFourierSupportClosedSubspace_iff
    (lambda : CCM24SoninScale) (u : cc20GlobalLogCrossingL2) :
    u ∈ ccm24ArchimedeanFourierSupportClosedSubspace lambda ↔
      ccm24ArchimedeanHardyTitchmarsh u ∈
        ccm24LogRadialSupportClosedSubspace lambda :=
  Iff.rfl

/-- The complete archimedean Sonin space on the common log carrier. -/
noncomputable def ccm24ArchimedeanSoninClosedSubspace
    (lambda : CCM24SoninScale) :
    ClosedSubmodule ℂ cc20GlobalLogCrossingL2 :=
  ccm24LogRadialSupportClosedSubspace lambda ⊓
    ccm24ArchimedeanFourierSupportClosedSubspace lambda

end CC20Concrete
end Source
end ConnesWeilRH
