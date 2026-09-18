/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.SoninCarrierEigenvectorBridge
import ConnesWeilRH.Source.CC20Concrete.CCM24ArchimedeanCarrier

/-!
# The Hardy--Titchmarsh involution is a reflection of a multiplier conjugate

The committed definition (`CCM24HardyTitchmarsh.lean:331`) reads

  `H = F⁻¹ ∘L M_m ∘L R ∘L F`,

with `R` the log-Fourier reflection and `F` the whole-line Fourier transform.
The committed covariance `F⁻¹ = R ∘L F`
(`CCM24ArchimedeanCarrier.lean:863`) removes the reflection from the middle:
writing `U_m := F ∘L M_m ∘L F⁻¹` for the multiplier transported to the
logarithmic domain,

  `H = R ∘L U_m`,   `H u = R (U_m u)`.

Consequences recorded here: the fixed/anti-fixed equations of `H` become
`U_m u = ± R u` (the self-reflection form of the multiplier conjugate, i.e.
the Toeplitz/de Branges shape of records 1590/1621), and the carrier is the set
of radial `u` whose multiplier conjugate lies in the reflected radial
subspace.  The eigenvector bridge of record 1621 is restated in this closed
form.  No existence statement is proved: the carrier's nonemptiness stays the
open analytic obligation (law F33) and RH is not claimed.
-/

namespace ConnesWeilRH
namespace Dev
namespace SoninCarrierMultiplierConjugate

open MeasureTheory
open ConnesWeilRH.Source.CC20Concrete
open ConnesWeilRH.Dev.SoninWindowWitness
open ConnesWeilRH.Dev.SoninCarrierEigenvectorBridge

/-- Involution form of the committed reflection law, for the reflection
*equivalence* (`ccm24LogSpectralReflection_involutive` is stated for the
underlying linear isometry). -/
theorem ccm24LogSpectralReflection_apply_involutive
    (u : cc20GlobalLogCrossingL2) :
    ccm24LogSpectralReflection (ccm24LogSpectralReflection u) = u :=
  ccm24LogSpectralReflection_involutive u

/-- The committed archimedean scattering multiplier transported to the
logarithmic domain: `F ∘L M_m ∘L F⁻¹`. -/
noncomputable def archimedeanMultiplierConjugate :
    cc20GlobalLogCrossingL2 ≃ₗᵢ[ℂ] cc20GlobalLogCrossingL2 :=
  (Lp.fourierTransformₗᵢ ℝ ℂ).symm.trans
    (ccm24ArchimedeanScatteringMultiplier.trans (Lp.fourierTransformₗᵢ ℝ ℂ))

theorem archimedeanMultiplierConjugate_apply
    (u : cc20GlobalLogCrossingL2) :
    archimedeanMultiplierConjugate u =
      Lp.fourierTransformₗᵢ ℝ ℂ (ccm24ArchimedeanScatteringMultiplier
        ((Lp.fourierTransformₗᵢ ℝ ℂ).symm u)) :=
  rfl

/-- Pointwise form of the factorization: the Hardy--Titchmarsh involution is
the reflection applied to the multiplier conjugate. -/
theorem ccm24ArchimedeanHardyTitchmarsh_apply_eq_reflection_multiplierConjugate
    (u : cc20GlobalLogCrossingL2) :
    ccm24ArchimedeanHardyTitchmarsh u =
      ccm24LogSpectralReflection (archimedeanMultiplierConjugate u) := by
  rw [archimedeanMultiplierConjugate_apply]
  simp only [ccm24ArchimedeanHardyTitchmarsh, LinearIsometryEquiv.trans_apply]
  rw [← ccm24_fourierInv_eq_reflection_fourier u,
    ← ccm24_fourierInv_eq_reflection_fourier
      (ccm24ArchimedeanScatteringMultiplier
        ((Lp.fourierTransformₗᵢ ℝ ℂ).symm u))]

/-- Operator form of the factorization: `H = R ∘L U_m`. -/
theorem ccm24ArchimedeanHardyTitchmarsh_eq_multiplierConjugate_trans_reflection :
    ccm24ArchimedeanHardyTitchmarsh =
      archimedeanMultiplierConjugate.trans ccm24LogSpectralReflection :=
  LinearIsometryEquiv.ext fun u => by
    rw [LinearIsometryEquiv.trans_apply]
    exact ccm24ArchimedeanHardyTitchmarsh_apply_eq_reflection_multiplierConjugate u

/-- The multiplier conjugate of a vector is the reflection of its
Hardy--Titchmarsh image: `U_m u = R (H u)`. -/
theorem archimedeanMultiplierConjugate_eq_reflection_apply
    (u : cc20GlobalLogCrossingL2) :
    archimedeanMultiplierConjugate u =
      ccm24LogSpectralReflection (ccm24ArchimedeanHardyTitchmarsh u) := by
  rw [ccm24ArchimedeanHardyTitchmarsh_apply_eq_reflection_multiplierConjugate u,
    ccm24LogSpectralReflection_apply_involutive]

/-- Fixed points of the involution are the self-reflected vectors under the
multiplier conjugate: `H u = u ↔ U_m u = R u`. -/
theorem hardyTitchmarsh_fixed_iff (u : cc20GlobalLogCrossingL2) :
    ccm24ArchimedeanHardyTitchmarsh u = u ↔
      archimedeanMultiplierConjugate u = ccm24LogSpectralReflection u := by
  rw [ccm24ArchimedeanHardyTitchmarsh_apply_eq_reflection_multiplierConjugate u]
  constructor
  · intro h
    have h2 := congrArg ccm24LogSpectralReflection h
    rwa [ccm24LogSpectralReflection_apply_involutive] at h2
  · intro h
    rw [h, ccm24LogSpectralReflection_apply_involutive]

/-- Anti-fixed points: `H u = -u ↔ U_m u = -R u`. -/
theorem hardyTitchmarsh_antifixed_iff (u : cc20GlobalLogCrossingL2) :
    ccm24ArchimedeanHardyTitchmarsh u = -u ↔
      archimedeanMultiplierConjugate u = -ccm24LogSpectralReflection u := by
  rw [ccm24ArchimedeanHardyTitchmarsh_apply_eq_reflection_multiplierConjugate u]
  constructor
  · intro h
    have h2 := congrArg ccm24LogSpectralReflection h
    rw [map_neg] at h2
    rw [ccm24LogSpectralReflection_apply_involutive] at h2
    exact h2
  · intro h
    rw [h, map_neg, ccm24LogSpectralReflection_apply_involutive]

/-- The carrier is the set of radial vectors whose multiplier conjugate lies
in the reflected radial subspace. -/
theorem mem_sonin_iff_radial_and_multiplierConjugate_mem_map
    (lambda : CCM24SoninScale) (u : cc20GlobalLogCrossingL2) :
    u ∈ ccm24ArchimedeanSoninClosedSubspace lambda ↔
      u ∈ ccm24LogRadialSupportClosedSubspace lambda ∧
        archimedeanMultiplierConjugate u ∈
          Submodule.map ccm24LogSpectralReflection.toLinearEquiv.toLinearMap
            (ccm24LogRadialSupportClosedSubspace lambda).toSubmodule := by
  constructor
  · intro hmem
    have hR := (Submodule.mem_inf.mp hmem).1
    have hH := (Submodule.mem_inf.mp hmem).2
    exact ⟨hR, ccm24ArchimedeanHardyTitchmarsh u, hH,
      (archimedeanMultiplierConjugate_eq_reflection_apply u).symm⟩
  · rintro ⟨hR, v, hv, hvU⟩
    have hEq : ccm24LogSpectralReflection (archimedeanMultiplierConjugate u) = v := by
      rw [← hvU]
      exact ccm24LogSpectralReflection_apply_involutive v
    refine Submodule.mem_inf.mpr ⟨hR,
      (mem_ccm24ArchimedeanFourierSupportClosedSubspace_iff lambda u).mpr ?_⟩
    rw [ccm24ArchimedeanHardyTitchmarsh_apply_eq_reflection_multiplierConjugate u,
      hEq]
    exact hv

/-- Record 1621's eigenvector bridge in closed multiplier-conjugate form: the
carrier is nontrivial iff there is a nonzero radial vector whose multiplier
conjugate is its own reflection up to sign. -/
theorem archimedeanSoninCarrier_nontrivial_iff_multiplierConjugate_reflection
    (lambda : CCM24SoninScale) :
    archimedeanSoninCarrier_nontrivial lambda ↔
      ∃ u : cc20GlobalLogCrossingL2, u ≠ 0 ∧
        u ∈ ccm24LogRadialSupportClosedSubspace lambda ∧
          (archimedeanMultiplierConjugate u = ccm24LogSpectralReflection u ∨
            archimedeanMultiplierConjugate u = -ccm24LogSpectralReflection u) := by
  rw [archimedeanSoninCarrier_nontrivial_iff_radial_eigenvector]
  constructor
  · rintro ⟨u, hu, hR, hfix | hanti⟩
    · exact ⟨u, hu, hR, Or.inl ((hardyTitchmarsh_fixed_iff u).1 hfix)⟩
    · exact ⟨u, hu, hR, Or.inr ((hardyTitchmarsh_antifixed_iff u).1 hanti)⟩
  · rintro ⟨u, hu, hR, h | h⟩
    · exact ⟨u, hu, hR, Or.inl ((hardyTitchmarsh_fixed_iff u).2 h)⟩
    · exact ⟨u, hu, hR, Or.inr ((hardyTitchmarsh_antifixed_iff u).2 h)⟩

end SoninCarrierMultiplierConjugate
end Dev
end ConnesWeilRH
