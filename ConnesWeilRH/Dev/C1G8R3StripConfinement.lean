/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3CompositeBoundaryEnergy

/-!
# Strip confinement of the radial defect (record 1575 section 3.3)

For `E_λ` the radial support projection at scale `λ` and `E_{λ''}` the radial
projection at the wider scale `λ'' = λ·e^{-s}` (`s ≥ 0`), every operator `M`
whose columns are supported on the wider half-line `[log λ - s, ∞)` has radial
defect at scale `λ` confined to the finite strip `[log λ - s, log λ)`:

  `(1 - E_λ) ∘L M = (E_{λ''} - E_λ) ∘L M`

                    `= T(-log λ) ∘L π_[-s,0] ∘L T(log λ) ∘L M`.

The shifts of wide-supported factors add under composition, which turns the
support ledger of record 1575 section 2 (one `log q` per adjoint Euler
transport, total `Σ log q`) into a Lean chain.  The consumer-facing corollary
is the signed B4 form of record 1599: under the Hardy wide-support certificate
`E_{λ''} ∘L H ∘L M ∘L J = H ∘L M ∘L J`, the defect of the Hardy column
`H ∘L M ∘L J` is exactly the finite strip projection, so the reflected
half-line tail is a finite-strip object and not an unbounded remainder.

No estimate, no summability, and no sign statement is proved here; (★), B4,
ρ5, and RH remain open.
-/

namespace ConnesWeilRH
namespace Dev

open MeasureTheory
open Source
open Source.CC20Concrete
open Source.CC20Concrete.ELambdaProjector
open Source.CCM25Concrete
open Source.CCM25Concrete.CCM24FiniteSProjectionTrace
open Source.CCM25Concrete.CCM24FiniteSGramResponse
open Source.CCM25Concrete.CCM24FiniteSBandTrace
open Source.CCM25Concrete.CCM24FiniteSActualSchurCascade
open Source.CCM25Concrete.CCM24FiniteSCompletedJuliaAmbientDefectFactorization
open Source.CCM25Concrete.CCM24RadialBoundaryPairTransport
open Source.CCM25Concrete.SelectedCrossingOperatorBridge
open scoped InnerProductSpace

local notation "Carrier" => finiteSCarrier

noncomputable local instance stripConfinementSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! ## The scale algebra -/

/-- Iterating the wide radial scale adds the shifts. -/
theorem wideRadialScale_add (lambda : CCM24SoninScale) (s₁ s₂ : ℝ) :
    wideRadialScale (wideRadialScale lambda s₁) s₂ =
      wideRadialScale lambda (s₁ + s₂) := by
  apply Subtype.ext
  change (lambda.1 * Real.exp (-s₁)) * Real.exp (-s₂) =
    lambda.1 * Real.exp (-(s₁ + s₂))
  rw [mul_assoc, ← Real.exp_add]
  ring_nf

/-- Composition of wide-supported factors: the certificate of the outer
factor widens to the sum.  The radial subspaces are nested (a wider scale
gives a larger half-line support), so `M₁ ∘L M₂` already inherits the
certificate of `M₁` alone; the sum form is the shape used by the strip
ledger of record 1575 section 2, where the strip statements are indexed by
the accumulated shift (one `log q` per adjoint Euler transport). -/
theorem wideRadial_support_comp
    (lambda : CCM24SoninScale) (s₁ s₂ : ℝ) (hs₂ : 0 ≤ s₂)
    (M₁ M₂ : Carrier →L[ℂ] Carrier)
    (h₁ : radialSupportProjection (wideRadialScale lambda s₁) ∘L M₁ = M₁) :
    radialSupportProjection (wideRadialScale lambda (s₁ + s₂)) ∘L
        (M₁ ∘L M₂) = M₁ ∘L M₂ := by
  have hle : (wideRadialScale (wideRadialScale lambda s₁) s₂).1 ≤
      (wideRadialScale lambda s₁).1 := by
    change (lambda.1 * Real.exp (-s₁)) * Real.exp (-s₂) ≤
      lambda.1 * Real.exp (-s₁)
    calc
      (lambda.1 * Real.exp (-s₁)) * Real.exp (-s₂)
          ≤ (lambda.1 * Real.exp (-s₁)) * 1 :=
            mul_le_mul_of_nonneg_left
              (Real.exp_le_one_iff.mpr (by linarith))
              (le_of_lt (mul_pos lambda.2 (Real.exp_pos (-s₁))))
      _ = lambda.1 * Real.exp (-s₁) := by ring
  have hproj : radialSupportProjection
      (wideRadialScale (wideRadialScale lambda s₁) s₂) ∘L
        radialSupportProjection (wideRadialScale lambda s₁) =
      radialSupportProjection (wideRadialScale lambda s₁) :=
    radialProjector_comp_of_le (wideRadialScale (wideRadialScale lambda s₁) s₂) hle
  have hEsum : radialSupportProjection
      (wideRadialScale (wideRadialScale lambda s₁) s₂) ∘L M₁ = M₁ := by
    calc
      radialSupportProjection (wideRadialScale (wideRadialScale lambda s₁) s₂) ∘L M₁
          = radialSupportProjection (wideRadialScale (wideRadialScale lambda s₁) s₂) ∘L
              (radialSupportProjection (wideRadialScale lambda s₁) ∘L M₁) := by
            rw [h₁]
      _ = (radialSupportProjection (wideRadialScale (wideRadialScale lambda s₁) s₂) ∘L
              radialSupportProjection (wideRadialScale lambda s₁)) ∘L M₁ := by
            rw [← ContinuousLinearMap.comp_assoc]
      _ = radialSupportProjection (wideRadialScale lambda s₁) ∘L M₁ := by rw [hproj]
      _ = M₁ := h₁
  rw [← wideRadialScale_add]
  calc
    radialSupportProjection (wideRadialScale (wideRadialScale lambda s₁) s₂) ∘L
        (M₁ ∘L M₂)
        = (radialSupportProjection (wideRadialScale (wideRadialScale lambda s₁) s₂) ∘L
            M₁) ∘L M₂ := by
          rw [← ContinuousLinearMap.comp_assoc]
    _ = M₁ ∘L M₂ := by rw [hEsum]

/-! ## The strip-confinement identity -/

/-- Record 1575 section 3.3, operator form: every radial defect of a
wide-supported operator is the difference of the two radial projections. -/
theorem radialComplement_comp_eq_wideProjection_sub
    (lambda : CCM24SoninScale) (s : ℝ)
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    (M : G →L[ℂ] Carrier)
    (hwide : radialSupportProjection (wideRadialScale lambda s) ∘L M = M) :
    (ContinuousLinearMap.id ℂ Carrier - radialSupportProjection lambda) ∘L M =
      (radialSupportProjection (wideRadialScale lambda s) -
        radialSupportProjection lambda) ∘L M := by
  apply ContinuousLinearMap.ext
  intro u
  have hwideAt := DFunLike.congr_fun hwide u
  simp only [ContinuousLinearMap.comp_apply] at hwideAt ⊢
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]
  rw [hwideAt]

/-- Record 1575 section 3.3, strip form: the same defect is the translated
interval projection on the finite strip `[log λ - s, log λ)`. -/
theorem radialComplement_comp_eq_stripProjection
    (lambda : CCM24SoninScale) (s : ℝ) (hs : 0 ≤ s)
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    (M : G →L[ℂ] Carrier)
    (hwide : radialSupportProjection (wideRadialScale lambda s) ∘L M = M) :
    (ContinuousLinearMap.id ℂ Carrier - radialSupportProjection lambda) ∘L M =
      (cc20GlobalLogTranslation (-(Real.log lambda))).toContinuousLinearMap ∘L
        kernelIntervalProjection (-s) 0 0 ∘L
          (cc20GlobalLogTranslation (Real.log lambda)).toContinuousLinearMap ∘L
          M := by
  rw [radialComplement_comp_eq_wideProjection_sub lambda s M hwide,
    radialProjection_sub_eq_translatedInterval lambda s hs]
  simp only [ContinuousLinearMap.comp_assoc]

/-- Source-column form of the strip identity, matching the wide-support
hypothesis shape of the committed composite consumers: the defect of the
column `M ∘L J` is the finite strip applied to that same column. -/
theorem radialComplement_comp_comp_eq_stripProjection
    (lambda : CCM24SoninScale) (s : ℝ) (hs : 0 ≤ s)
    (M : Carrier →L[ℂ] Carrier)
    (hwide : radialSupportProjection (wideRadialScale lambda s) ∘L M ∘L
        sourceInclusion lambda = M ∘L sourceInclusion lambda) :
    ((ContinuousLinearMap.id ℂ Carrier - radialSupportProjection lambda) ∘L
        M) ∘L sourceInclusion lambda =
      ((cc20GlobalLogTranslation (-(Real.log lambda))).toContinuousLinearMap ∘L
        kernelIntervalProjection (-s) 0 0 ∘L
          (cc20GlobalLogTranslation (Real.log lambda)).toContinuousLinearMap ∘L
          M) ∘L sourceInclusion lambda :=
  radialComplement_comp_eq_stripProjection lambda s hs
    (M ∘L sourceInclusion lambda) hwide

/-- Vector form: a vector already supported on the wider half-line has
radial defect confined to the finite strip. -/
theorem radialComplement_apply_eq_strip_of_mem_wideRadial
    (lambda : CCM24SoninScale) (s : ℝ) (hs : 0 ≤ s)
    {u : Carrier}
    (hu : u ∈ ccm24LogRadialSupportClosedSubspace (wideRadialScale lambda s)) :
    (ContinuousLinearMap.id ℂ Carrier - radialSupportProjection lambda) u =
      (cc20GlobalLogTranslation (-(Real.log lambda))).toContinuousLinearMap
        (kernelIntervalProjection (-s) 0 0
          ((cc20GlobalLogTranslation (Real.log lambda)).toContinuousLinearMap
            u)) := by
  have hfixed : radialSupportProjection (wideRadialScale lambda s) u = u :=
    (ccm24LogRadialSupportProjection_eq_self_iff
      (wideRadialScale lambda s) u).2 hu
  have hsub := DFunLike.congr_fun
    (radialProjection_sub_eq_translatedInterval lambda s hs) u
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply]
    at hsub
  calc
    (ContinuousLinearMap.id ℂ Carrier - radialSupportProjection lambda) u =
        radialSupportProjection (wideRadialScale lambda s) u -
          radialSupportProjection lambda u := by
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
        hfixed]
    _ = (cc20GlobalLogTranslation (-(Real.log lambda))).toContinuousLinearMap
        (kernelIntervalProjection (-s) 0 0
          ((cc20GlobalLogTranslation (Real.log lambda)).toContinuousLinearMap
            u)) := hsub

/-! ## Instances on the committed ambient columns -/

/-- The committed one-prime ambient loss column has radial defect confined to
the strip of width exactly `log p`. -/
theorem suffixEulerFrameAmbientLossColumn_radialDefect_eq_strip
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    (ContinuousLinearMap.id ℂ Carrier - radialSupportProjection lambda) ∘L
        suffixEulerFrameAmbientLossColumn lambda p S =
      (cc20GlobalLogTranslation (-(Real.log lambda))).toContinuousLinearMap ∘L
        kernelIntervalProjection (-(Real.log p)) 0 0 ∘L
          (cc20GlobalLogTranslation (Real.log lambda)).toContinuousLinearMap ∘L
          suffixEulerFrameAmbientLossColumn lambda p S := by
  have hlogp : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast p.property.le)
  exact radialComplement_comp_eq_stripProjection lambda (Real.log p) hlogp
    (suffixEulerFrameAmbientLossColumn lambda p S)
    (suffixEulerFrameAmbientLossColumn_wideRadialSupport lambda p S)

/-- The committed Schur boundary dagger has radial defect confined to the
strip of width exactly `log p`. -/
theorem suffixEulerFrameSchurStep_boundaryDagger_radialDefect_eq_strip
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    (ContinuousLinearMap.id ℂ Carrier - radialSupportProjection lambda) ∘L
        (suffixEulerFrameSchurStep lambda p S).boundaryDagger =
      (cc20GlobalLogTranslation (-(Real.log lambda))).toContinuousLinearMap ∘L
        kernelIntervalProjection (-(Real.log p)) 0 0 ∘L
          (cc20GlobalLogTranslation (Real.log lambda)).toContinuousLinearMap ∘L
          (suffixEulerFrameSchurStep lambda p S).boundaryDagger := by
  have hlogp : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast p.property.le)
  exact radialComplement_comp_eq_stripProjection lambda (Real.log p) hlogp
    (suffixEulerFrameSchurStep lambda p S).boundaryDagger
    (suffixEulerFrameSchurStep_boundaryDagger_wideRadialSupport lambda p S)

/-! ## The signed B4 form -/

/-- The signed reflected-half-line reading of record 1599: under the Hardy
wide-support certificate used by the committed gap-leg consumers, the radial
defect of the Hardy column `H ∘L M` is exactly the finite strip projection.
The reflected tail is therefore a finite-strip object; no decay statement is
made here. -/
theorem hardyColumn_radialDefect_eq_strip_of_wideHardySupport
    (lambda : CCM24SoninScale) (s : ℝ) (hs : 0 ≤ s)
    (M : Carrier →L[ℂ] Carrier)
    (hwideHT : radialSupportProjection (wideRadialScale lambda s) ∘L
        archimedeanHardyTitchmarshOperator ∘L M ∘L sourceInclusion lambda =
      archimedeanHardyTitchmarshOperator ∘L M ∘L sourceInclusion lambda) :
    ((ContinuousLinearMap.id ℂ Carrier - radialSupportProjection lambda) ∘L
        archimedeanHardyTitchmarshOperator ∘L M) ∘L sourceInclusion lambda =
      ((cc20GlobalLogTranslation (-(Real.log lambda))).toContinuousLinearMap ∘L
        kernelIntervalProjection (-s) 0 0 ∘L
          (cc20GlobalLogTranslation (Real.log lambda)).toContinuousLinearMap ∘L
          archimedeanHardyTitchmarshOperator ∘L M) ∘L
        sourceInclusion lambda :=
  radialComplement_comp_comp_eq_stripProjection lambda s hs
    (archimedeanHardyTitchmarshOperator ∘L M) hwideHT

end Dev
end ConnesWeilRH
