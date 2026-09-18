/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3DetectorRootSquareSum

/-!
# R3 leakage normal form at the doubled shift

The radial support is an upper half-line, so the raw selected convolution
root after that projection is not declared Hilbert--Schmidt.  This leaf instead
rewrites the exact leakage leg into the relative-motion defect of the doubled
shift alternating product.  It is an operator identity only; no Schatten
estimate or sign conclusion is hidden in it.
-/

namespace ConnesWeilRH
namespace Dev

open Source
open Source.CC20Concrete
open Source.CCM25Concrete
open Source.CCM25Concrete.CCM24FiniteSProjectionTrace
open Source.CCM25Concrete.CCM24FiniteSRootCompletedFirstJet
open Source.CCM25Concrete.CCM24FiniteSBandTrace
open Source.CCM25Concrete.CCM24RadialBoundaryPairTransport
open Source.CCM25Concrete.CCM24UnitScaleProlateAlignment
open Source.CCM25Concrete.SelectedCrossingOperatorBridge

local notation "Carrier" =>
  Source.CCM25Concrete.CCM24FiniteSProjectionTrace.finiteSCarrier
local notation "Op" => Carrier →L[ℂ] Carrier

theorem doubledShiftRadialClosedSubspace_eq_transportedHalfLineClosedRange
    (b : ℝ) :
    doubledShiftRadialClosedSubspace b =
      cc20TransportedHalfLineClosedRange
        (cc20GlobalLogTranslationEquiv (2 * b)) := by
  let e := cc20GlobalLogTranslationEquiv (2 * b)
  have hforward (v : Carrier) :
      e v = cc20GlobalLogTranslation (2 * b) v := by
    rfl
  have hE0 (v : Carrier) :
      v ∈ cc20PositiveHalfLineClosedRange ↔
        cc20PositiveHalfLineProjection v = v := by
    change v ∈ cc20PositiveHalfLineProjection.range ↔ _
    exact mem_range_iff_of_isIdempotentElem
      cc20PositiveHalfLineProjection
      cc20PositiveHalfLineProjection_isIdempotentElem v
  have htransport (v : Carrier) :
      v ∈ cc20TransportedHalfLineClosedRange e ↔
        cc20TransportedHalfLineProjection e v = v := by
    change v ∈ (cc20TransportedHalfLineProjection e).range ↔ _
    exact mem_range_iff_of_isIdempotentElem
      (cc20TransportedHalfLineProjection e)
      (cc20TransportedHalfLineProjection_isIdempotentElem e) v
  ext u
  constructor
  · intro hu
    have hpre := (ClosedSubmodule.mem_mapEquiv_iff
      (cc20GlobalLogTranslationEquiv (-2 * b)).toContinuousLinearEquiv
      cc20PositiveHalfLineClosedRange u).1 hu
    rw [globalTranslationContinuousEquiv_symm_apply] at hpre
    have hpre' : e u ∈ cc20PositiveHalfLineClosedRange := by
      rw [hforward u]
      have hparam : -(-2 * b) = 2 * b := by ring
      simpa only [hparam] using hpre
    apply (htransport u).mpr
    rw [cc20TransportedHalfLineProjection_apply]
    have hfixed : cc20PositiveHalfLineProjection (e u) = e u := by
      exact (hE0 (e u)).mp hpre'
    rw [hfixed]
    exact e.symm_apply_apply u
  · intro hu
    have hfixed := (htransport u).mp hu
    have hfixed' : cc20PositiveHalfLineProjection (e u) = e u := by
      have h := congrArg (fun v : Carrier => e v) hfixed
      simpa only [cc20TransportedHalfLineProjection_apply,
        e.apply_symm_apply] using h
    have hmember : e u ∈ cc20PositiveHalfLineClosedRange :=
      (hE0 (e u)).mpr hfixed'
    rw [hforward u] at hmember
    apply (ClosedSubmodule.mem_mapEquiv_iff
      (cc20GlobalLogTranslationEquiv (-2 * b)).toContinuousLinearEquiv
      cc20PositiveHalfLineClosedRange u).2
    rw [globalTranslationContinuousEquiv_symm_apply]
    have hparam : -(-2 * b) = 2 * b := by ring
    simpa only [hparam] using hmember

theorem doubledShiftRadialProjection_eq_translatedHalfLineProjection
    (b : ℝ) :
    doubledShiftRadialProjection b =
      (cc20GlobalLogTranslation (-2 * b)).toContinuousLinearMap ∘L
        cc20PositiveHalfLineProjection ∘L
          (cc20GlobalLogTranslation (2 * b)).toContinuousLinearMap := by
  let e := cc20GlobalLogTranslationEquiv (2 * b)
  have hrange :=
    doubledShiftRadialClosedSubspace_eq_transportedHalfLineClosedRange b
  have hprojection : doubledShiftRadialProjection b =
      cc20TransportedHalfLineProjection e := by
    apply ContinuousLinearMap.IsStarProjection.ext
      (doubledShiftRadialProjection_isStarProjection b)
      (cc20TransportedHalfLineProjection_isStarProjection e)
    rw [doubledShiftRadialProjection, Submodule.range_starProjection]
    change (doubledShiftRadialClosedSubspace b).toSubmodule =
      (cc20TransportedHalfLineClosedRange e).toSubmodule
    exact congrArg ClosedSubmodule.toSubmodule hrange
  rw [hprojection]
  unfold cc20TransportedHalfLineProjection
  have heq :
      (e : Carrier →L[ℂ] Carrier) =
        (cc20GlobalLogTranslation (2 * b)).toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro u
    rfl
  have hadj :
      (e : Carrier →L[ℂ] Carrier).adjoint =
        (cc20GlobalLogTranslation (-2 * b)).toContinuousLinearMap := by
    rw [heq]
    have h := cc20GlobalLogTranslation_neg_adjoint (-(2 * b))
    convert h using 1 <;> ring_nf
  rw [hadj]
  rfl

theorem rootConvolution_comp_globalLogTranslation
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) (b : ℝ) :
    rootConvolution owner ∘L
        (cc20GlobalLogTranslation b).toContinuousLinearMap =
      (cc20GlobalLogTranslation b).toContinuousLinearMap ∘L
        rootConvolution owner := by
  unfold rootConvolution
  simpa only [neg_neg] using
    (cc20GlobalLogConvolution_comp_translation_neg_eq owner.sourceTest (-b))

theorem sourceRootCompletedRightCommutatorLeftLeg_eq_translated_doubledShift_defect
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    sourceRootCompletedRightCommutatorLeftLeg owner lambda =
      (cc20GlobalLogTranslation (Real.log lambda)).toContinuousLinearMap ∘L
        rootConvolution owner ∘L
          (doubledShiftRadialProjection (Real.log lambda) -
            doubledShiftAlternatingProduct (Real.log lambda)) ∘L
            (cc20GlobalLogTranslation (-Real.log lambda)).toContinuousLinearMap := by
  let b : ℝ := Real.log lambda
  let U : ℝ → Op := fun a =>
    (cc20GlobalLogTranslation a).toContinuousLinearMap
  let C : Op := rootConvolution owner
  let P : Op := cc20PositiveHalfLineProjection
  let Q : Op := sourceFourierSupportProjection unitSoninScale
  let E : Op := U (-b) * P * U b
  let Qscale : Op := U b * Q * U (-b)
  let R : Op := U (-2 * b) * P * U (2 * b)
  have htrans (a c : ℝ) : U a * U c = U (a + c) := by
    dsimp [U]
    simpa only [ContinuousLinearMap.mul_def] using
      rawGlobalLogTranslation_comp a c
  have hzero : U 0 = (1 : Op) := by
    dsimp [U]
    simpa only [ContinuousLinearMap.one_def] using
      unitTranslation_zero_operator
  have htrans_eq (a c d : ℝ) (h : a + c = d) :
      U a * U c = U d := by
    rw [htrans a c, h]
  have h_b_mb : U b * U (-b) = (1 : Op) := by
    rw [htrans b (-b), show b + -b = 0 by ring, hzero]
  have h_mb_b : U (-b) * U b = (1 : Op) := by
    rw [htrans (-b) b, show -b + b = 0 by ring, hzero]
  have h_b_b : U b * U b = U (2 * b) := by
    exact htrans_eq b b (2 * b) (by ring)
  have h_mb_mb : U (-b) * U (-b) = U (-2 * b) := by
    exact htrans_eq (-b) (-b) (-2 * b) (by ring)
  have h_b_m2b : U b * U (-2 * b) = U (-b) := by
    exact htrans_eq b (-2 * b) (-b) (by ring)
  have h_2b_mb : U (2 * b) * U (-b) = U b := by
    exact htrans_eq (2 * b) (-b) b (by ring)
  have hC (a : ℝ) : U a * C = C * U a := by
    dsimp [U, C]
    simpa only [ContinuousLinearMap.mul_def] using
      (rootConvolution_comp_globalLogTranslation owner a).symm
  have hE : radialSupportProjection lambda = E := by
    simpa only [E, U, P, b, ContinuousLinearMap.mul_def,
      ContinuousLinearMap.comp_assoc] using
      (radialSupportProjection_eq_translation_conjugation lambda)
  have hQ : sourceFourierSupportProjection lambda = Qscale := by
    simpa only [Qscale, Q, U, b, logTranslation,
      ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc] using
      (sourceFourierSupportProjection_eq_scale_conjugate_of_zero_defects lambda)
  have hR : doubledShiftRadialProjection b = R := by
    simpa only [R, U, P, ContinuousLinearMap.mul_def,
      ContinuousLinearMap.comp_assoc] using
      (doubledShiftRadialProjection_eq_translatedHalfLineProjection b)
  have hAlt : doubledShiftAlternatingProduct b = R * Q * R := by
    unfold doubledShiftAlternatingProduct
    rw [hR]
  have hP : P * P = P := by
    dsimp [P]
    simpa only [ContinuousLinearMap.mul_def] using
      cc20PositiveHalfLineProjection_isIdempotentElem
  have hEid : E * E = E := by
    calc
      E * E = U (-b) * P * (U b * U (-b)) * P * U b := by
        dsimp [E]
        noncomm_ring
      _ = U (-b) * (P * P) * U b := by
        rw [h_b_mb]
        noncomm_ring
      _ = U (-b) * P * U b := by rw [hP]
      _ = E := by rfl
  have hRconj : U b * R * U (-b) = E := by
    calc
      U b * R * U (-b) =
          (U b * U (-2 * b)) * P *
            (U (2 * b) * U (-b)) := by
        dsimp [R]
        noncomm_ring
      _ = E := by
        rw [h_b_m2b, h_2b_mb]
  have hQconj : E * Qscale * E =
      U (-b) * P * U (2 * b) * Q * U (-2 * b) * P * U b := by
    calc
      E * Qscale * E =
          U (-b) * P * (U b * U b) * Q *
            (U (-b) * U (-b)) * P * U b := by
        dsimp [E, Qscale]
        noncomm_ring
      _ = U (-b) * P * U (2 * b) * Q *
            U (-2 * b) * P * U b := by
        rw [h_b_b, h_mb_mb]
  have hRQconj : U b * R * Q * R * U (-b) = E * Qscale * E := by
    calc
      U b * R * Q * R * U (-b) =
          (U b * U (-2 * b)) * P * U (2 * b) * Q *
            U (-2 * b) * P * (U (2 * b) * U (-b)) := by
        dsimp [R]
        noncomm_ring
      _ = U (-b) * P * U (2 * b) * Q *
            U (-2 * b) * P * U b := by
        rw [h_b_m2b, h_2b_mb]
      _ = E * Qscale * E := hQconj.symm
  have hfirst : U b * C * R * U (-b) = C * E := by
    calc
      U b * C * R * U (-b) = C * U b * R * U (-b) := by rw [hC b]
      _ = C * (U b * R * U (-b)) := by noncomm_ring
      _ = C * E := by rw [hRconj]
  have hsecond : U b * C * R * Q * R * U (-b) =
      C * E * Qscale * E := by
    calc
      U b * C * R * Q * R * U (-b) =
          C * (U b * R * Q * R * U (-b)) := by
            rw [hC b]
            noncomm_ring
      _ = C * (E * Qscale * E) := by rw [hRQconj]
      _ = C * E * Qscale * E := by noncomm_ring
  have hstar : C * E * (1 - Qscale) * E =
      U b * C * (R - R * Q * R) * U (-b) := by
    calc
      C * E * (1 - Qscale) * E =
          C * E * E - C * E * Qscale * E := by noncomm_ring
      _ = C * (E * E) - C * E * Qscale * E := by noncomm_ring
      _ = C * E - C * E * Qscale * E := by rw [hEid]
      _ = U b * C * R * U (-b) -
          U b * C * R * Q * R * U (-b) := by
        rw [hfirst, hsecond]
      _ = U b * C * (R - R * Q * R) * U (-b) := by noncomm_ring
  have hleft : sourceRootCompletedRightCommutatorLeftLeg owner lambda =
      C * E * (1 - Qscale) * E := by
    rw [sourceRootCompletedRightCommutatorLeftLeg_eq_root_fourierLeakage]
    rw [hE, hQ]
    simpa only [C, E, Qscale, ContinuousLinearMap.mul_def,
      ContinuousLinearMap.comp_assoc]
  calc
    sourceRootCompletedRightCommutatorLeftLeg owner lambda =
        C * E * (1 - Qscale) * E := hleft
    _ = U b * C * (R - R * Q * R) * U (-b) := hstar
    _ = (cc20GlobalLogTranslation (Real.log lambda)).toContinuousLinearMap ∘L
          rootConvolution owner ∘L
            (doubledShiftRadialProjection (Real.log lambda) -
              doubledShiftAlternatingProduct (Real.log lambda)) ∘L
              (cc20GlobalLogTranslation (-Real.log lambda)).toContinuousLinearMap := by
      rw [hAlt, hR]
      simpa only [U, C, Q, b, ContinuousLinearMap.mul_def,
        ContinuousLinearMap.comp_assoc]

/-! The same defect in its projection-complement form.  This spelling is
useful because it distinguishes the live S3 block from the already controlled
interior-compression block in the shifted-Hardy reduction. -/
theorem sourceRootCompletedRightCommutatorLeftLeg_eq_translated_complement_corner
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    sourceRootCompletedRightCommutatorLeftLeg owner lambda =
      (cc20GlobalLogTranslation (Real.log lambda)).toContinuousLinearMap ∘L
        rootConvolution owner ∘L
          (doubledShiftRadialProjection (Real.log lambda) ∘L
            (ContinuousLinearMap.id ℂ Carrier -
              sourceFourierSupportProjection unitSoninScale) ∘L
            doubledShiftRadialProjection (Real.log lambda)) ∘L
      (cc20GlobalLogTranslation (-Real.log lambda)).toContinuousLinearMap := by
  rw [sourceRootCompletedRightCommutatorLeftLeg_eq_translated_doubledShift_defect]
  have hAlt : doubledShiftAlternatingProduct (Real.log lambda) =
      doubledShiftRadialProjection (Real.log lambda) ∘L
        sourceFourierSupportProjection unitSoninScale ∘L
          doubledShiftRadialProjection (Real.log lambda) := by
    rfl
  rw [hAlt]
  have hR :
      doubledShiftRadialProjection (Real.log lambda) ∘L
          doubledShiftRadialProjection (Real.log lambda) =
        doubledShiftRadialProjection (Real.log lambda) := by
    exact (doubledShiftRadialProjection_isStarProjection
      (Real.log lambda)).isIdempotentElem
  have hcorner :
      doubledShiftRadialProjection (Real.log lambda) -
          doubledShiftRadialProjection (Real.log lambda) ∘L
            sourceFourierSupportProjection unitSoninScale ∘L
              doubledShiftRadialProjection (Real.log lambda) =
        doubledShiftRadialProjection (Real.log lambda) ∘L
          (ContinuousLinearMap.id ℂ Carrier -
            sourceFourierSupportProjection unitSoninScale) ∘L
            doubledShiftRadialProjection (Real.log lambda) := by
    apply ContinuousLinearMap.ext
    intro u
    have hRu := congrArg (fun L : Carrier →L[ℂ] Carrier => L u) hR
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.id_apply, map_sub] at hRu ⊢
    rw [hRu]
  rw [hcorner]

end Dev
end ConnesWeilRH
