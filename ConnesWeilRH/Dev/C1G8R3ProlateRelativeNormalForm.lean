/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3LeakageDoubledShift

/-!
# R3 relative-motion normal form for the source prolate factor

The unit-scale prolate square-sum cannot simply be transported to every
cutoff: after putting the source cutoff on one carrier, the two projections
move relative to one another.  This leaf records the exact normal form and
the corresponding Hilbert--Schmidt summability transfer.

No uniform relative-angle estimate, detector sign, or RH implication is
asserted here.
-/

namespace ConnesWeilRH
namespace Dev

open Source
open Source.CC20Concrete
open Source.CCM25Concrete
open Source.CCM25Concrete.CCM24FiniteSProjectionTrace
open Source.CCM25Concrete.CCM24RadialBoundaryPairTransport
open Source.CCM25Concrete.CCM24SourceProlateTrace
open Source.CCM25Concrete.CCM24UnitScaleProlateAlignment
open Source.CCM25Concrete.SelectedCrossingOperatorBridge

local notation "Carrier" =>
  Source.CCM25Concrete.CCM24FiniteSProjectionTrace.finiteSCarrier
local notation "Op" => Carrier →L[ℂ] Carrier

noncomputable def doubledShiftProlateHilbertSchmidtFactor (b : ℝ) : Op :=
  sourceFourierSupportProjection unitSoninScale ∘L
    (doubledShiftRadialProjection b -
      doubledShiftSoninIntersectionProjection b)

theorem globalTranslation_comp (a c : ℝ) :
    (cc20GlobalLogTranslation a).toContinuousLinearMap ∘L
        (cc20GlobalLogTranslation c).toContinuousLinearMap =
      (cc20GlobalLogTranslation (a + c)).toContinuousLinearMap := by
  exact rawGlobalLogTranslation_comp a c

theorem sourceRadialProjection_eq_translated_doubledShift
    (lambda : CCM24SoninScale) :
    radialSupportProjection lambda =
      (cc20GlobalLogTranslation (Real.log lambda)).toContinuousLinearMap ∘L
        doubledShiftRadialProjection (Real.log lambda) ∘L
          (cc20GlobalLogTranslation (-Real.log lambda)).toContinuousLinearMap := by
  let b : ℝ := Real.log lambda
  let U : ℝ → Op := fun a =>
    (cc20GlobalLogTranslation a).toContinuousLinearMap
  let P : Op := cc20PositiveHalfLineProjection
  have htrans (a c : ℝ) : U a * U c = U (a + c) := by
    dsimp [U]
    simpa only [ContinuousLinearMap.mul_def] using globalTranslation_comp a c
  have hR : doubledShiftRadialProjection b =
      U (-2 * b) * P * U (2 * b) := by
    simpa only [doubledShiftRadialProjection_eq_translatedHalfLineProjection,
      U, P, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc] using
      (doubledShiftRadialProjection_eq_translatedHalfLineProjection b)
  have hE : radialSupportProjection lambda = U (-b) * P * U b := by
    simpa only [radialSupportProjection_eq_translation_conjugation,
      U, P, b, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc] using
      (radialSupportProjection_eq_translation_conjugation lambda)
  have h_b_m2b : U b * U (-2 * b) = U (-b) := by
    rw [htrans, show b + -2 * b = -b by ring]
  have h_2b_mb : U (2 * b) * U (-b) = U b := by
    rw [htrans, show 2 * b + -b = b by ring]
  rw [hE, hR]
  symm
  calc
    U b * (U (-2 * b) * P * U (2 * b)) * U (-b) =
        (U b * U (-2 * b)) * P * (U (2 * b) * U (-b)) := by
          noncomm_ring
    _ = U (-b) * P * U b := by rw [h_b_m2b, h_2b_mb]

theorem sourceSoninProjection_eq_translated_intersectionProjection
    (lambda : CCM24SoninScale) :
    sourceSoninProjection lambda =
      (cc20GlobalLogTranslation (Real.log lambda)).toContinuousLinearMap ∘L
        doubledShiftSoninIntersectionProjection (Real.log lambda) ∘L
          (cc20GlobalLogTranslation (-Real.log lambda)).toContinuousLinearMap := by
  let b : ℝ := Real.log lambda
  let U : ℝ → Op := fun a =>
    (cc20GlobalLogTranslation a).toContinuousLinearMap
  have hsymm :
      ((cc20GlobalLogTranslationEquiv b).symm : Carrier →L[ℂ] Carrier) =
        U (-b) := by
    apply ContinuousLinearMap.ext
    intro u
    exact globalTranslationEquiv_symm_apply b u
  have hmap := doubledShiftSoninProjection_map_eq_source lambda
  rw [← hmap]
  unfold doubledShiftSoninProjection doubledShiftSoninIntersectionProjection
  rw [hsymm]
  rfl

theorem sourceProlateHilbertSchmidtFactor_eq_translated_relativeFactor
    (lambda : CCM24SoninScale) :
    sourceProlateHilbertSchmidtFactor lambda =
      (cc20GlobalLogTranslation (Real.log lambda)).toContinuousLinearMap ∘L
        doubledShiftProlateHilbertSchmidtFactor (Real.log lambda) ∘L
          (cc20GlobalLogTranslation (-Real.log lambda)).toContinuousLinearMap := by
  let b : ℝ := Real.log lambda
  let U : ℝ → Op := fun a =>
    (cc20GlobalLogTranslation a).toContinuousLinearMap
  let Q : Op := sourceFourierSupportProjection unitSoninScale
  let P : Op := doubledShiftRadialProjection b
  let R : Op := doubledShiftSoninIntersectionProjection b
  have htrans (a c : ℝ) : U a * U c = U (a + c) := by
    dsimp [U]
    simpa only [ContinuousLinearMap.mul_def] using globalTranslation_comp a c
  have hcancel : U (-b) * U b = (1 : Op) := by
    rw [htrans, show -b + b = 0 by ring]
    dsimp [U]
    simpa only [ContinuousLinearMap.one_def] using unitTranslation_zero_operator
  have hQ : sourceFourierSupportProjection lambda = U b * Q * U (-b) := by
    simpa only [U, Q, b, logTranslation, ContinuousLinearMap.mul_def,
      ContinuousLinearMap.comp_assoc] using
      (sourceFourierSupportProjection_eq_scale_conjugate_of_zero_defects lambda)
  have hE := sourceRadialProjection_eq_translated_doubledShift lambda
  have hS := sourceSoninProjection_eq_translated_intersectionProjection lambda
  have hB : radialSupportProjection lambda - sourceSoninProjection lambda =
      U b * (P - R) * U (-b) := by
    rw [hE, hS]
    dsimp only [P, R]
    noncomm_ring
  change sourceProlateHilbertSchmidtFactor lambda =
    U b ∘L doubledShiftProlateHilbertSchmidtFactor b ∘L U (-b)
  rw [sourceProlateHilbertSchmidtFactor, hQ, hB]
  dsimp only [doubledShiftProlateHilbertSchmidtFactor, Q, P, R]
  calc
    (U b * Q * U (-b)) * (U b * (P - R) * U (-b)) =
        U b * Q * (U (-b) * U b) * (P - R) * U (-b) := by
          noncomm_ring
    _ = U b * Q * (P - R) * U (-b) := by
      rw [hcancel]
      simp

theorem sourceProlateHilbertSchmidtFactor_summable_of_relativeFactor
    {ι : Type*} (basis : HilbertBasis ι ℂ Carrier)
    (lambda : CCM24SoninScale)
    (hfactor : Summable fun i =>
      ‖doubledShiftProlateHilbertSchmidtFactor (Real.log lambda)
        (basis i)‖ ^ 2) :
    Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (basis i)‖ ^ 2 := by
  rw [sourceProlateHilbertSchmidtFactor_eq_translated_relativeFactor lambda]
  let Uplus : Op :=
    (cc20GlobalLogTranslation (Real.log lambda)).toContinuousLinearMap
  let Uminus : Op :=
    (cc20GlobalLogTranslation (-Real.log lambda)).toContinuousLinearMap
  have hpre := PositiveTrace.summable_normSq_precomp
    basis basis basis (doubledShiftProlateHilbertSchmidtFactor
      (Real.log lambda)) Uminus hfactor
  have hpost := PositiveTrace.summable_normSq_postcomp
    basis (doubledShiftProlateHilbertSchmidtFactor
      (Real.log lambda) ∘L Uminus) Uplus hpre
  simpa only [Uplus, Uminus, ContinuousLinearMap.comp_assoc] using hpost

theorem relativeFactor_summable_of_sourceProlateHilbertSchmidtFactor
    {ι : Type*} (basis : HilbertBasis ι ℂ Carrier)
    (lambda : CCM24SoninScale)
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (basis i)‖ ^ 2) :
    Summable fun i =>
      ‖doubledShiftProlateHilbertSchmidtFactor (Real.log lambda)
        (basis i)‖ ^ 2 := by
  let b : ℝ := Real.log lambda
  let Uplus : Op := (cc20GlobalLogTranslation b).toContinuousLinearMap
  let Uminus : Op := (cc20GlobalLogTranslation (-b)).toContinuousLinearMap
  have htrans (a c : ℝ) :
      (cc20GlobalLogTranslation a).toContinuousLinearMap ∘L
          (cc20GlobalLogTranslation c).toContinuousLinearMap =
        (cc20GlobalLogTranslation (a + c)).toContinuousLinearMap := by
    exact globalTranslation_comp a c
  have hzero :
      (cc20GlobalLogTranslation 0).toContinuousLinearMap =
        ContinuousLinearMap.id ℂ Carrier :=
    unitTranslation_zero_operator
  have hplusminus : Uplus ∘L Uminus =
      ContinuousLinearMap.id ℂ Carrier := by
    dsimp [Uplus, Uminus]
    rw [htrans, show b + -b = 0 by ring, hzero]
  have hminusplus : Uminus ∘L Uplus =
      ContinuousLinearMap.id ℂ Carrier := by
    dsimp [Uplus, Uminus]
    rw [htrans, show -b + b = 0 by ring, hzero]
  have hforward := sourceProlateHilbertSchmidtFactor_eq_translated_relativeFactor
    lambda
  have hforward' :
      sourceProlateHilbertSchmidtFactor lambda =
        Uplus ∘L doubledShiftProlateHilbertSchmidtFactor b ∘L Uminus := by
    simpa only [Uplus, Uminus, b] using hforward
  have hreverse :
      doubledShiftProlateHilbertSchmidtFactor b =
        Uminus ∘L sourceProlateHilbertSchmidtFactor lambda ∘L Uplus := by
    calc
      doubledShiftProlateHilbertSchmidtFactor b =
          (Uminus ∘L Uplus) ∘L
            doubledShiftProlateHilbertSchmidtFactor b ∘L
              (Uminus ∘L Uplus) := by
                rw [hminusplus]
                simp
      _ = Uminus ∘L
          (Uplus ∘L doubledShiftProlateHilbertSchmidtFactor b ∘L Uminus) ∘L
            Uplus := by
              simp only [ContinuousLinearMap.comp_assoc]
      _ = Uminus ∘L sourceProlateHilbertSchmidtFactor lambda ∘L Uplus := by
            rw [hforward']
  rw [hreverse]
  let Uplus' : Op := (cc20GlobalLogTranslation (Real.log lambda)).toContinuousLinearMap
  let Uminus' : Op := (cc20GlobalLogTranslation (-Real.log lambda)).toContinuousLinearMap
  have hpre := PositiveTrace.summable_normSq_precomp
    basis basis basis (sourceProlateHilbertSchmidtFactor lambda) Uplus' hfactor
  have hpost := PositiveTrace.summable_normSq_postcomp
    basis (sourceProlateHilbertSchmidtFactor lambda ∘L Uplus') Uminus' hpre
  simpa only [Uplus', Uminus', ContinuousLinearMap.comp_assoc] using hpost

theorem sourceProlateHilbertSchmidtFactor_summable_iff_relativeFactor
    {ι : Type*} (basis : HilbertBasis ι ℂ Carrier)
    (lambda : CCM24SoninScale) :
    (Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (basis i)‖ ^ 2) ↔
      (Summable fun i =>
        ‖doubledShiftProlateHilbertSchmidtFactor (Real.log lambda)
          (basis i)‖ ^ 2) := by
  constructor
  · exact relativeFactor_summable_of_sourceProlateHilbertSchmidtFactor
      basis lambda
  · exact sourceProlateHilbertSchmidtFactor_summable_of_relativeFactor
      basis lambda

end Dev
end ConnesWeilRH
