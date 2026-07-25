/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSActualSchurGraphPhysicalCascadeReadback

/-!
# Full-cascade graph physical residual

The graph-support readback is a one-step identity.  This module lifts it to
the chronological finite-S product and keeps the resulting difference as one
operator-valued Duhamel residual.  No termwise estimate or residual-vanishing
claim is introduced.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSActualSchurGraphPhysicalCascadeResidual

open CC20Concrete
open CCM24FiniteSActualJuliaInput
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSActualSchurForwardTransport
open CCM24FiniteSActualSchurGraphPhysicalCascadeReadback
open CCM24FiniteSActualSchurGraphPhysicalTransportReadback
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSProjectionTrace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

noncomputable def suffixActualSchurGraphPhysicalStep
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  normalizedPrimeEulerFrameTransport p ∘L
    canonicalFullGraphFrame (suffixStepPrimeEulerInput lambda p S)

noncomputable def suffixActualSchurGraphPhysicalProduct
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S) :
    List CCM24VisiblePrime → finiteSCarrier →L[ℂ] finiteSCarrier
  | [] => ContinuousLinearMap.id ℂ finiteSCarrier
  | p :: S =>
      suffixActualSchurGraphPhysicalProduct lambda stepData S ∘L
        suffixActualSchurGraphPhysicalStep lambda p S

noncomputable def suffixActualSchurGraphPhysicalCascadeResidual
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S) :
    List CCM24VisiblePrime → finiteSCarrier →L[ℂ] finiteSCarrier
  | [] => 0
  | p :: S =>
      suffixActualSchurGraphPhysicalCascadeResidual lambda stepData S ∘L
          (suffixActualSchurFrameStep lambda stepData p S).transport +
        suffixActualSchurGraphPhysicalProduct lambda stepData S ∘L
          normalizedCanonicalGraphPhysicalResidual
            (suffixStepPrimeEulerInput lambda p S)

theorem suffixActualSchurGraphPhysicalCascadeProduct_sub_actualSchurProduct_eq_residual
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (S : List CCM24VisiblePrime) :
    suffixActualSchurGraphPhysicalProduct lambda stepData S -
        suffixActualSchurForwardAmbientProduct lambda stepData S =
      suffixActualSchurGraphPhysicalCascadeResidual lambda stepData S := by
  induction S with
  | nil =>
      apply ContinuousLinearMap.ext
      intro x
      simp only [suffixActualSchurGraphPhysicalProduct,
        suffixActualSchurForwardAmbientProduct,
        suffixActualSchurGraphPhysicalCascadeResidual,
        sub_self]
  | cons p S ih =>
      let step := suffixActualSchurFrameStep lambda stepData p S
      let graphStep := suffixActualSchurGraphPhysicalStep lambda p S
      let graphResidual :=
        normalizedCanonicalGraphPhysicalResidual
          (suffixStepPrimeEulerInput lambda p S)
      have hstep : graphStep = step.transport + graphResidual := by
        dsimp [graphStep, step, suffixActualSchurGraphPhysicalStep,
          graphResidual]
        exact suffixActualSchurFrameStep_fullGraphPhysicalTransport_eq_add_residual
          lambda stepData p S
      apply ContinuousLinearMap.ext
      intro x
      have ihPoint := congrArg
        (fun operator : finiteSCarrier →L[ℂ] finiteSCarrier =>
          operator (step.transport x)) ih
      have ihPoint' :
          (suffixActualSchurGraphPhysicalProduct lambda stepData S)
              (step.transport x) -
            (suffixActualSchurForwardAmbientProduct lambda stepData S)
              (step.transport x) =
          (suffixActualSchurGraphPhysicalCascadeResidual lambda stepData S)
            (step.transport x) := by
        simpa only [ContinuousLinearMap.sub_apply] using ihPoint
      simp only [suffixActualSchurGraphPhysicalProduct,
        suffixActualSchurForwardAmbientProduct,
        suffixActualSchurGraphPhysicalCascadeResidual,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.add_apply] at ⊢
      rw [show graphStep x = step.transport x + graphResidual x by
        exact congrArg (fun operator : finiteSCarrier →L[ℂ] finiteSCarrier =>
          operator x) hstep]
      rw [map_add]
      calc
        (suffixActualSchurGraphPhysicalProduct lambda stepData S)
              (step.transport x) +
            (suffixActualSchurGraphPhysicalProduct lambda stepData S)
              (graphResidual x) -
            (suffixActualSchurForwardAmbientProduct lambda stepData S)
              (step.transport x) =
          ((suffixActualSchurGraphPhysicalProduct lambda stepData S)
              (step.transport x) -
            (suffixActualSchurForwardAmbientProduct lambda stepData S)
              (step.transport x)) +
            (suffixActualSchurGraphPhysicalProduct lambda stepData S)
              (graphResidual x) := by abel
        _ = (suffixActualSchurGraphPhysicalCascadeResidual lambda stepData S)
              (step.transport x) +
            (suffixActualSchurGraphPhysicalProduct lambda stepData S)
              (graphResidual x) := by rw [ihPoint']

theorem suffixActualSchurGraphPhysicalProduct_eq_actualSchurProduct_add_residual
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (S : List CCM24VisiblePrime) :
    suffixActualSchurGraphPhysicalProduct lambda stepData S =
      suffixActualSchurForwardAmbientProduct lambda stepData S +
        suffixActualSchurGraphPhysicalCascadeResidual lambda stepData S := by
  rw [← suffixActualSchurGraphPhysicalCascadeProduct_sub_actualSchurProduct_eq_residual
    lambda stepData S]
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply]
  abel

end CCM24FiniteSActualSchurGraphPhysicalCascadeResidual
end CCM25Concrete
end Source
end ConnesWeilRH
