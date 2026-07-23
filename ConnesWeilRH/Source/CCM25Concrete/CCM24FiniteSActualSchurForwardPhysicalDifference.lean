/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSActualSchurForwardTransport
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCausalMarkov

/-!
# Physical inverse versus source-forward Schur transport

The normalized physical Euler inverse and the actual source-forward Schur
product have the same chronological list recursion but different one-step
factors.  This module keeps their difference as one operator-valued residual.
The residual is exact post-Q bookkeeping; no norm, sign, or vanishing claim is
made.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSActualSchurForwardPhysicalDifference

open scoped InnerProduct

open CC20Concrete
open _root_.ConnesWeilRH.CC20Concrete
open CCM24FiniteSActualJuliaInput
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSActualSchurForwardTransport
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSProjectionTrace
open CCM24FiniteSInverseMetric
open CCM24FiniteSCoframeResponse
open CCM24FiniteSRawRemainderCommonPair
open CCM24FiniteSCausalMarkov

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace
      (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! ## Ambient variation-of-constants residual -/

/-- The exact physical-inverse minus Schur-forward transport residual. -/
noncomputable def suffixActualSchurForwardPhysicalTransportResidual
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S) :
    List CCM24VisiblePrime → finiteSCarrier →L[ℂ] finiteSCarrier
  | [] => 0
  | p :: S =>
      suffixActualSchurForwardPhysicalTransportResidual lambda stepData S ∘L
          normalizedPrimeEulerInverse p +
        suffixActualSchurForwardAmbientProduct lambda stepData S ∘L
          (normalizedPrimeEulerInverse p -
            (suffixActualSchurFrameStep lambda stepData p S).transport)

theorem normalizedFiniteEulerInverseList_sub_forwardAmbient_eq_residual
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (S : List CCM24VisiblePrime) :
    normalizedFiniteEulerInverseList S -
        suffixActualSchurForwardAmbientProduct lambda stepData S =
      suffixActualSchurForwardPhysicalTransportResidual lambda stepData S := by
  induction S with
  | nil =>
      apply ContinuousLinearMap.ext
      intro x
      simp [normalizedFiniteEulerInverseList,
        suffixActualSchurForwardAmbientProduct,
        suffixActualSchurForwardPhysicalTransportResidual,
        CCM24FiniteSGramResponse.finiteEulerLowerFactor]
  | cons p S ih =>
      apply ContinuousLinearMap.ext
      intro x
      rw [normalizedFiniteEulerInverseList_cons]
      simp only [suffixActualSchurForwardAmbientProduct,
        suffixActualSchurForwardPhysicalTransportResidual,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.add_apply]
      have hpoint := congrArg
        (fun operator : finiteSCarrier →L[ℂ] finiteSCarrier =>
          operator (normalizedPrimeEulerInverse p x)) ih
      simp only [ContinuousLinearMap.sub_apply] at hpoint
      let u := normalizedPrimeEulerInverse p x
      let v := (suffixActualSchurFrameStep lambda stepData p S).transport x
      have hpoint' :
          normalizedFiniteEulerInverseList S u -
              (suffixActualSchurForwardAmbientProduct lambda stepData S) u =
            (suffixActualSchurForwardPhysicalTransportResidual lambda stepData S) u := by
        simpa only [u] using hpoint
      calc
        normalizedFiniteEulerInverseList S u -
              (suffixActualSchurForwardAmbientProduct lambda stepData S) v =
            (normalizedFiniteEulerInverseList S u -
                (suffixActualSchurForwardAmbientProduct lambda stepData S) u) +
              ((suffixActualSchurForwardAmbientProduct lambda stepData S) u -
                (suffixActualSchurForwardAmbientProduct lambda stepData S) v) := by
          abel
        _ = (suffixActualSchurForwardPhysicalTransportResidual lambda stepData S) u +
              (suffixActualSchurForwardAmbientProduct lambda stepData S) (u - v) := by
          rw [hpoint']
          simp only [map_sub]
        _ = (suffixActualSchurForwardPhysicalTransportResidual lambda stepData S) u +
              (suffixActualSchurForwardAmbientProduct lambda stepData S)
                ((normalizedPrimeEulerInverse p -
                  (suffixActualSchurFrameStep lambda stepData p S).transport) x) := by
          rfl

/-! ## Lift to the physical forward coframe -/

noncomputable def sourceActualBandForwardSchurCoframe
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (S : List CCM24VisiblePrime) :
    sourceSoninCarrier lambda →L[ℂ] finiteSCarrier :=
  CCM24FiniteSProjectionTrace.sourceBandProjection lambda ∘L
    suffixActualSchurForwardAmbientProduct lambda stepData S ∘L
      CCM24FiniteSGramResponse.sourceInclusion lambda

noncomputable def sourceActualBandForwardTransportResidual
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (S : List CCM24VisiblePrime) :
    sourceSoninCarrier lambda →L[ℂ] finiteSCarrier :=
  CCM24FiniteSProjectionTrace.sourceBandProjection lambda ∘L
    suffixActualSchurForwardPhysicalTransportResidual lambda stepData S ∘L
      CCM24FiniteSGramResponse.sourceInclusion lambda

theorem sourceActualBandForwardCoframe_eq_schurForwardCoframe_add_residual
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (family : FinitePrimePowerFamily) :
    sourceActualBandForwardCoframe lambda family =
      sourceActualBandForwardSchurCoframe lambda stepData family.visiblePrimes +
        sourceActualBandForwardTransportResidual lambda stepData
          family.visiblePrimes := by
  have hphysical :
      normalizedFiniteEulerInverse family =
        normalizedFiniteEulerInverseList family.visiblePrimes := by
    rw [normalizedFiniteEulerInverse_eq_causalAverage,
      finiteEulerCausalAverage_eq_normalizedInverse]
  have hres :=
    normalizedFiniteEulerInverseList_sub_forwardAmbient_eq_residual
      lambda stepData family.visiblePrimes
  apply ContinuousLinearMap.ext
  intro x
  rw [sourceActualBandForwardCoframe, hphysical]
  have hpoint := congrArg
    (fun operator : finiteSCarrier →L[ℂ] finiteSCarrier =>
      operator (CCM24FiniteSGramResponse.sourceInclusion lambda x)) hres
  simp only [sourceActualBandForwardSchurCoframe,
    sourceActualBandForwardTransportResidual,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.add_apply] at hpoint ⊢
  rw [show normalizedFiniteEulerInverseList family.visiblePrimes
        (CCM24FiniteSGramResponse.sourceInclusion lambda x) =
      (suffixActualSchurForwardAmbientProduct lambda stepData
          family.visiblePrimes)
          (CCM24FiniteSGramResponse.sourceInclusion lambda x) +
        (suffixActualSchurForwardPhysicalTransportResidual lambda stepData
          family.visiblePrimes)
        (CCM24FiniteSGramResponse.sourceInclusion lambda x) by
        simpa only [ContinuousLinearMap.sub_apply, add_comm] using
          sub_eq_iff_eq_add.mp hpoint]
  simp only [map_add]

noncomputable def sourceActualBandForwardSchurEndpointCoframe
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (family : FinitePrimePowerFamily) :
    sourceSoninCarrier lambda →L[ℂ] finiteSCarrier :=
  sourceActualBandForwardSchurCoframe lambda stepData family.visiblePrimes +
    finiteEulerMetricCoframe lambda family

theorem sourceActualBandForwardEndpointCoframe_eq_schurForwardEndpoint_add_residual
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (family : FinitePrimePowerFamily) :
    sourceActualBandForwardEndpointCoframe lambda family =
      sourceActualBandForwardSchurEndpointCoframe lambda stepData family +
        sourceActualBandForwardTransportResidual lambda stepData
          family.visiblePrimes := by
  rw [sourceActualBandForwardEndpointCoframe,
    sourceActualBandForwardSchurEndpointCoframe]
  rw [sourceActualBandForwardCoframe_eq_schurForwardCoframe_add_residual
    (G := G) lambda stepData family]
  abel

end CCM24FiniteSActualSchurForwardPhysicalDifference
end CCM25Concrete
end Source
end ConnesWeilRH
