/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSActualSchurGraphPhysicalCascadeResidual
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSActualSchurForwardPhysicalDifference

/-!
# Endpoint readback for the graph physical cascade

Proof 526 lives on the ambient finite-S carrier.  This module pushes its
complete cascade residual through the actual source inclusion and band
projection, then assembles the metric endpoint.  The physical endpoint
mismatch is thereby one signed difference of two residual coframes.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSActualSchurGraphPhysicalEndpointReadback

open CC20Concrete
open CCM24FiniteSActualJuliaInput
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSActualSchurForwardPhysicalDifference
open CCM24FiniteSActualSchurForwardTransport
open CCM24FiniteSActualSchurGraphPhysicalCascadeResidual
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSProjectionTrace
open CCM24FiniteSCoframeResponse
open CCM24FiniteSRawRemainderCommonPair

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) :
      CompleteSpace
        (CCM24FiniteSFrameGramCalculus.sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! ## Graph physical coframes -/

noncomputable def sourceActualBandGraphPhysicalCoframe
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (S : List CCM24VisiblePrime) :
    CCM24FiniteSFrameGramCalculus.sourceSoninCarrier lambda →L[ℂ]
      finiteSCarrier :=
  sourceBandProjection lambda ∘L
    suffixActualSchurGraphPhysicalProduct lambda stepData S ∘L
      CCM24FiniteSGramResponse.sourceInclusion lambda

noncomputable def sourceActualBandGraphPhysicalResidualCoframe
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (S : List CCM24VisiblePrime) :
    CCM24FiniteSFrameGramCalculus.sourceSoninCarrier lambda →L[ℂ]
      finiteSCarrier :=
  sourceBandProjection lambda ∘L
    suffixActualSchurGraphPhysicalCascadeResidual lambda stepData S ∘L
      CCM24FiniteSGramResponse.sourceInclusion lambda

theorem sourceActualBandGraphPhysicalCoframe_eq_schur_add_residual
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (S : List CCM24VisiblePrime) :
    sourceActualBandGraphPhysicalCoframe lambda stepData S =
      sourceActualBandForwardSchurCoframe lambda stepData S +
        sourceActualBandGraphPhysicalResidualCoframe lambda stepData S := by
  have hproduct :=
    suffixActualSchurGraphPhysicalProduct_eq_actualSchurProduct_add_residual
      lambda stepData S
  apply ContinuousLinearMap.ext
  intro x
  have hpoint := congrArg
    (fun operator : finiteSCarrier →L[ℂ] finiteSCarrier =>
      operator (CCM24FiniteSGramResponse.sourceInclusion lambda x)) hproduct
  simp only [sourceActualBandGraphPhysicalCoframe,
    sourceActualBandForwardSchurCoframe,
    sourceActualBandGraphPhysicalResidualCoframe,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply] at hpoint ⊢
  simpa only [map_add] using
    congrArg (fun y : finiteSCarrier => sourceBandProjection lambda y) hpoint

/-! ## Endpoint assembly -/

noncomputable def sourceActualBandGraphPhysicalEndpointCoframe
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (family : FinitePrimePowerFamily) :
    CCM24FiniteSFrameGramCalculus.sourceSoninCarrier lambda →L[ℂ]
      finiteSCarrier :=
  sourceActualBandGraphPhysicalCoframe lambda stepData family.visiblePrimes +
    finiteEulerMetricCoframe lambda family

noncomputable def sourceActualBandGraphPhysicalEndpointResidual
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (family : FinitePrimePowerFamily) :
    CCM24FiniteSFrameGramCalculus.sourceSoninCarrier lambda →L[ℂ]
      finiteSCarrier :=
  sourceActualBandForwardEndpointCoframe lambda family -
    sourceActualBandGraphPhysicalEndpointCoframe lambda stepData family

theorem sourceActualBandForwardEndpointCoframe_eq_graphEndpoint_add_residual
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (family : FinitePrimePowerFamily) :
    sourceActualBandForwardEndpointCoframe lambda family =
      sourceActualBandGraphPhysicalEndpointCoframe lambda stepData family +
        sourceActualBandGraphPhysicalEndpointResidual lambda stepData family := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [sourceActualBandGraphPhysicalEndpointResidual,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply]
  abel

theorem sourceActualBandGraphPhysicalEndpointResidual_eq_residual_difference
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (family : FinitePrimePowerFamily) :
    sourceActualBandGraphPhysicalEndpointResidual lambda stepData family =
      sourceActualBandForwardTransportResidual lambda stepData
          family.visiblePrimes -
        sourceActualBandGraphPhysicalResidualCoframe lambda stepData
          family.visiblePrimes := by
  rw [sourceActualBandGraphPhysicalEndpointResidual,
    sourceActualBandGraphPhysicalEndpointCoframe,
    sourceActualBandForwardEndpointCoframe_eq_schurForwardEndpoint_add_residual
      (G := G) lambda stepData family]
  rw [sourceActualBandGraphPhysicalCoframe_eq_schur_add_residual
    lambda stepData family.visiblePrimes]
  rw [sourceActualBandForwardSchurEndpointCoframe]
  abel_nf

end CCM24FiniteSActualSchurGraphPhysicalEndpointReadback
end CCM25Concrete
end Source
end ConnesWeilRH
