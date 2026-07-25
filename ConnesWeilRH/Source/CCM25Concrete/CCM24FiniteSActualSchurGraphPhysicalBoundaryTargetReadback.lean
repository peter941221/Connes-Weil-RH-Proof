/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSActualSchurGraphPhysicalEndpointReadback
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedPhysicalTerminalReadout

/-!
# Graph physical boundary-target readback

Proof 527 expresses the actual endpoint as a graph endpoint plus one signed
endpoint residual.  This module pushes that equality through the existing
physical boundary target used by the completed-history readout.  The residual
therefore appears on the same target carrier as the future Gate 3U producer.

No factorization, norm estimate, sign, or RH conclusion is asserted here.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSActualSchurGraphPhysicalBoundaryTargetReadback

open CC20Concrete
open CCM24FiniteSActualJuliaInput
open CCM24FiniteSActualSchurForwardPhysicalDifference
open CCM24FiniteSActualSchurGraphPhysicalEndpointReadback
open CCM24FiniteSActualSchurGraphPhysicalCascadeResidual
open CCM24FiniteSCompletedPhysicalTerminalReadout
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSInverseMetric
open CCM24FiniteSProjectionTrace
open CCM24FiniteSRawRemainderCommonPair

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- The physical boundary target formed with the graph endpoint. -/
noncomputable def sourceActualBandGraphPhysicalBoundaryDaggerTarget
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G]
    (rightLeg : finiteSCarrier →L[ℂ] G)
    (lambda : CCM24SoninScale)
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (family : FinitePrimePowerFamily)
    (survivor : CCM24FiniteSFrameGramCalculus.sourceSoninCarrier lambda →L[ℂ]
      CCM24FiniteSFrameGramCalculus.sourceSoninCarrier lambda) :
    CCM24FiniteSFrameGramCalculus.sourceSoninCarrier lambda →L[ℂ] G :=
  physicalBoundaryDaggerTarget rightLeg
    (sourceActualBandGraphPhysicalEndpointCoframe lambda stepData family)
    (CCM24FiniteSGramResponse.sourceInclusion lambda) survivor

/-- The right-leg image of the complete graph endpoint residual. -/
noncomputable def sourceActualBandGraphPhysicalBoundaryDaggerResidual
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G]
    (rightLeg : finiteSCarrier →L[ℂ] G)
    (lambda : CCM24SoninScale)
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (family : FinitePrimePowerFamily) :
    CCM24FiniteSFrameGramCalculus.sourceSoninCarrier lambda →L[ℂ] G :=
  rightLeg ∘L sourceActualBandGraphPhysicalEndpointResidual
    (G := G) lambda stepData family

/-- The endpoint residual with the actual Schur product cancelled before any
estimate.  This is the direct physical-inverse minus full-graph owner. -/
noncomputable def sourceActualBandGraphPhysicalDirectEndpointResidual
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G]
    (lambda : CCM24SoninScale)
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (family : FinitePrimePowerFamily) :
    CCM24FiniteSFrameGramCalculus.sourceSoninCarrier lambda →L[ℂ]
      finiteSCarrier :=
  sourceBandProjection lambda ∘L
    (normalizedFiniteEulerInverse family -
      suffixActualSchurGraphPhysicalProduct lambda stepData family.visiblePrimes) ∘L
    CCM24FiniteSGramResponse.sourceInclusion lambda

theorem physicalBoundaryDaggerTarget_eq_graphTarget_add_residual
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G]
    (rightLeg : finiteSCarrier →L[ℂ] G)
    (lambda : CCM24SoninScale)
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (family : FinitePrimePowerFamily)
    (survivor : CCM24FiniteSFrameGramCalculus.sourceSoninCarrier lambda →L[ℂ]
      CCM24FiniteSFrameGramCalculus.sourceSoninCarrier lambda) :
    physicalBoundaryDaggerTarget rightLeg
        (sourceActualBandForwardEndpointCoframe lambda family)
        (CCM24FiniteSGramResponse.sourceInclusion lambda) survivor =
      sourceActualBandGraphPhysicalBoundaryDaggerTarget rightLeg lambda
        stepData family survivor +
        sourceActualBandGraphPhysicalBoundaryDaggerResidual rightLeg lambda
          stepData family := by
  apply ContinuousLinearMap.ext
  intro x
  rw [physicalBoundaryDaggerTarget,
    sourceActualBandForwardEndpointCoframe_eq_graphEndpoint_add_residual
      (G := G) lambda stepData family]
  simp only [physicalBoundaryDaggerTarget,
    sourceActualBandGraphPhysicalBoundaryDaggerTarget,
    sourceActualBandGraphPhysicalBoundaryDaggerResidual,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.add_apply, map_add]
  abel

theorem sourceActualBandGraphPhysicalBoundaryDaggerResidual_eq_rightLeg_comp
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G]
    (rightLeg : finiteSCarrier →L[ℂ] G)
    (lambda : CCM24SoninScale)
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (family : FinitePrimePowerFamily) :
    sourceActualBandGraphPhysicalBoundaryDaggerResidual rightLeg lambda
        stepData family =
      rightLeg ∘L sourceActualBandGraphPhysicalEndpointResidual
        (G := G) lambda stepData family := by
  rfl

theorem sourceActualBandGraphPhysicalEndpointResidual_eq_direct_residual
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G]
    (lambda : CCM24SoninScale)
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (family : FinitePrimePowerFamily) :
    sourceActualBandGraphPhysicalEndpointResidual lambda stepData family =
      sourceActualBandGraphPhysicalDirectEndpointResidual lambda stepData family := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [sourceActualBandGraphPhysicalEndpointResidual,
    sourceActualBandGraphPhysicalEndpointCoframe,
    sourceActualBandGraphPhysicalCoframe,
    sourceActualBandForwardEndpointCoframe,
    sourceActualBandForwardCoframe,
    sourceActualBandGraphPhysicalDirectEndpointResidual,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.add_apply, map_sub]
  abel

end CCM24FiniteSActualSchurGraphPhysicalBoundaryTargetReadback
end CCM25Concrete
end Source
end ConnesWeilRH
