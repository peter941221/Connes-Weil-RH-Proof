/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSActualBandSourceRemainder

/-!
# Actual band quadratic remainder cycle

The actual quadratic remainder lives on the ambient common-log carrier, while
its trace-compatible readback lives on the source Sonin carrier.  This module
exposes four rectangular root legs and proves both factor orders before using
the trace-legal source remainder owner from Proof 440.

No raw root leg is asserted to be Hilbert--Schmidt by itself.  Trace legality
belongs to the complete recombined source cycle.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSActualBandQuadraticCycle

open CC20Concrete
open MeasureTheory
open CCM24FiniteSProjectionTrace
open CCM24FiniteSGramResponse
open CCM24FiniteSBandTrace
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSInverseMetric
open CCM24FiniteSFixedQuotientCarrier
open CCM24FiniteSActualBandJetOrientation
open CCM24FiniteSActualBandFirstJetTrace
open CCM24FiniteSActualBandSourceRemainder
open CCM24FiniteSRootCompletedFirstJet
open CCM24SourceProlateTrace
open CC20Concrete.CompactRootHalfLinePair
open scoped InnerProduct InnerProductSpace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace
      (CCM24FiniteSGramResponse.sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

local notation "Op" => finiteSCarrier →L[ℂ] finiteSCarrier

noncomputable def actualBandBaseRootLeg
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    CCM24FiniteSGramResponse.sourceSoninCarrier lambda →L[ℂ] finiteSCarrier :=
  rootConvolution owner ∘L CCM24FiniteSGramResponse.sourceInclusion lambda

noncomputable def actualBandJetRootLeg
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    CCM24FiniteSGramResponse.sourceSoninCarrier lambda →L[ℂ] finiteSCarrier :=
  rootConvolution owner ∘L sourceBandProjection lambda ∘L
    normalizedFiniteEulerInverse family ∘L
      CCM24FiniteSGramResponse.sourceInclusion lambda

noncomputable def actualBandTargetFrameRootLeg
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    CCM24FiniteSGramResponse.sourceSoninCarrier lambda →L[ℂ] finiteSCarrier :=
  rootConvolution owner ∘L finiteEulerFrame lambda family

noncomputable def actualBandTargetDualRootLeg
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    CCM24FiniteSGramResponse.sourceSoninCarrier lambda →L[ℂ] finiteSCarrier :=
  rootConvolution owner ∘L finiteEulerDualFrame lambda family

noncomputable def actualBandFirstJetRootResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) : Op :=
  rootConvolution owner ∘L
    sourceActualBandNormalizedInversePairedJet lambda family ∘L
      (rootConvolution owner)†

noncomputable def actualBandQuadraticRootResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) : Op :=
  rootConvolution owner ∘L
    sourceActualBandQuadraticRemainder lambda family ∘L
      (rootConvolution owner)†

noncomputable def actualBandFirstJetCycledResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    CCM24FiniteSGramResponse.sourceSoninCarrier lambda →L[ℂ]
      CCM24FiniteSGramResponse.sourceSoninCarrier lambda :=
  (actualBandBaseRootLeg owner lambda)† ∘L
      actualBandJetRootLeg owner lambda family +
    (actualBandJetRootLeg owner lambda family)† ∘L
      actualBandBaseRootLeg owner lambda

noncomputable def actualBandEndpointCycledResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    CCM24FiniteSGramResponse.sourceSoninCarrier lambda →L[ℂ]
      CCM24FiniteSGramResponse.sourceSoninCarrier lambda :=
  (actualBandBaseRootLeg owner lambda)† ∘L
      actualBandBaseRootLeg owner lambda -
    (actualBandTargetFrameRootLeg owner lambda family)† ∘L
      actualBandTargetDualRootLeg owner lambda family

noncomputable def actualBandQuadraticCycledResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    CCM24FiniteSGramResponse.sourceSoninCarrier lambda →L[ℂ]
      CCM24FiniteSGramResponse.sourceSoninCarrier lambda :=
  actualBandFirstJetCycledResponse owner lambda family -
    actualBandEndpointCycledResponse owner lambda family

theorem sourceSoninProjection_comp_sourceInclusion_eq_self
    (lambda : CCM24SoninScale) :
    sourceSoninProjection lambda ∘L
        CCM24FiniteSGramResponse.sourceInclusion lambda =
      CCM24FiniteSGramResponse.sourceInclusion lambda := by
  rw [← CCM24FiniteSGramResponse.sourceInclusion_comp_adjoint]
  apply ContinuousLinearMap.ext
  intro u
  change CCM24FiniteSGramResponse.sourceInclusion lambda
      (((CCM24FiniteSGramResponse.sourceInclusion lambda)† ∘L
        CCM24FiniteSGramResponse.sourceInclusion lambda) u) = _
  rw [CCM24FiniteSGramResponse.sourceInclusion_adjoint_comp_self]
  rfl

theorem sourceActualBandQuadraticRemainder_eq_actualPair_sub_bandDifference
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceActualBandQuadraticRemainder lambda family =
      sourceActualBandNormalizedInversePairedJet lambda family -
        soninBandDifference lambda family := by
  rw [soninBandDifference_eq_actualNormalizedPair_sub_quadraticRemainder]
  abel

theorem actualBandFirstJetRootResponse_eq_rectangularFactors
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    actualBandFirstJetRootResponse owner lambda family =
      actualBandJetRootLeg owner lambda family ∘L
          (actualBandBaseRootLeg owner lambda)† +
        actualBandBaseRootLeg owner lambda ∘L
          (actualBandJetRootLeg owner lambda family)† := by
  rw [actualBandFirstJetRootResponse,
    sourceActualBandNormalizedInversePairedJet, normalizedInverseBandPair,
    ← CCM24FiniteSGramResponse.sourceInclusion_comp_adjoint]
  apply ContinuousLinearMap.ext
  intro u
  simp only [actualBandJetRootLeg, actualBandBaseRootLeg,
    ContinuousLinearMap.adjoint_comp,
    (sourceBandProjection_isStarProjection lambda).isSelfAdjoint.adjoint_eq,
    ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.add_apply, map_add]

theorem rootSandwichedBandResponse_eq_rectangularFactors
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    rootSandwichedBandResponse owner lambda family =
      actualBandBaseRootLeg owner lambda ∘L
          (actualBandBaseRootLeg owner lambda)† -
        actualBandTargetDualRootLeg owner lambda family ∘L
          (actualBandTargetFrameRootLeg owner lambda family)† := by
  rw [rootSandwichedBandResponse, soninBandDifference,
    targetBandProjection, sourceBandProjection,
    targetSoninProjection_eq_dualFrame_comp_frameAdjoint,
    ← CCM24FiniteSGramResponse.sourceInclusion_comp_adjoint]
  apply ContinuousLinearMap.ext
  intro u
  simp only [actualBandBaseRootLeg, actualBandTargetDualRootLeg,
    actualBandTargetFrameRootLeg, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    map_sub]
  abel

theorem actualBandQuadraticRootResponse_eq_first_sub_endpoint
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    actualBandQuadraticRootResponse owner lambda family =
      actualBandFirstJetRootResponse owner lambda family -
        rootSandwichedBandResponse owner lambda family := by
  rw [actualBandQuadraticRootResponse, actualBandFirstJetRootResponse,
    rootSandwichedBandResponse,
    sourceActualBandQuadraticRemainder_eq_actualPair_sub_bandDifference]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    map_sub]

theorem actualBandQuadraticRootResponse_eq_rectangularFactors
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    actualBandQuadraticRootResponse owner lambda family =
      actualBandJetRootLeg owner lambda family ∘L
          (actualBandBaseRootLeg owner lambda)† +
        actualBandBaseRootLeg owner lambda ∘L
          (actualBandJetRootLeg owner lambda family)† -
        actualBandBaseRootLeg owner lambda ∘L
          (actualBandBaseRootLeg owner lambda)† +
        actualBandTargetDualRootLeg owner lambda family ∘L
          (actualBandTargetFrameRootLeg owner lambda family)† := by
  rw [actualBandQuadraticRootResponse_eq_first_sub_endpoint,
    actualBandFirstJetRootResponse_eq_rectangularFactors,
    rootSandwichedBandResponse_eq_rectangularFactors]
  abel

theorem sourceActualBandFiniteEulerSoninResponse_eq_firstJetCycle
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceActualBandFiniteEulerSoninResponse owner lambda family =
      actualBandFirstJetCycledResponse owner lambda family := by
  rw [sourceActualBandFiniteEulerSoninResponse,
    sourceActualBandFiniteEulerPairedResponse_eq_rawDetector,
    detectorOperator_eq_rootConvolution_adjoint_comp_rootConvolution]
  apply ContinuousLinearMap.ext
  intro u
  have hright := congrArg
    (fun operator : CCM24FiniteSGramResponse.sourceSoninCarrier lambda →L[ℂ]
      finiteSCarrier => operator u)
    (sourceSoninProjection_comp_sourceInclusion_eq_self lambda)
  simp only [ContinuousLinearMap.comp_apply] at hright
  have hleft (x : finiteSCarrier) :
      ((CCM24FiniteSGramResponse.sourceInclusion lambda)†)
          (sourceSoninProjection lambda x) =
        ((CCM24FiniteSGramResponse.sourceInclusion lambda)†) x := by
    have hx := congrArg
      (fun operator : finiteSCarrier →L[ℂ]
        CCM24FiniteSGramResponse.sourceSoninCarrier lambda => operator x)
      (CCM24FiniteSGramResponse.sourceInclusionAdjoint_comp_sourceProjection
        lambda)
    simpa only [ContinuousLinearMap.comp_apply] using hx
  simp only [actualBandFirstJetCycledResponse, actualBandBaseRootLeg,
    actualBandJetRootLeg, actualBandDetectorPairedResponse,
    ContinuousLinearMap.mul_def, ContinuousLinearMap.adjoint_comp,
    (sourceBandProjection_isStarProjection lambda).isSelfAdjoint.adjoint_eq,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply, map_add]
  rw [hright, hleft, hleft]

theorem sourceBandGramResponse_eq_endpointCycle
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceBandGramResponse owner lambda family =
      actualBandEndpointCycledResponse owner lambda family := by
  rw [sourceBandGramResponse, sourceGramResponse,
    detectorOperator_eq_rootConvolution_adjoint_comp_rootConvolution]
  apply ContinuousLinearMap.ext
  intro u
  simp only [actualBandEndpointCycledResponse, actualBandBaseRootLeg,
    actualBandTargetFrameRootLeg, actualBandTargetDualRootLeg,
    finiteEulerDualFrame, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.neg_apply]
  abel

theorem sourceActualBandFiniteEulerRemainderResponse_eq_quadraticCycle
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceActualBandFiniteEulerRemainderResponse owner lambda family =
      actualBandQuadraticCycledResponse owner lambda family := by
  rw [sourceActualBandFiniteEulerRemainderResponse,
    actualBandQuadraticCycledResponse,
    sourceActualBandFiniteEulerSoninResponse_eq_firstJetCycle,
    sourceBandGramResponse_eq_endpointCycle]

theorem actualBandQuadraticCycledResponse_isTraceClassAlong
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ tau ιr κr taur nu mu sigma rho : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis tau ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis ιr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis κr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis taur ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis mu ℂ (commonBoundaryCarrier a c))
    (pairedBoundaryBasis : HilbertBasis sigma ℂ
      (actualBandPairCarrier a c))
    (sourceBasis : HilbertBasis rho ℂ
      (CCM24FiniteSGramResponse.sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    CC20Concrete.PositiveTrace.IsTraceClassAlong sourceBasis
      (actualBandQuadraticCycledResponse owner lambda family) := by
  rw [← sourceActualBandFiniteEulerRemainderResponse_eq_quadraticCycle]
  exact sourceActualBandFiniteEulerRemainderResponse_isTraceClassAlong owner
    lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis pairedBoundaryBasis sourceBasis hfactor

end CCM24FiniteSActualBandQuadraticCycle
end CCM25Concrete
end Source
end ConnesWeilRH
