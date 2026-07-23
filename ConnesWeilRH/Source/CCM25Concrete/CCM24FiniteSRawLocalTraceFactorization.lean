/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSRawCompletedSchurCocycle
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSRawRemainderCommonPair

/-!
# Local trace factorization of the raw Schur--Markov cocycle

Proof 499 constructs the raw quadratic remainder for every literal suffix
list.  This module gives every such suffix the same complete physical
Hilbert--Schmidt owner used by the finite-family endpoint.  It then builds the
one-step raw defect by bounded sandwiches of those owners.

The outer, reflected-outer, second-support, and prolate branches remain inside
one common physical pair.  No branchwise absolute value, uniform estimate,
Gate 3U conclusion, sign statement, or RH premise is introduced here.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSRawLocalTraceFactorization

open MeasureTheory
open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.PositiveTrace
open CC20Concrete.CompactRootHalfLinePair
open CCM24FiniteSProjectionTrace
open CCM24FiniteSGramResponse
open CCM24FiniteSBandTrace
open CCM24FiniteSInverseMetric
open CCM24FiniteSCoframeResponse
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSTwoSidedRootRecombination
open CCM24FiniteSFixedQuotientCarrier
open CCM24FiniteSRootCompletedFirstJet
open CCM24FiniteSActualBandFirstJetTrace
open CCM24FiniteSActualBandQuadraticCycle
open CCM24FiniteSActualBandSourceRemainder
open CCM24FiniteSCausalMarkov
open CCM24FiniteSGramInverseCalculus
open CCM24FiniteSParameterizedEulerProduct
open CCM24FiniteSRawRemainderCommonPair
open CCM24FiniteSRawCompletedSchurCocycle
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSSchurMarkovPairing
open CCM24SourceProlateTrace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

local notation "SourceOp" lambda =>
  sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda

local notation "GlobalOp" => finiteSCarrier →L[ℂ] finiteSCarrier

/-! ## Family-free suffix frame and coframe -/

/-- The unnormalized finite Euler transport on a literal suffix list. -/
noncomputable def suffixActualBandTransportOperator
    (S : List CCM24VisiblePrime) : GlobalOp :=
  (ccm24FiniteEulerTransportEquiv S).toContinuousLinearMap

/-- The literal suffix frame at the endpoint parameter `alpha = 1`. -/
noncomputable def suffixActualBandFrame
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    sourceSoninCarrier lambda →L[ℂ] finiteSCarrier :=
  CCM24FiniteSFrameGramCalculus.parameterizedSoninFrame lambda 1 S

/-- The inverse restricted Gram covariance on a literal suffix list. -/
noncomputable def suffixActualBandGramInv
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    SourceOp lambda :=
  parameterizedSoninGramInv lambda 1 S (by norm_num)

/-- The canonical dual suffix frame. -/
noncomputable def suffixActualBandDualFrame
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    sourceSoninCarrier lambda →L[ℂ] finiteSCarrier :=
  suffixActualBandFrame lambda S ∘L suffixActualBandGramInv lambda S

/-- The ambient Euler covariance `T_S† T_S` for a literal suffix list. -/
noncomputable def suffixActualBandAmbientGram
    (S : List CCM24VisiblePrime) : GlobalOp :=
  (suffixActualBandTransportOperator S)† ∘L
    suffixActualBandTransportOperator S

/-- The metric coframe `T_S† T_S J G_S⁻¹` on a literal suffix list. -/
noncomputable def suffixActualBandMetricCoframe
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    sourceSoninCarrier lambda →L[ℂ] finiteSCarrier :=
  suffixActualBandAmbientGram S ∘L sourceInclusion lambda ∘L
    suffixActualBandGramInv lambda S

/-- The normalized forward actual-band coframe `B A_S J`. -/
noncomputable def suffixActualBandForwardCoframe
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    sourceSoninCarrier lambda →L[ℂ] finiteSCarrier :=
  sourceBandProjection lambda ∘L normalizedFiniteEulerInverseList S ∘L
    sourceInclusion lambda

theorem suffixActualBandForwardCoframe_adjoint_eq
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    (suffixActualBandForwardCoframe lambda S)† =
      (sourceInclusion lambda)† ∘L
        (normalizedFiniteEulerInverseList S)† ∘L
          sourceBandProjection lambda := by
  rw [suffixActualBandForwardCoframe, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_comp]
  have hBand :=
    (sourceBandProjection_isStarProjection lambda).isSelfAdjoint.adjoint_eq
  rw [hBand]
  apply ContinuousLinearMap.ext
  intro u
  rfl

/-- The complete right coframe used by the raw physical response. -/
noncomputable def suffixActualBandForwardEndpointCoframe
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    sourceSoninCarrier lambda →L[ℂ] finiteSCarrier :=
  suffixActualBandForwardCoframe lambda S +
    suffixActualBandMetricCoframe lambda S

theorem suffixActualBandFrame_eq_transport_comp_inclusion
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    suffixActualBandFrame lambda S =
      suffixActualBandTransportOperator S ∘L sourceInclusion lambda := by
  rw [suffixActualBandFrame,
    CCM24FiniteSFrameGramCalculus.parameterizedSoninFrame,
    suffixActualBandTransportOperator, parameterizedFiniteEulerFactor_one]
  rfl

theorem suffixActualBandGram_eq_compressedAmbientGram
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    CCM24FiniteSFrameGramCalculus.parameterizedSoninGram lambda 1 S =
      (sourceInclusion lambda)† ∘L suffixActualBandAmbientGram S ∘L
        sourceInclusion lambda := by
  rw [CCM24FiniteSFrameGramCalculus.parameterizedSoninGram]
  change (suffixActualBandFrame lambda S)† ∘L
      suffixActualBandFrame lambda S = _
  rw [suffixActualBandFrame_eq_transport_comp_inclusion,
    suffixActualBandAmbientGram, ContinuousLinearMap.adjoint_comp]
  apply ContinuousLinearMap.ext
  intro u
  rfl

theorem suffixActualBandFrameAdjoint_detector_frame_eq
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    (suffixActualBandFrame lambda S)† ∘L detectorOperator owner ∘L
        suffixActualBandFrame lambda S =
      (sourceInclusion lambda)† ∘L detectorOperator owner ∘L
        suffixActualBandAmbientGram S ∘L sourceInclusion lambda := by
  rw [suffixActualBandFrame_eq_transport_comp_inclusion,
    suffixActualBandAmbientGram, ContinuousLinearMap.adjoint_comp]
  have h := finiteEulerTransportAdjoint_comp_detector owner S
  apply ContinuousLinearMap.ext
  intro u
  have hu := congrArg
    (fun operator : GlobalOp =>
      operator (suffixActualBandTransportOperator S
        (sourceInclusion lambda u))) h
  simpa only [suffixActualBandTransportOperator,
    ContinuousLinearMap.comp_apply] using congrArg
      ((sourceInclusion lambda)†) hu

/-- The centered suffix Gram numerator before applying `G_S⁻¹`. -/
noncomputable def suffixActualBandCenteredGramNumerator
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    SourceOp lambda :=
  (suffixActualBandFrame lambda S)† ∘L detectorOperator owner ∘L
      suffixActualBandFrame lambda S -
    ((sourceInclusion lambda)† ∘L detectorOperator owner ∘L
      sourceInclusion lambda) ∘L
        CCM24FiniteSFrameGramCalculus.parameterizedSoninGram lambda 1 S

theorem suffixActualBandCenteredGramNumerator_eq_fixedBoundary
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    suffixActualBandCenteredGramNumerator owner lambda S =
      (sourceInclusion lambda)† ∘L detectorOperator owner ∘L
        (ContinuousLinearMap.id ℂ finiteSCarrier -
          sourceSoninProjection lambda) ∘L
        suffixActualBandAmbientGram S ∘L sourceInclusion lambda := by
  rw [suffixActualBandCenteredGramNumerator,
    suffixActualBandFrameAdjoint_detector_frame_eq,
    suffixActualBandGram_eq_compressedAmbientGram,
    ← sourceInclusion_comp_adjoint]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, map_sub]

theorem suffixActualBandCenteredGramNumerator_eq_threeBranch
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    suffixActualBandCenteredGramNumerator owner lambda S =
      (sourceInclusion lambda)† ∘L
        cc20ThreeBranchCommutator (radialSupportProjection lambda)
          (sourceFourierSupportProjection lambda)
          (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
        suffixActualBandAmbientGram S ∘L sourceInclusion lambda := by
  rw [suffixActualBandCenteredGramNumerator_eq_fixedBoundary]
  apply ContinuousLinearMap.ext
  intro u
  have h := congrArg
    (fun operator : finiteSCarrier →L[ℂ] sourceSoninCarrier lambda =>
      operator (suffixActualBandAmbientGram S (sourceInclusion lambda u)))
    (inclusionAdjoint_detector_complement_eq_neg_commutator owner lambda)
  rw [sourceBoundaryCommutator_eq_neg_threeBranch] at h
  simpa only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.neg_apply, map_neg, neg_neg] using h

/-- The route-oriented suffix endpoint response before changing its sign. -/
noncomputable def suffixActualBandSourceGramResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    SourceOp lambda :=
  ((suffixActualBandFrame lambda S)† ∘L detectorOperator owner ∘L
      suffixActualBandFrame lambda S) ∘L
        suffixActualBandGramInv lambda S -
    (sourceInclusion lambda)† ∘L detectorOperator owner ∘L
      sourceInclusion lambda

theorem suffixActualBandSourceGramResponse_eq_centered
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    suffixActualBandSourceGramResponse owner lambda S =
      suffixActualBandCenteredGramNumerator owner lambda S ∘L
        suffixActualBandGramInv lambda S := by
  rw [suffixActualBandSourceGramResponse,
    suffixActualBandCenteredGramNumerator]
  have hright := parameterizedSoninGram_mul_gramInv
    lambda 1 S (by norm_num)
  apply ContinuousLinearMap.ext
  intro u
  have hu := congrArg
    (fun operator : SourceOp lambda => operator u) hright
  simp only [suffixActualBandGramInv, ContinuousLinearMap.mul_def,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.one_apply] at hu ⊢
  rw [hu]

theorem suffixActualBandSourceGramResponse_eq_threeBranch
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    suffixActualBandSourceGramResponse owner lambda S =
      (sourceInclusion lambda)† ∘L
        cc20ThreeBranchCommutator (radialSupportProjection lambda)
          (sourceFourierSupportProjection lambda)
          (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
        suffixActualBandMetricCoframe lambda S := by
  rw [suffixActualBandSourceGramResponse_eq_centered,
    suffixActualBandCenteredGramNumerator_eq_threeBranch]
  apply ContinuousLinearMap.ext
  intro u
  rfl

theorem suffixActualBandEndpointCycledResponse_eq_neg_threeBranch
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    suffixActualBandEndpointCycledResponse owner lambda S =
      -((sourceInclusion lambda)† ∘L
        cc20ThreeBranchCommutator (radialSupportProjection lambda)
          (sourceFourierSupportProjection lambda)
          (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
        suffixActualBandMetricCoframe lambda S) := by
  rw [← suffixActualBandSourceGramResponse_eq_threeBranch]
  rw [suffixActualBandEndpointCycledResponse,
    suffixActualBandSourceGramResponse,
    actualBandBaseRootLeg, suffixActualBandTargetFrameRootLeg,
    suffixActualBandTargetDualRootLeg,
    detectorOperator_eq_rootConvolution_adjoint_comp_rootConvolution]
  apply ContinuousLinearMap.ext
  intro u
  simp only [suffixActualBandFrame, suffixActualBandGramInv,
    ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.neg_apply]
  abel

/-! ## Family-free first-jet physical response -/

/-- The ambient paired first jet for an arbitrary suffix list. -/
noncomputable def suffixActualBandFiniteEulerPairedResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) : GlobalOp :=
  actualBandDetectorPairedResponse (sourceBandProjection lambda)
    (sourceSoninProjection lambda)
    (compressedDetector (radialSupportProjection lambda)
      (detectorOperator owner))
    (normalizedFiniteEulerInverseList S)
    ((normalizedFiniteEulerInverseList S)†)

theorem suffixActualBandFiniteEulerPairedResponse_eq_rawDetector
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    suffixActualBandFiniteEulerPairedResponse owner lambda S =
      actualBandDetectorPairedResponse (sourceBandProjection lambda)
        (sourceSoninProjection lambda) (detectorOperator owner)
        (normalizedFiniteEulerInverseList S)
        ((normalizedFiniteEulerInverseList S)†) := by
  have hInnerSupport : sourceSoninProjection lambda *
      radialSupportProjection lambda = sourceSoninProjection lambda := by
    simpa only [ContinuousLinearMap.mul_def] using
      sourceSoninProjection_comp_radialSupportProjection lambda
  have hSupportInner : radialSupportProjection lambda *
      sourceSoninProjection lambda = sourceSoninProjection lambda := by
    simpa only [ContinuousLinearMap.mul_def] using
      radialSupportProjection_comp_sourceSoninProjection lambda
  have hBandSupport : sourceBandProjection lambda *
      radialSupportProjection lambda = sourceBandProjection lambda := by
    simpa only [ContinuousLinearMap.mul_def] using
      sourceBandProjection_comp_radialSupportProjection_eq_self lambda
  have hSupportBand : radialSupportProjection lambda *
      sourceBandProjection lambda = sourceBandProjection lambda := by
    simpa only [ContinuousLinearMap.mul_def] using
      radialSupportProjection_comp_sourceBandProjection_eq_self lambda
  have hForwardDetector :
      sourceSoninProjection lambda *
          (radialSupportProjection lambda * detectorOperator owner *
            radialSupportProjection lambda) *
          sourceBandProjection lambda =
        sourceSoninProjection lambda * detectorOperator owner *
          sourceBandProjection lambda := by
    calc
      _ = (sourceSoninProjection lambda * radialSupportProjection lambda) *
          detectorOperator owner *
            (radialSupportProjection lambda * sourceBandProjection lambda) := by
              noncomm_ring
      _ = _ := by rw [hInnerSupport, hSupportBand]
  have hReverseDetector :
      sourceBandProjection lambda *
          (radialSupportProjection lambda * detectorOperator owner *
            radialSupportProjection lambda) *
          sourceSoninProjection lambda =
        sourceBandProjection lambda * detectorOperator owner *
          sourceSoninProjection lambda := by
    calc
      _ = (sourceBandProjection lambda * radialSupportProjection lambda) *
          detectorOperator owner *
            (radialSupportProjection lambda * sourceSoninProjection lambda) := by
              noncomm_ring
      _ = _ := by rw [hBandSupport, hSupportInner]
  unfold suffixActualBandFiniteEulerPairedResponse
    actualBandDetectorPairedResponse compressedDetector
  simpa only [ContinuousLinearMap.mul_def] using show
    sourceSoninProjection lambda *
            (radialSupportProjection lambda * detectorOperator owner *
              radialSupportProjection lambda) *
            sourceBandProjection lambda *
          normalizedFiniteEulerInverseList S * sourceSoninProjection lambda +
        sourceSoninProjection lambda *
            (normalizedFiniteEulerInverseList S)† *
            sourceBandProjection lambda *
          (radialSupportProjection lambda * detectorOperator owner *
            radialSupportProjection lambda) *
          sourceSoninProjection lambda =
      sourceSoninProjection lambda * detectorOperator owner *
            sourceBandProjection lambda *
          normalizedFiniteEulerInverseList S * sourceSoninProjection lambda +
        sourceSoninProjection lambda *
            (normalizedFiniteEulerInverseList S)† *
          sourceBandProjection lambda * detectorOperator owner *
          sourceSoninProjection lambda by
    calc
      _ = (sourceSoninProjection lambda *
              (radialSupportProjection lambda * detectorOperator owner *
                radialSupportProjection lambda) *
              sourceBandProjection lambda) *
            normalizedFiniteEulerInverseList S *
            sourceSoninProjection lambda +
          sourceSoninProjection lambda *
            (normalizedFiniteEulerInverseList S)† *
            (sourceBandProjection lambda *
              (radialSupportProjection lambda * detectorOperator owner *
                radialSupportProjection lambda) *
              sourceSoninProjection lambda) := by
                noncomm_ring
      _ = (sourceSoninProjection lambda * detectorOperator owner *
              sourceBandProjection lambda) *
            normalizedFiniteEulerInverseList S *
            sourceSoninProjection lambda +
          sourceSoninProjection lambda *
            (normalizedFiniteEulerInverseList S)† *
            (sourceBandProjection lambda * detectorOperator owner *
              sourceSoninProjection lambda) := by
        rw [hForwardDetector, hReverseDetector]
      _ = _ := by noncomm_ring

theorem suffixActualBandFiniteEulerPairedResponse_eq_threeBranch
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    suffixActualBandFiniteEulerPairedResponse owner lambda S =
      sourceSoninProjection lambda ∘L
          cc20ThreeBranchCommutator (radialSupportProjection lambda)
            (sourceFourierSupportProjection lambda)
            (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
          sourceBandProjection lambda ∘L
          normalizedFiniteEulerInverseList S ∘L
          sourceSoninProjection lambda -
        sourceSoninProjection lambda ∘L
          (normalizedFiniteEulerInverseList S)† ∘L
          sourceBandProjection lambda ∘L
          cc20ThreeBranchCommutator (radialSupportProjection lambda)
            (sourceFourierSupportProjection lambda)
            (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
          sourceSoninProjection lambda := by
  let band := sourceBandProjection lambda
  let inner := sourceSoninProjection lambda
  let detector := compressedDetector (radialSupportProjection lambda)
    (detectorOperator owner)
  let transport := normalizedFiniteEulerInverseList S
  let transportAdjoint := (normalizedFiniteEulerInverseList S)†
  let fixed := fixedPhysicalCommutator (radialSupportProjection lambda)
    (sourceFourierSupportProjection lambda) (sourceProlateRemainder lambda)
    (detectorOperator owner)
  have hdecomp :
      suffixActualBandFiniteEulerPairedResponse owner lambda S =
        -(inner ∘L fixed ∘L band ∘L transport ∘L inner) +
          inner ∘L transportAdjoint ∘L band ∘L fixed ∘L inner := by
    rw [suffixActualBandFiniteEulerPairedResponse]
    rw [← actualBandCommutatorPairedResponse_eq_detector band inner detector
      transport transportAdjoint
      (sourceSoninProjection_isStarProjection lambda).isIdempotentElem
      (by simpa only [band, inner, ContinuousLinearMap.mul_def] using
        sourceBandProjection_comp_sourceSoninProjection_eq_zero lambda)
      (by simpa only [band, inner, ContinuousLinearMap.mul_def] using
        sourceSoninProjection_comp_sourceBandProjection_eq_zero lambda)]
    unfold actualBandCommutatorPairedResponse
    rw [← fixedPhysicalCommutator_eq_sourceCompressedCommutator owner lambda]
    rfl
  rw [hdecomp]
  simpa only [band, inner, transport, transportAdjoint, fixed,
      ContinuousLinearMap.mul_def] using
    (pairedFixedResponse_eq_threeBranch
      (sourceSoninProjection lambda) (sourceBandProjection lambda)
      (normalizedFiniteEulerInverseList S)
      ((normalizedFiniteEulerInverseList S)†)
      (radialSupportProjection lambda)
      (cc20ThreeBranchCommutator (radialSupportProjection lambda)
        (sourceFourierSupportProjection lambda)
        (sourceProlateRemainder lambda) (detectorOperator owner))
      (fixedPhysicalCommutator (radialSupportProjection lambda)
        (sourceFourierSupportProjection lambda)
        (sourceProlateRemainder lambda) (detectorOperator owner))
      (by simpa only [ContinuousLinearMap.mul_def] using
        (fixedPhysicalCommutator_eq_neg_compressedThreeBranch
          (radialSupportProjection lambda)
          (sourceFourierSupportProjection lambda)
          (sourceProlateRemainder lambda) (detectorOperator owner)
          (radialSupportProjection_isStarProjection lambda).isIdempotentElem
          (radialSupportProjection_comp_sourceProlateRemainder lambda)
          (sourceProlateRemainder_comp_radialSupportProjection lambda)))
      (by simpa only [ContinuousLinearMap.mul_def] using
        sourceSoninProjection_comp_radialSupportProjection lambda)
      (by simpa only [ContinuousLinearMap.mul_def] using
        radialSupportProjection_comp_sourceBandProjection_eq_self lambda)
      (by simpa only [ContinuousLinearMap.mul_def] using
        sourceBandProjection_comp_radialSupportProjection_eq_self lambda)
      (by simpa only [ContinuousLinearMap.mul_def] using
        radialSupportProjection_comp_sourceSoninProjection lambda))

/-- Pullback of the ambient suffix first jet to the source carrier. -/
noncomputable def suffixActualBandFiniteEulerSoninResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    SourceOp lambda :=
  (sourceInclusion lambda)† ∘L
    suffixActualBandFiniteEulerPairedResponse owner lambda S ∘L
      sourceInclusion lambda

theorem suffixActualBandFiniteEulerSoninResponse_eq_firstJetCycle
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    suffixActualBandFiniteEulerSoninResponse owner lambda S =
      suffixActualBandFirstJetCycledResponse owner lambda S := by
  rw [suffixActualBandFiniteEulerSoninResponse,
    suffixActualBandFiniteEulerPairedResponse_eq_rawDetector,
    detectorOperator_eq_rootConvolution_adjoint_comp_rootConvolution]
  apply ContinuousLinearMap.ext
  intro u
  have hright := congrArg
    (fun operator : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier =>
      operator u)
    (sourceSoninProjection_comp_sourceInclusion_eq_self lambda)
  simp only [ContinuousLinearMap.comp_apply] at hright
  have hleft (x : finiteSCarrier) :
      ((sourceInclusion lambda)†) (sourceSoninProjection lambda x) =
        ((sourceInclusion lambda)†) x := by
    exact congrArg
      (fun operator : finiteSCarrier →L[ℂ] sourceSoninCarrier lambda =>
        operator x)
      (sourceInclusionAdjoint_comp_sourceProjection lambda)
  simp only [suffixActualBandFirstJetCycledResponse,
    actualBandBaseRootLeg, suffixActualBandJetRootLeg,
    actualBandDetectorPairedResponse, ContinuousLinearMap.mul_def,
    ContinuousLinearMap.adjoint_comp,
    (sourceBandProjection_isStarProjection lambda).isSelfAdjoint.adjoint_eq,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply, map_add]
  rw [hright, hleft, hleft]

theorem suffixActualBandFiniteEulerSoninResponse_eq_commonPhysicalFirstJet
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    suffixActualBandFiniteEulerSoninResponse owner lambda S =
      (sourceInclusion lambda)† ∘L
          cc20ThreeBranchCommutator (radialSupportProjection lambda)
            (sourceFourierSupportProjection lambda)
            (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
          suffixActualBandForwardCoframe lambda S -
        (suffixActualBandForwardCoframe lambda S)† ∘L
          cc20ThreeBranchCommutator (radialSupportProjection lambda)
            (sourceFourierSupportProjection lambda)
            (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
          sourceInclusion lambda := by
  rw [suffixActualBandFiniteEulerSoninResponse,
    suffixActualBandFiniteEulerPairedResponse_eq_threeBranch,
    suffixActualBandForwardCoframe_adjoint_eq]
  apply ContinuousLinearMap.ext
  intro u
  have hright := congrArg
    (fun operator : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier =>
      operator u)
    (sourceSoninProjection_comp_sourceInclusion_eq_self lambda)
  have hleft (x : finiteSCarrier) :
      ((sourceInclusion lambda)†) (sourceSoninProjection lambda x) =
        ((sourceInclusion lambda)†) x := by
    exact congrArg
      (fun operator : finiteSCarrier →L[ℂ] sourceSoninCarrier lambda =>
        operator x)
      (sourceInclusionAdjoint_comp_sourceProjection lambda)
  simp only [suffixActualBandForwardCoframe,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply, map_sub]
  rw [show sourceSoninProjection lambda (sourceInclusion lambda u) =
      sourceInclusion lambda u by
    simpa only [ContinuousLinearMap.comp_apply] using hright,
    hleft, hleft]

/-! ## Complete suffix physical response -/

/-- The raw suffix remainder with both orientations on one physical ledger. -/
noncomputable def suffixActualBandRawCommonPhysicalResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    SourceOp lambda :=
  (sourceInclusion lambda)† ∘L
      cc20ThreeBranchCommutator (radialSupportProjection lambda)
        (sourceFourierSupportProjection lambda)
        (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
      suffixActualBandForwardEndpointCoframe lambda S -
    (suffixActualBandForwardCoframe lambda S)† ∘L
      cc20ThreeBranchCommutator (radialSupportProjection lambda)
        (sourceFourierSupportProjection lambda)
        (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
      sourceInclusion lambda

theorem suffixActualBandRawCommonPhysicalResponse_eq_raw
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    suffixActualBandRawCommonPhysicalResponse owner lambda S =
      suffixActualBandRawQuadraticCycledResponse owner lambda S := by
  rw [suffixActualBandRawQuadraticCycledResponse,
    ← suffixActualBandFiniteEulerSoninResponse_eq_firstJetCycle,
    suffixActualBandFiniteEulerSoninResponse_eq_commonPhysicalFirstJet,
    suffixActualBandEndpointCycledResponse_eq_neg_threeBranch]
  apply ContinuousLinearMap.ext
  intro u
  simp only [suffixActualBandRawCommonPhysicalResponse,
    suffixActualBandForwardEndpointCoframe,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.neg_apply, map_add]
  abel

/-! ## Complete Hilbert--Schmidt owner for every suffix -/

/-- The forward first jet and endpoint coframe share the same complete
four-branch left leg for an arbitrary literal suffix. -/
noncomputable def suffixActualBandForwardEndpointPairData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {iota kappa tau iotaR kappaR tauR nu mu rho : Type*}
    (negativeBasis : HilbertBasis iota ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis kappa ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis tau ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis iotaR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis kappaR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis tauR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis mu ℂ (commonBoundaryCarrier a c))
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    BasisHilbertSchmidtPairData
      (G := commonBoundaryCarrier a c) sourceBasis :=
  boundedPrecompAddRight boundaryBasis sourceBasis
    (sourceThreeBranchPairData owner lambda a c hac hsupp negativeBasis
      positiveBasis outputBasis reflectedNegativeBasis reflectedPositiveBasis
      reflectedOutputBasis globalBasis hfactor)
    (sourceInclusion lambda)
    (suffixActualBandForwardCoframe lambda S)
    (suffixActualBandMetricCoframe lambda S)

theorem suffixActualBandForwardEndpointPairData_traceProduct_eq
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {iota kappa tau iotaR kappaR tauR nu mu rho : Type*}
    (negativeBasis : HilbertBasis iota ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis kappa ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis tau ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis iotaR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis kappaR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis tauR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis mu ℂ (commonBoundaryCarrier a c))
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    (suffixActualBandForwardEndpointPairData owner lambda S a c hac hsupp
      negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
      sourceBasis hfactor).traceProduct =
        (sourceInclusion lambda)† ∘L
          cc20ThreeBranchCommutator (radialSupportProjection lambda)
            (sourceFourierSupportProjection lambda)
            (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
          suffixActualBandForwardEndpointCoframe lambda S := by
  rw [suffixActualBandForwardEndpointPairData,
    boundedPrecompAddRight_traceProduct_eq,
    sourceThreeBranchPairData_traceProduct_eq owner lambda a c hac hsupp
      negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor]
  rfl

/-- Both orientations of the suffix response as one genuine
Hilbert--Schmidt pair. -/
noncomputable def suffixActualBandRawCommonPairData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {iota kappa tau iotaR kappaR tauR nu mu rho : Type*}
    (negativeBasis : HilbertBasis iota ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis kappa ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis tau ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis iotaR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis kappaR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis tauR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis mu ℂ (commonBoundaryCarrier a c))
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    BasisHilbertSchmidtPairData
      (G := WithLp 2
        (commonBoundaryCarrier a c × commonBoundaryCarrier a c)) sourceBasis :=
  BasisHilbertSchmidtPairData.l2Sum
    (suffixActualBandForwardEndpointPairData owner lambda S a c hac hsupp
      negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
      sourceBasis hfactor)
    ((BasisHilbertSchmidtPairData.boundedPrecomp boundaryBasis sourceBasis
      (sourceThreeBranchPairData owner lambda a c hac hsupp negativeBasis
        positiveBasis outputBasis reflectedNegativeBasis reflectedPositiveBasis
        reflectedOutputBasis globalBasis hfactor)
      (suffixActualBandForwardCoframe lambda S)
      (sourceInclusion lambda)).smulRight (-1))

theorem suffixActualBandRawCommonPairData_traceProduct_eq
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {iota kappa tau iotaR kappaR tauR nu mu rho : Type*}
    (negativeBasis : HilbertBasis iota ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis kappa ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis tau ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis iotaR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis kappaR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis tauR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis mu ℂ (commonBoundaryCarrier a c))
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    (suffixActualBandRawCommonPairData owner lambda S a c hac hsupp
      negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
      sourceBasis hfactor).traceProduct =
        suffixActualBandRawCommonPhysicalResponse owner lambda S := by
  rw [suffixActualBandRawCommonPairData,
    BasisHilbertSchmidtPairData.l2Sum_traceProduct_eq_add,
    suffixActualBandForwardEndpointPairData_traceProduct_eq owner lambda S
      a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis sourceBasis hfactor,
    BasisHilbertSchmidtPairData.smulRight_traceProduct_eq,
    BasisHilbertSchmidtPairData.boundedPrecomp_traceProduct_eq,
    sourceThreeBranchPairData_traceProduct_eq owner lambda a c hac hsupp
      negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor]
  apply ContinuousLinearMap.ext
  intro u
  simp only [suffixActualBandRawCommonPhysicalResponse,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    neg_smul, one_smul, ContinuousLinearMap.neg_apply, sub_eq_add_neg]

theorem suffixActualBandRawCommonPairData_traceProduct_eq_raw
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {iota kappa tau iotaR kappaR tauR nu mu rho : Type*}
    (negativeBasis : HilbertBasis iota ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis kappa ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis tau ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis iotaR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis kappaR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis tauR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis mu ℂ (commonBoundaryCarrier a c))
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    (suffixActualBandRawCommonPairData owner lambda S a c hac hsupp
      negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
      sourceBasis hfactor).traceProduct =
        suffixActualBandRawQuadraticCycledResponse owner lambda S := by
  rw [suffixActualBandRawCommonPairData_traceProduct_eq,
    suffixActualBandRawCommonPhysicalResponse_eq_raw]

theorem suffixActualBandRawQuadraticCycledResponse_isTraceClassAlong
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {iota kappa tau iotaR kappaR tauR nu mu rho : Type*}
    (negativeBasis : HilbertBasis iota ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis kappa ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis tau ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis iotaR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis kappaR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis tauR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis mu ℂ (commonBoundaryCarrier a c))
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    IsTraceClassAlong sourceBasis
      (suffixActualBandRawQuadraticCycledResponse owner lambda S) := by
  rw [← suffixActualBandRawCommonPairData_traceProduct_eq_raw owner lambda S
    a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis sourceBasis hfactor]
  exact (suffixActualBandRawCommonPairData owner lambda S a c hac hsupp
    negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
    sourceBasis hfactor).traceProduct_isTraceClassAlong

/-! ## Legal scalar sandwich cycle -/

/-- A bounded sandwich of an owned `A†B` product may be collapsed when the
reverse and forward dressings multiply to a scalar.  Both changes of cut are
genuine Hilbert--Schmidt trace cycles. -/
theorem ordinaryTraceAlong_boundedSandwich_eq_scalar
    {H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {iota kappa : Type*} {sourceBasis : HilbertBasis iota ℂ H}
    (targetBasis : HilbertBasis kappa ℂ G)
    (data : BasisHilbertSchmidtPairData (G := G) sourceBasis)
    (forward reverse : H →L[ℂ] H) (scalar : ℂ)
    (hpair : reverse ∘L forward =
      scalar • ContinuousLinearMap.id ℂ H) :
    ordinaryTraceAlong sourceBasis
        (forward ∘L data.traceProduct ∘L reverse) =
      scalar * ordinaryTraceAlong sourceBasis data.traceProduct := by
  let sandwiched := data.boundedSandwich targetBasis forward reverse
  let cycled : BasisHilbertSchmidtPairData (G := H) targetBasis :=
    { left := data.right.adjoint
      right := data.left.adjoint
      left_summable_normSq :=
        BasisHilbertSchmidtPairData.summable_adjoint_normSq
          sourceBasis targetBasis data.right data.right_summable_normSq
      right_summable_normSq :=
        BasisHilbertSchmidtPairData.summable_adjoint_normSq
          sourceBasis targetBasis data.left data.left_summable_normSq }
  have hSandwichedProduct : sandwiched.traceProduct =
      forward ∘L data.traceProduct ∘L reverse := by
    exact data.boundedSandwich_traceProduct_eq targetBasis forward reverse
  have hSandwichedCycle :=
    sandwiched.ordinaryTraceAlong_traceProduct_eq_cyclic targetBasis
  have hDataCycle :=
    data.ordinaryTraceAlong_traceProduct_eq_cyclic targetBasis
  have hCycleOperator :
      sandwiched.right ∘L sandwiched.left.adjoint =
        scalar • (data.right ∘L data.left.adjoint) := by
    have hu (u : G) := congrArg
      (fun operator : H →L[ℂ] H => operator (data.left.adjoint u)) hpair
    apply ContinuousLinearMap.ext
    intro u
    specialize hu u
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply] at hu
    dsimp only [sandwiched,
      BasisHilbertSchmidtPairData.boundedSandwich]
    rw [ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint]
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smul_apply, hu, map_smul]
  have hCycledProduct : cycled.traceProduct =
      data.right ∘L data.left.adjoint := by
    dsimp only [cycled, BasisHilbertSchmidtPairData.traceProduct]
    rw [ContinuousLinearMap.adjoint_adjoint]
  have hTargetTraceClass : IsTraceClassAlong targetBasis
      (data.right ∘L data.left.adjoint) := by
    rw [← hCycledProduct]
    exact cycled.traceProduct_isTraceClassAlong
  calc
    ordinaryTraceAlong sourceBasis
        (forward ∘L data.traceProduct ∘L reverse) =
        ordinaryTraceAlong sourceBasis sandwiched.traceProduct := by
          rw [hSandwichedProduct]
    _ = ordinaryTraceAlong targetBasis
        (sandwiched.right ∘L sandwiched.left.adjoint) := hSandwichedCycle
    _ = ordinaryTraceAlong targetBasis
        (scalar • (data.right ∘L data.left.adjoint)) := by
          rw [hCycleOperator]
    _ = scalar * ordinaryTraceAlong targetBasis
        (data.right ∘L data.left.adjoint) :=
      ordinaryTraceAlong_smul targetBasis scalar _ hTargetTraceClass
    _ = scalar * ordinaryTraceAlong sourceBasis data.traceProduct := by
      rw [hDataCycle]

/-! ## Pair owner for each local raw defect -/

/-- The local raw defect keeps its larger-suffix term and transported
smaller-suffix term in two orthogonal coordinates. -/
noncomputable def suffixActualBandLocalRawDefectPairData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {iota kappa tau iotaR kappaR tauR nu mu rho sigma : Type*}
    (negativeBasis : HilbertBasis iota ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis kappa ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis tau ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis iotaR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis kappaR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis tauR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis mu ℂ (commonBoundaryCarrier a c))
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (pairedBoundaryBasis : HilbertBasis sigma ℂ
      (WithLp 2 (commonBoundaryCarrier a c × commonBoundaryCarrier a c)))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    BasisHilbertSchmidtPairData
      (G := WithLp 2
        (WithLp 2
            (commonBoundaryCarrier a c × commonBoundaryCarrier a c) ×
          WithLp 2
            (commonBoundaryCarrier a c × commonBoundaryCarrier a c)))
      sourceBasis :=
  BasisHilbertSchmidtPairData.l2Sum
    ((suffixActualBandRawCommonPairData owner lambda (p :: S) a c hac hsupp
      negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
      sourceBasis hfactor).smulRight (primeSchurMarkovScalar p : ℂ))
    (((suffixActualBandRawCommonPairData owner lambda S a c hac hsupp
      negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
      sourceBasis hfactor).boundedSandwich pairedBoundaryBasis
        (suffixEulerFrameTransition lambda p S)
        (suffixEulerFrameReverseTransition lambda p S)).smulRight (-1))

theorem suffixActualBandLocalRawDefectPairData_traceProduct_eq
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {iota kappa tau iotaR kappaR tauR nu mu rho sigma : Type*}
    (negativeBasis : HilbertBasis iota ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis kappa ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis tau ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis iotaR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis kappaR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis tauR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis mu ℂ (commonBoundaryCarrier a c))
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (pairedBoundaryBasis : HilbertBasis sigma ℂ
      (WithLp 2 (commonBoundaryCarrier a c × commonBoundaryCarrier a c)))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    (suffixActualBandLocalRawDefectPairData owner lambda p S a c hac hsupp
      negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
      sourceBasis pairedBoundaryBasis hfactor).traceProduct =
        suffixActualBandLocalRawDefect owner lambda p S := by
  rw [suffixActualBandLocalRawDefectPairData,
    BasisHilbertSchmidtPairData.l2Sum_traceProduct_eq_add,
    BasisHilbertSchmidtPairData.smulRight_traceProduct_eq,
    BasisHilbertSchmidtPairData.smulRight_traceProduct_eq,
    BasisHilbertSchmidtPairData.boundedSandwich_traceProduct_eq,
    suffixActualBandRawCommonPairData_traceProduct_eq_raw owner lambda
      (p :: S) a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis sourceBasis hfactor,
    suffixActualBandRawCommonPairData_traceProduct_eq_raw owner lambda S
      a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis sourceBasis hfactor]
  apply ContinuousLinearMap.ext
  intro u
  simp only [suffixActualBandLocalRawDefect,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.neg_apply, neg_smul, one_smul, sub_eq_add_neg]

theorem suffixActualBandLocalRawDefect_isTraceClassAlong
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {iota kappa tau iotaR kappaR tauR nu mu rho sigma : Type*}
    (negativeBasis : HilbertBasis iota ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis kappa ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis tau ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis iotaR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis kappaR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis tauR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis mu ℂ (commonBoundaryCarrier a c))
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (pairedBoundaryBasis : HilbertBasis sigma ℂ
      (WithLp 2 (commonBoundaryCarrier a c × commonBoundaryCarrier a c)))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    IsTraceClassAlong sourceBasis
      (suffixActualBandLocalRawDefect owner lambda p S) := by
  rw [← suffixActualBandLocalRawDefectPairData_traceProduct_eq owner lambda p
    S a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis sourceBasis pairedBoundaryBasis hfactor]
  exact (suffixActualBandLocalRawDefectPairData owner lambda p S a c hac hsupp
    negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
    sourceBasis pairedBoundaryBasis hfactor).traceProduct_isTraceClassAlong

/-! ## Ordinary-trace local and list-level collapse -/

section SuffixTraceReadout

variable (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
variable (lambda : CCM24SoninScale)
variable (a c : ℝ) (hac : a ≤ c)
variable (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
variable {iota kappa tau iotaR kappaR tauR nu mu rho sigma : Type*}
variable (negativeBasis : HilbertBasis iota ℂ
  (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
variable (positiveBasis : HilbertBasis kappa ℂ
  (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
variable (outputBasis : HilbertBasis tau ℂ
  (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
variable (reflectedNegativeBasis : HilbertBasis iotaR ℂ
  (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
variable (reflectedPositiveBasis : HilbertBasis kappaR ℂ
  (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
variable (reflectedOutputBasis : HilbertBasis tauR ℂ
  (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
variable (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
variable (boundaryBasis : HilbertBasis mu ℂ (commonBoundaryCarrier a c))
variable (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
variable (pairedBoundaryBasis : HilbertBasis sigma ℂ
  (WithLp 2 (commonBoundaryCarrier a c × commonBoundaryCarrier a c)))
variable (hfactor : Summable fun i =>
  ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)

include a c hac hsupp negativeBasis positiveBasis outputBasis
  reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
  globalBasis boundaryBasis pairedBoundaryBasis hfactor

/-- The actual one-step Schur--Markov sandwich collapses by two legal
Hilbert--Schmidt trace cycles. -/
theorem ordinaryTraceAlong_suffixActualBandTransitionSandwich_eq
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime) :
    ordinaryTraceAlong sourceBasis
        (suffixEulerFrameTransition lambda p S ∘L
          suffixActualBandRawQuadraticCycledResponse owner lambda S ∘L
          suffixEulerFrameReverseTransition lambda p S) =
      (primeSchurMarkovScalar p : ℂ) *
        ordinaryTraceAlong sourceBasis
          (suffixActualBandRawQuadraticCycledResponse owner lambda S) := by
  let data := suffixActualBandRawCommonPairData owner lambda S a c hac hsupp
    negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
    sourceBasis hfactor
  have hdata : data.traceProduct =
      suffixActualBandRawQuadraticCycledResponse owner lambda S := by
    exact suffixActualBandRawCommonPairData_traceProduct_eq_raw owner lambda S
      a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis sourceBasis hfactor
  rw [← hdata]
  exact ordinaryTraceAlong_boundedSandwich_eq_scalar pairedBoundaryBasis data
    (suffixEulerFrameTransition lambda p S)
    (suffixEulerFrameReverseTransition lambda p S)
    (primeSchurMarkovScalar p : ℂ)
    (suffixEulerFrameReverse_comp_transition lambda p S)

/-- The ordinary trace of a local raw defect is the one-prime scalar times
the adjacent difference of raw suffix traces. -/
theorem ordinaryTraceAlong_suffixActualBandLocalRawDefect_eq
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime) :
    ordinaryTraceAlong sourceBasis
        (suffixActualBandLocalRawDefect owner lambda p S) =
      (primeSchurMarkovScalar p : ℂ) *
        (ordinaryTraceAlong sourceBasis
            (suffixActualBandRawQuadraticCycledResponse owner lambda (p :: S)) -
          ordinaryTraceAlong sourceBasis
            (suffixActualBandRawQuadraticCycledResponse owner lambda S)) := by
  have hNew :=
    suffixActualBandRawQuadraticCycledResponse_isTraceClassAlong owner lambda
      (p :: S) a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis sourceBasis hfactor
  have hOld :=
    suffixActualBandRawQuadraticCycledResponse_isTraceClassAlong owner lambda S
      a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis sourceBasis hfactor
  have hScaled := isTraceClassAlong_smul sourceBasis
    (primeSchurMarkovScalar p : ℂ)
    (suffixActualBandRawQuadraticCycledResponse owner lambda (p :: S)) hNew
  let oldData := suffixActualBandRawCommonPairData owner lambda S a c hac hsupp
    negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
    sourceBasis hfactor
  have hOldData : oldData.traceProduct =
      suffixActualBandRawQuadraticCycledResponse owner lambda S := by
    exact suffixActualBandRawCommonPairData_traceProduct_eq_raw owner lambda S
      a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis sourceBasis hfactor
  have hSandwich : IsTraceClassAlong sourceBasis
      (suffixEulerFrameTransition lambda p S ∘L
        suffixActualBandRawQuadraticCycledResponse owner lambda S ∘L
        suffixEulerFrameReverseTransition lambda p S) := by
    rw [← hOldData]
    exact oldData.boundedSandwich_isTraceClassAlong pairedBoundaryBasis
      (suffixEulerFrameTransition lambda p S)
      (suffixEulerFrameReverseTransition lambda p S)
  rw [suffixActualBandLocalRawDefect]
  rw [ordinaryTraceAlong_sub sourceBasis _ _ hScaled hSandwich]
  rw [ordinaryTraceAlong_smul sourceBasis _ _ hNew]
  rw [ordinaryTraceAlong_suffixActualBandTransitionSandwich_eq owner lambda
    a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis sourceBasis pairedBoundaryBasis hfactor p S]
  ring

/-- One legal local step of Proof 499's relative scalar recurrence. -/
theorem ordinaryTraceAlong_suffixActualBandRaw_cons_eq
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime) :
    ordinaryTraceAlong sourceBasis
        (suffixActualBandRawQuadraticCycledResponse owner lambda (p :: S)) =
      ordinaryTraceAlong sourceBasis
          (suffixActualBandRawQuadraticCycledResponse owner lambda S) +
        (primeSchurMarkovScalar p : ℂ)⁻¹ *
          ordinaryTraceAlong sourceBasis
            (suffixActualBandLocalRawDefect owner lambda p S) := by
  rw [ordinaryTraceAlong_suffixActualBandLocalRawDefect_eq owner lambda
    a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis sourceBasis pairedBoundaryBasis hfactor p S]
  have hp : (primeSchurMarkovScalar p : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (primeSchurMarkovScalar_pos p))
  field_simp [hp]
  ring

/-- The actual ordinary trace instantiates Proof 499's relative collapsed
readout without any unrestricted infinite-dimensional cyclicity hypothesis. -/
theorem ordinaryTraceAlong_suffixActualBandRawResponse_eq_relativeCollapsed
    (S : List CCM24VisiblePrime) :
    ordinaryTraceAlong sourceBasis
        (suffixActualBandRawQuadraticCycledResponse owner lambda S) =
      suffixActualBandRelativeCollapsedTrace owner lambda
        (ordinaryTraceAlong sourceBasis) S := by
  induction S with
  | nil =>
      simp [suffixActualBandRawQuadraticCycledResponse_nil_eq_zero,
        suffixActualBandRelativeCollapsedTrace, ordinaryTraceAlong]
  | cons p S ih =>
      rw [ordinaryTraceAlong_suffixActualBandRaw_cons_eq owner lambda
        a c hac hsupp negativeBasis positiveBasis outputBasis
        reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
        globalBasis boundaryBasis sourceBasis pairedBoundaryBasis hfactor p S]
      rw [suffixActualBandRelativeCollapsedTrace, ih]

/-- Readback on the exact visible-prime list of an arithmetic family. -/
theorem ordinaryTraceAlong_sourceActualBandFiniteEulerRemainderResponse_eq
    (family : FinitePrimePowerFamily) :
    ordinaryTraceAlong sourceBasis
        (sourceActualBandFiniteEulerRemainderResponse owner lambda family) =
      suffixActualBandRelativeCollapsedTrace owner lambda
        (ordinaryTraceAlong sourceBasis) family.visiblePrimes := by
  rw [← suffixActualBandRawQuadraticCycledResponse_eq_actual]
  exact ordinaryTraceAlong_suffixActualBandRawResponse_eq_relativeCollapsed
    owner lambda a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis sourceBasis pairedBoundaryBasis hfactor
    family.visiblePrimes

end SuffixTraceReadout

end CCM24FiniteSRawLocalTraceFactorization
end CCM25Concrete
end Source
end ConnesWeilRH
