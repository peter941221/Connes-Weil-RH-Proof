/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalResidualLedger
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCombinedCoframeGuard
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSRawCompletedSchurCocycle
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSRawLocalTraceFactorization

/-!
# Raw coframe boundary telescope

The physical three-branch operator is the source Sonin commutator
`[R_0,W]`, with `R_0 = J J†`.  Consequently its two off-diagonal corners
are not independent:

```text
[R_0,W] J = -(I-R_0) W J,
J† [R_0,W] F = J† W F
```

for every forward coframe `F` killed by `R_0`.  Applying these identities to
the four-term raw row gives one exact adjacent coframe telescope.  This is
the signed object that must be estimated; estimating its four summands or the
physical coframe residual separately loses this cancellation.

No norm estimate, factorization, Gate 3U bound, sign statement, or RH premise
is introduced here.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedJuliaRawCoframeBoundaryTelescope

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSActualBandQuadraticCycle
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCompletedJuliaRawPhysicalResidualLedger
open CCM24FiniteSCompletedJuliaRawPhysicalFactorization
open CCM24FiniteSCompletedJuliaPolarRawReadout
open CCM24FiniteSGramResponse
open CCM24FiniteSProjectionTrace
open CCM24FiniteSRawRemainderCommonPair
open CCM24FiniteSActualBandSourceRemainder
open CCM24FiniteSRawCompletedSchurCocycle
open CCM24FiniteSRawLocalTraceFactorization
open CCM24FiniteSCombinedCoframeGuard
open CCM24FiniteSCausalMarkov
open CCM24FiniteSRootCompletedFirstJet
open CCM24FiniteSGramInverseCalculus
open CCM24FiniteSSchurMarkovPolarTraceBridge
open CCM24FiniteSFixedQuotientCarrier

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) :
      CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

local notation "SourceOp" lambda =>
  sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda

/-! ## The coframe boundary moment -/

/-- The source complement of the archimedean Sonin projection. -/
noncomputable def sourceSoninComplement
    (lambda : CCM24SoninScale) : finiteSCarrier →L[ℂ] finiteSCarrier :=
  ContinuousLinearMap.id ℂ finiteSCarrier - sourceSoninProjection lambda

/-- The signed boundary moment of a forward/endpoint coframe pair.  The first
coordinate is the endpoint leakage seen by the source commutator; the second
coordinate is the forward coframe crossing. -/
noncomputable def rawCoframeBoundaryMoment
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    (forward endpoint : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier) :
    SourceOp lambda :=
  endpoint† ∘L
      sourceSoninComplement lambda ∘L
      detectorOperator owner ∘L sourceInclusion lambda +
    (sourceInclusion lambda)† ∘L detectorOperator owner ∘L forward

/-! ## Two source-corner identities -/

theorem threeBranch_comp_sourceInclusion_eq_neg_complement_detector_inclusion
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    cc20ThreeBranchCommutator (radialSupportProjection lambda)
        (sourceFourierSupportProjection lambda)
        (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
      sourceInclusion lambda =
      -(sourceSoninComplement lambda ∘L detectorOperator owner ∘L
        sourceInclusion lambda) := by
  have hProjection := sourceSoninProjection_comp_sourceInclusion_eq_self
    lambda
  rw [← sourceSoninCommutator_eq_threeBranch owner lambda]
  unfold cc20Commutator
  apply ContinuousLinearMap.ext
  intro x
  have hpoint := congrArg
    (fun operator : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier =>
      operator x) hProjection
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.id_apply, sourceSoninComplement] at hpoint ⊢
  rw [hpoint]
  abel

theorem sourceInclusionAdjoint_comp_threeBranch_comp_forward_eq
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    (forward : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier)
    (hforward : sourceSoninProjection lambda ∘L forward = 0) :
    (sourceInclusion lambda)† ∘L
        cc20ThreeBranchCommutator (radialSupportProjection lambda)
          (sourceFourierSupportProjection lambda)
          (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
        forward =
      (sourceInclusion lambda)† ∘L detectorOperator owner ∘L forward := by
  have hProjection := sourceInclusionAdjoint_comp_sourceProjection lambda
  rw [← sourceSoninCommutator_eq_threeBranch owner lambda]
  unfold cc20Commutator
  apply ContinuousLinearMap.ext
  intro x
  have hleft := congrArg
    (fun operator : finiteSCarrier →L[ℂ] sourceSoninCarrier lambda =>
      operator (detectorOperator owner (forward x))) hProjection
  have hright := congrArg
    (fun operator : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier =>
      operator x) hforward
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.zero_apply] at hleft hright ⊢
  rw [map_sub, hleft, hright]
  simp only [map_zero, sub_zero]

/-! ## Exact four-term telescope -/

set_option maxHeartbeats 4000000 in
-- The four-term source/ambient normalization needs a larger elaboration budget.
set_option maxRecDepth 10000 in
theorem rawPhysicalFourTermRowOfCoframes_eq_boundaryMoment_telescope
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime)
    (forwardS endpointS endpointPS forwardPS :
      sourceSoninCarrier lambda →L[ℂ] finiteSCarrier)
    (hforwardS : sourceSoninProjection lambda ∘L forwardS = 0)
    (hforwardPS : sourceSoninProjection lambda ∘L forwardPS = 0) :
    rawPhysicalFourTermRowOfCoframes owner lambda p S
        forwardS endpointS endpointPS forwardPS =
      rawCoframeBoundaryMoment owner lambda forwardS endpointS ∘L
          (suffixEulerFrameTransition lambda p S)† -
        (suffixEulerFrameTransition lambda p S)† ∘L
          rawCoframeBoundaryMoment owner lambda forwardPS endpointPS := by
  have hKJ :=
    threeBranch_comp_sourceInclusion_eq_neg_complement_detector_inclusion
      owner lambda
  have hJKforward (forward : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier)
      (hforward : sourceSoninProjection lambda ∘L forward = 0) :
      (sourceInclusion lambda)† ∘L
          cc20ThreeBranchCommutator (radialSupportProjection lambda)
            (sourceFourierSupportProjection lambda)
            (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
          forward =
        (sourceInclusion lambda)† ∘L detectorOperator owner ∘L forward :=
    sourceInclusionAdjoint_comp_threeBranch_comp_forward_eq
      owner lambda forward hforward
  apply ContinuousLinearMap.ext
  intro x
  have hKJPoint :
      (cc20ThreeBranchCommutator (radialSupportProjection lambda)
        (sourceFourierSupportProjection lambda)
        (sourceProlateRemainder lambda) (detectorOperator owner))
          ((sourceInclusion lambda) (ContinuousLinearMap.adjoint
            (suffixEulerFrameTransition lambda p S) x)) =
        -(sourceSoninComplement lambda)
          (detectorOperator owner
            ((sourceInclusion lambda) (ContinuousLinearMap.adjoint
              (suffixEulerFrameTransition lambda p S) x))) := by
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.neg_apply] using congrArg
      (fun operator : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier =>
        operator (ContinuousLinearMap.adjoint
          (suffixEulerFrameTransition lambda p S) x)) hKJ
  have hKJEndpoint :
      (cc20ThreeBranchCommutator (radialSupportProjection lambda)
        (sourceFourierSupportProjection lambda)
        (sourceProlateRemainder lambda) (detectorOperator owner))
          ((sourceInclusion lambda) x) =
        -(sourceSoninComplement lambda)
          (detectorOperator owner ((sourceInclusion lambda) x)) := by
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.neg_apply] using congrArg
      (fun operator : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier =>
        operator x) hKJ
  have hJKForwardSPoint :
      ContinuousLinearMap.adjoint (sourceInclusion lambda)
          ((cc20ThreeBranchCommutator (radialSupportProjection lambda)
            (sourceFourierSupportProjection lambda)
            (sourceProlateRemainder lambda) (detectorOperator owner))
            (forwardS
            (ContinuousLinearMap.adjoint
              (suffixEulerFrameTransition lambda p S) x))) =
        ContinuousLinearMap.adjoint (sourceInclusion lambda)
          (detectorOperator owner (forwardS
            (ContinuousLinearMap.adjoint
              (suffixEulerFrameTransition lambda p S) x))) := by
    simpa only [ContinuousLinearMap.comp_apply] using congrArg
      (fun operator : sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda =>
        operator (ContinuousLinearMap.adjoint
          (suffixEulerFrameTransition lambda p S) x))
      (hJKforward forwardS hforwardS)
  have hJKForwardPSPoint :
      ContinuousLinearMap.adjoint (sourceInclusion lambda)
          ((cc20ThreeBranchCommutator (radialSupportProjection lambda)
            (sourceFourierSupportProjection lambda)
            (sourceProlateRemainder lambda) (detectorOperator owner))
            (forwardPS x)) =
        ContinuousLinearMap.adjoint (sourceInclusion lambda)
          (detectorOperator owner (forwardPS x)) := by
    simpa only [ContinuousLinearMap.comp_apply] using congrArg
      (fun operator : sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda =>
        operator x) (hJKforward forwardPS hforwardPS)
  simp only [rawPhysicalFourTermRowOfCoframes,
    rawCoframeBoundaryMoment, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.neg_apply]
  rw [hKJPoint, hJKForwardSPoint, hKJEndpoint, hJKForwardPSPoint]
  simp only [map_add, map_neg]
  abel

/-! ## Instantiation on the actual source coframes -/

theorem suffixActualBandRawPhysicalFourTermRow_eq_boundaryMoment_telescope
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandRawPhysicalFourTermRow owner lambda p S =
      rawCoframeBoundaryMoment owner lambda
          (suffixActualBandForwardCoframe lambda S)
          (suffixActualBandForwardEndpointCoframe lambda S) ∘L
          (suffixEulerFrameTransition lambda p S)† -
        (suffixEulerFrameTransition lambda p S)† ∘L
          rawCoframeBoundaryMoment owner lambda
            (suffixActualBandForwardCoframe lambda (p :: S))
            (suffixActualBandForwardEndpointCoframe lambda (p :: S)) := by
  rw [actualRawPhysicalFourTermRow_eq_ofCoframes]
  apply rawPhysicalFourTermRowOfCoframes_eq_boundaryMoment_telescope
  · apply ContinuousLinearMap.ext
    intro x
    have hzero := congrArg
      (fun operator : finiteSCarrier →L[ℂ] finiteSCarrier =>
        operator (normalizedFiniteEulerInverseList S
          (sourceInclusion lambda x)))
      (sourceSoninProjection_comp_sourceBandProjection_eq_zero lambda)
    simp only [suffixActualBandForwardCoframe,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply] at hzero ⊢
    simpa only [ContinuousLinearMap.comp_apply] using hzero
  · apply ContinuousLinearMap.ext
    intro x
    have hzero := congrArg
      (fun operator : finiteSCarrier →L[ℂ] finiteSCarrier =>
        operator (normalizedFiniteEulerInverseList (p :: S)
          (sourceInclusion lambda x)))
      (sourceSoninProjection_comp_sourceBandProjection_eq_zero lambda)
    simp only [suffixActualBandForwardCoframe,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply] at hzero ⊢
    simpa only [ContinuousLinearMap.comp_apply] using hzero

/-! ## The literal endpoint is biorthogonal -/

theorem sourceSoninProjection_comp_suffixActualBandMetricCoframe
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    sourceSoninProjection lambda ∘L
        suffixActualBandMetricCoframe lambda S =
      sourceInclusion lambda := by
  rw [← sourceInclusion_comp_adjoint]
  apply ContinuousLinearMap.ext
  intro u
  change sourceInclusion lambda
      (ContinuousLinearMap.adjoint (sourceInclusion lambda)
        (suffixActualBandAmbientGram S
          (sourceInclusion lambda
            (suffixActualBandGramInv lambda S u)))) =
    sourceInclusion lambda u
  have hgram := suffixActualBandGram_eq_compressedAmbientGram lambda S
  have hgramPoint := congrArg
    (fun operator : sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda =>
      operator (suffixActualBandGramInv lambda S u)) hgram
  have hprod := parameterizedSoninGram_mul_gramInv
    lambda 1 S (by norm_num)
  have hprodPoint := congrArg
    (fun operator : sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda =>
      operator u) hprod
  simp only [ContinuousLinearMap.comp_apply] at hgramPoint hprodPoint
  rw [← hgramPoint]
  simpa only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.one_apply] using congrArg
      (sourceInclusion lambda) hprodPoint

theorem sourceSoninProjection_comp_suffixActualBandForwardCoframe_eq_zero
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    sourceSoninProjection lambda ∘L
        suffixActualBandForwardCoframe lambda S = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  have hzero := congrArg
    (fun operator : finiteSCarrier →L[ℂ] finiteSCarrier =>
      operator (normalizedFiniteEulerInverseList S
        (sourceInclusion lambda x)))
    (sourceSoninProjection_comp_sourceBandProjection_eq_zero lambda)
  simp only [suffixActualBandForwardCoframe,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply] at hzero ⊢
  simpa only [ContinuousLinearMap.comp_apply] using hzero

theorem sourceSoninProjection_comp_suffixActualBandForwardEndpointCoframe
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    sourceSoninProjection lambda ∘L
      suffixActualBandForwardEndpointCoframe lambda S =
      sourceInclusion lambda := by
  apply ContinuousLinearMap.ext
  intro x
  have hforward := congrArg
    (fun operator : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier =>
      operator x)
    (sourceSoninProjection_comp_suffixActualBandForwardCoframe_eq_zero
      lambda S)
  have hmetric := congrArg
    (fun operator : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier =>
      operator x)
    (sourceSoninProjection_comp_suffixActualBandMetricCoframe lambda S)
  simp only [suffixActualBandForwardEndpointCoframe,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply] at hforward hmetric ⊢
  rw [map_add, hforward, hmetric]
  simp

theorem rawCoframeBoundaryMoment_eq_leakage_of_endpoint_compression
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    (forward endpoint : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier)
    (hendpoint : sourceSoninProjection lambda ∘L endpoint =
      sourceInclusion lambda) :
    rawCoframeBoundaryMoment owner lambda forward endpoint =
      (endpoint - sourceInclusion lambda)† ∘L detectorOperator owner ∘L
          sourceInclusion lambda +
        (sourceInclusion lambda)† ∘L detectorOperator owner ∘L forward := by
  have hEndpointAdj :
      endpoint† ∘L sourceSoninProjection lambda =
        (sourceInclusion lambda)† := by
    have h := congrArg ContinuousLinearMap.adjoint hendpoint
    simpa only [ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint,
      (sourceSoninProjection_isStarProjection lambda).isSelfAdjoint.adjoint_eq]
      using h
  have hLeft :
      endpoint† ∘L sourceSoninComplement lambda =
        endpoint† - (sourceInclusion lambda)† := by
    rw [sourceSoninComplement]
    apply ContinuousLinearMap.ext
    intro x
    have h := congrArg
      (fun operator : finiteSCarrier →L[ℂ] sourceSoninCarrier lambda =>
        operator x) hEndpointAdj
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
      map_sub] at h ⊢
    rw [h]
  have hAdjSub (A B : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier) :
      (A - B)† = A† - B† := by
    apply ContinuousLinearMap.ext
    intro y
    apply ext_inner_right ℂ
    intro z
    simp only [ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearMap.sub_apply, inner_sub_left, inner_sub_right]
  apply ContinuousLinearMap.ext
  intro x
  have hleftPoint := congrArg
    (fun operator : finiteSCarrier →L[ℂ] sourceSoninCarrier lambda =>
      operator (detectorOperator owner (sourceInclusion lambda x))) hLeft
  have hadjPoint := congrArg
    (fun operator : finiteSCarrier →L[ℂ] sourceSoninCarrier lambda =>
      operator (detectorOperator owner (sourceInclusion lambda x)))
    (hAdjSub endpoint (sourceInclusion lambda))
  simp only [rawCoframeBoundaryMoment, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply] at hleftPoint hadjPoint ⊢
  rw [hleftPoint, ← hadjPoint]

theorem suffixActualBandRawCoframeBoundaryMoment_eq_leakage
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    rawCoframeBoundaryMoment owner lambda
        (suffixActualBandForwardCoframe lambda S)
        (suffixActualBandForwardEndpointCoframe lambda S) =
      (suffixActualBandForwardEndpointCoframe lambda S -
          sourceInclusion lambda)† ∘L detectorOperator owner ∘L
          sourceInclusion lambda +
        (sourceInclusion lambda)† ∘L detectorOperator owner ∘L
          suffixActualBandForwardCoframe lambda S := by
  exact rawCoframeBoundaryMoment_eq_leakage_of_endpoint_compression
    owner lambda (suffixActualBandForwardCoframe lambda S)
      (suffixActualBandForwardEndpointCoframe lambda S)
      (sourceSoninProjection_comp_suffixActualBandForwardEndpointCoframe
        lambda S)

/-! ## Readback to the completed raw response -/

/-- The boundary moment is the adjoint of the complete raw quadratic response.
This is the same signed object already owned by the local trace factorization;
no residual-only factorization is inferred. -/
theorem suffixActualBandRawCoframeBoundaryMoment_eq_rawResponse_adjoint
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    rawCoframeBoundaryMoment owner lambda
        (suffixActualBandForwardCoframe lambda S)
        (suffixActualBandForwardEndpointCoframe lambda S) =
      (suffixActualBandRawQuadraticCycledResponse owner lambda S)† := by
  rw [suffixActualBandRawQuadraticCycledResponse_adjoint_eq_physical]
  have hforward :=
    sourceSoninProjection_comp_suffixActualBandForwardCoframe_eq_zero
      lambda S
  have hKJ := threeBranch_comp_sourceInclusion_eq_neg_complement_detector_inclusion
    owner lambda
  have hJKF := sourceInclusionAdjoint_comp_threeBranch_comp_forward_eq
    owner lambda (suffixActualBandForwardCoframe lambda S) hforward
  apply ContinuousLinearMap.ext
  intro x
  have hKJPoint := congrArg
    (fun operator : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier => operator x)
    hKJ
  have hJKFPoint := congrArg
    (fun operator : sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda =>
      operator x) hJKF
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply]
    at hKJPoint hJKFPoint
  simp only [rawCoframeBoundaryMoment, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.neg_apply] at ⊢
  rw [hKJPoint, hJKFPoint]
  simp

theorem suffixActualBandRawCoframeBoundaryMoment_eq_remainderResponse_adjoint
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    rawCoframeBoundaryMoment owner lambda
        (suffixActualBandForwardCoframe lambda family.visiblePrimes)
        (suffixActualBandForwardEndpointCoframe lambda family.visiblePrimes) =
      (sourceActualBandFiniteEulerRemainderResponse owner lambda family)† := by
  rw [suffixActualBandRawCoframeBoundaryMoment_eq_rawResponse_adjoint,
    suffixActualBandRawQuadraticCycledResponse_eq_actual]

theorem rawCoframeBoundaryMoment_isTraceClassAlong_of_rawResponse
    {ι : Type*} (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime)
    (basis : HilbertBasis ι ℂ (sourceSoninCarrier lambda))
    (hresponse : CC20Concrete.PositiveTrace.IsTraceClassAlong basis
      (suffixActualBandRawQuadraticCycledResponse owner lambda S)) :
    CC20Concrete.PositiveTrace.IsTraceClassAlong basis
      (rawCoframeBoundaryMoment owner lambda
        (suffixActualBandForwardCoframe lambda S)
        (suffixActualBandForwardEndpointCoframe lambda S)) := by
  rw [suffixActualBandRawCoframeBoundaryMoment_eq_rawResponse_adjoint]
  exact CC20Concrete.PositiveTrace.isTraceClassAlong_adjoint basis _ hresponse

theorem rawCoframeBoundaryMoment_ordinaryTraceAlong_eq_star_rawResponse
    {ι : Type*} (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime)
    (basis : HilbertBasis ι ℂ (sourceSoninCarrier lambda)) :
    CC20Concrete.PositiveTrace.ordinaryTraceAlong basis
      (rawCoframeBoundaryMoment owner lambda
        (suffixActualBandForwardCoframe lambda S)
        (suffixActualBandForwardEndpointCoframe lambda S)) =
      star (CC20Concrete.PositiveTrace.ordinaryTraceAlong basis
        (suffixActualBandRawQuadraticCycledResponse owner lambda S)) := by
  rw [suffixActualBandRawCoframeBoundaryMoment_eq_rawResponse_adjoint]
  exact CC20Concrete.PositiveTrace.ordinaryTraceAlong_adjoint basis _

/- The complete four-term raw row is the adjacent telescope of the already
owned raw quadratic responses, with the coframe boundary cancellation kept
inside each response. -/
set_option maxHeartbeats 4000000 in
-- The nested response readback needs a larger elaboration budget.
set_option maxRecDepth 10000 in
theorem suffixActualBandRawPhysicalFourTermRow_eq_rawResponse_adjoint_telescope
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandRawPhysicalFourTermRow owner lambda p S =
      (suffixActualBandRawQuadraticCycledResponse owner lambda S)† ∘L
          (suffixEulerFrameTransition lambda p S)† -
        (suffixEulerFrameTransition lambda p S)† ∘L
          (suffixActualBandRawQuadraticCycledResponse owner lambda (p :: S))† := by
  rw [suffixActualBandRawPhysicalFourTermRow_eq_boundaryMoment_telescope,
    suffixActualBandRawCoframeBoundaryMoment_eq_rawResponse_adjoint,
    suffixActualBandRawCoframeBoundaryMoment_eq_rawResponse_adjoint]

theorem suffixActualBandForwardCoframe_nil_eq_zero
    (lambda : CCM24SoninScale) :
    suffixActualBandForwardCoframe lambda [] = 0 := by
  have hInverse :
      normalizedFiniteEulerInverseList [] =
        ContinuousLinearMap.id ℂ finiteSCarrier := by
    have h := finiteEulerCausalAverage_eq_normalizedInverse []
    simpa only [finiteEulerCausalAverage] using h.symm
  apply ContinuousLinearMap.ext
  intro x
  have hzero := congrArg
    (fun operator : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier =>
      operator x)
    (sourceBandProjection_comp_sourceInclusion_eq_zero lambda)
  simp only [suffixActualBandForwardCoframe,
    ContinuousLinearMap.comp_apply, hInverse,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.zero_apply] at hzero ⊢
  exact hzero

theorem suffixActualBandMetricCoframe_nil_eq_sourceInclusion
    (lambda : CCM24SoninScale) :
    suffixActualBandMetricCoframe lambda [] = sourceInclusion lambda := by
  rw [suffixActualBandMetricCoframe, suffixActualBandAmbientGram,
    suffixActualBandTransportOperator, ccm24FiniteEulerTransportEquiv_nil,
    suffixActualBandGramInv, parameterizedSoninGramInv_one_nil_eq_id]
  apply ContinuousLinearMap.ext
  intro x
  simp

theorem suffixActualBandForwardEndpointCoframe_nil_eq_sourceInclusion
    (lambda : CCM24SoninScale) :
    suffixActualBandForwardEndpointCoframe lambda [] =
      sourceInclusion lambda := by
  rw [suffixActualBandForwardEndpointCoframe,
    suffixActualBandForwardCoframe_nil_eq_zero,
    suffixActualBandMetricCoframe_nil_eq_sourceInclusion]
  simp

theorem rawCoframeBoundaryMoment_nil_eq_zero
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    rawCoframeBoundaryMoment owner lambda
        (suffixActualBandForwardCoframe lambda [])
        (suffixActualBandForwardEndpointCoframe lambda []) = 0 := by
  have hJComplement :
      (sourceInclusion lambda)† ∘L sourceSoninComplement lambda = 0 := by
    rw [sourceSoninComplement]
    apply ContinuousLinearMap.ext
    intro x
    have h := congrArg
      (fun operator : finiteSCarrier →L[ℂ] sourceSoninCarrier lambda =>
        operator x)
      (sourceInclusionAdjoint_comp_sourceProjection lambda)
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
      map_sub] at h ⊢
    rw [h]
    simp
  rw [rawCoframeBoundaryMoment,
    suffixActualBandForwardCoframe_nil_eq_zero,
    suffixActualBandForwardEndpointCoframe_nil_eq_sourceInclusion]
  apply ContinuousLinearMap.ext
  intro x
  have h := congrArg
    (fun operator : finiteSCarrier →L[ℂ] sourceSoninCarrier lambda =>
      operator (detectorOperator owner (sourceInclusion lambda x)))
    hJComplement
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.zero_apply] at h ⊢
  rw [h]
  simp

theorem suffixActualBandRawPhysicalFourTermRow_cons_nil_eq_neg_boundaryMoment
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) :
    suffixActualBandRawPhysicalFourTermRow owner lambda p [] =
      -(ContinuousLinearMap.adjoint (suffixEulerFrameTransition lambda p [])) ∘L
        rawCoframeBoundaryMoment owner lambda
          (suffixActualBandForwardCoframe lambda [p])
          (suffixActualBandForwardEndpointCoframe lambda [p]) := by
  rw [suffixActualBandRawPhysicalFourTermRow_eq_boundaryMoment_telescope,
    rawCoframeBoundaryMoment_nil_eq_zero]
  simp only [ContinuousLinearMap.zero_comp, zero_sub]

end CCM24FiniteSCompletedJuliaRawCoframeBoundaryTelescope
end CCM25Concrete
end Source
end ConnesWeilRH
