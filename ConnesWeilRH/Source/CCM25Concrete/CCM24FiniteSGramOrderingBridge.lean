/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCommonBoundaryPair
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSIsometricTargetCrossing

/-!
# Left/right Gram-order bridge for the finite-S response

The route response stores the inverse Gram covariance on the right.  The
weighted-boundary resolvent of Proofs 427--428 places it on the left.  These
operators need not be equal in infinite dimension.  For the actual
self-adjoint detector and Gram inverse, however, the left-ordered operator is
exactly the Hilbert-space adjoint of the right-ordered operator.

Consequently their ordinary diagonal traces are complex conjugates and have
the same norm.  This is enough to transport a Gate 3U absolute trace bound; no
trace cycle and no real-trace premise is used.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSGramOrderingBridge

open CC20Concrete
open CCM24FiniteSProjectionTrace
open CCM24FiniteSGramResponse
open CCM24FiniteSBandTrace
open CCM24FiniteSCausalSupport
open CCM24FiniteSInverseMetric
open scoped InnerProduct

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

private theorem left_comp_sub_eq_adjoint_right_comp_sub
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    (gram compression base : H →L[ℂ] H)
    (hgram : IsSelfAdjoint gram)
    (hcompression : IsSelfAdjoint compression)
    (hbase : IsSelfAdjoint base) :
    gram ∘L compression - base = (compression ∘L gram - base)† := by
  have hadjointSub :
      (compression ∘L gram - base)† =
        (compression ∘L gram)† - base† := by
    apply ContinuousLinearMap.ext
    intro u
    exact ext_inner_right ℂ fun v => by
      simp only [ContinuousLinearMap.adjoint_inner_left,
        ContinuousLinearMap.sub_apply, inner_sub_left, inner_sub_right]
  rw [hadjointSub, ContinuousLinearMap.adjoint_comp,
    hgram.adjoint_eq, hcompression.adjoint_eq, hbase.adjoint_eq]

private theorem adjoint_neg_eq_neg_adjoint
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (operator : H →L[ℂ] H) :
    (-operator)† = -(operator†) := by
  apply ContinuousLinearMap.ext
  intro u
  exact ext_inner_right ℂ fun v => by
    simp only [ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearMap.neg_apply, inner_neg_left, inner_neg_right]

/-- Rectangular version of Proof 428's target-crossing collapse.  The source
frame and ambient transport live on different Hilbert carriers, so this
statement cannot be obtained by putting every factor in one endomorphism
ring. -/
theorem rectangular_isometric_targetCommutator_collapse
    {HSource HAmbient : Type*}
    [NormedAddCommGroup HSource] [InnerProductSpace ℂ HSource]
    [CompleteSpace HSource]
    [NormedAddCommGroup HAmbient] [InnerProductSpace ℂ HAmbient]
    [CompleteSpace HAmbient]
    (frame : HSource →L[ℂ] HAmbient)
    (transport transportInverse detector targetProjection :
      HAmbient →L[ℂ] HAmbient)
    (gramInverse : HSource →L[ℂ] HSource)
    (hFrameIsometry : frame† ∘L frame =
      ContinuousLinearMap.id ℂ HSource)
    (hInverseLeft : transportInverse ∘L transport =
      ContinuousLinearMap.id ℂ HAmbient)
    (hProjectionFormula : targetProjection =
      transport ∘L frame ∘L gramInverse ∘L frame† ∘L transport†)
    (hProjectionSq : targetProjection ∘L targetProjection = targetProjection)
    (hProjectionRange : targetProjection ∘L transport ∘L frame =
      transport ∘L frame)
    (hDetectorCommutes : transport ∘L detector = detector ∘L transport) :
    gramInverse ∘L
          ((transport ∘L frame)† ∘L detector ∘L
            (transport ∘L frame)) -
        frame† ∘L detector ∘L frame =
      -(frame† ∘L transportInverse ∘L
        (ContinuousLinearMap.id ℂ HAmbient - targetProjection) ∘L
        (detector ∘L targetProjection - targetProjection ∘L detector) ∘L
        transport ∘L frame) := by
  have hFrameIsometryApply (u : HSource) : (frame†) (frame u) = u := by
    have h := congrArg
      (fun operator : HSource →L[ℂ] HSource => operator u) hFrameIsometry
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] using h
  have hInverseLeftApply (u : HAmbient) :
      transportInverse (transport u) = u := by
    have h := congrArg
      (fun operator : HAmbient →L[ℂ] HAmbient => operator u) hInverseLeft
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] using h
  have hProjectionFormulaApply (u : HAmbient) :
      targetProjection u =
        transport (frame (gramInverse ((frame†) ((transport†) u)))) := by
    have h := congrArg
      (fun operator : HAmbient →L[ℂ] HAmbient => operator u)
      hProjectionFormula
    simpa only [ContinuousLinearMap.comp_apply] using h
  have hProjectionSqApply (u : HAmbient) :
      targetProjection (targetProjection u) = targetProjection u := by
    have h := congrArg
      (fun operator : HAmbient →L[ℂ] HAmbient => operator u) hProjectionSq
    simpa only [ContinuousLinearMap.comp_apply] using h
  have hProjectionRangeApply (u : HSource) :
      targetProjection (transport (frame u)) = transport (frame u) := by
    have h := congrArg
      (fun operator : HSource →L[ℂ] HAmbient => operator u) hProjectionRange
    simpa only [ContinuousLinearMap.comp_apply] using h
  have hDetectorCommutesApply (u : HAmbient) :
      transport (detector u) = detector (transport u) := by
    have h := congrArg
      (fun operator : HAmbient →L[ℂ] HAmbient => operator u)
      hDetectorCommutes
    simpa only [ContinuousLinearMap.comp_apply] using h
  have hProjectionTransport (u : HAmbient) :
      (frame†) (transportInverse (targetProjection (transport u))) =
        gramInverse ((frame†) ((transport†) (transport u))) := by
    rw [hProjectionFormulaApply, hInverseLeftApply, hFrameIsometryApply]
  have hRetraction :
      gramInverse ∘L frame† ∘L transport† ∘L transport - frame† =
        -(frame† ∘L transportInverse ∘L
          (ContinuousLinearMap.id ℂ HAmbient - targetProjection) ∘L
          transport) := by
    apply ContinuousLinearMap.ext
    intro u
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.neg_apply,
      ContinuousLinearMap.id_apply, map_sub]
    rw [hInverseLeftApply, hProjectionTransport]
    abel
  have hLeftReadback :
      gramInverse ∘L
            ((transport ∘L frame)† ∘L detector ∘L
              (transport ∘L frame)) -
          frame† ∘L detector ∘L frame =
        (gramInverse ∘L frame† ∘L transport† ∘L transport - frame†) ∘L
          detector ∘L frame := by
    apply ContinuousLinearMap.ext
    intro u
    simp only [ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply]
    rw [hDetectorCommutesApply]
  have hComplementProjection (u : HAmbient) :
      (ContinuousLinearMap.id ℂ HAmbient - targetProjection)
          (targetProjection u) = 0 := by
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]
    rw [hProjectionSqApply]
    exact sub_self _
  have hCrossing :
      (ContinuousLinearMap.id ℂ HAmbient - targetProjection) ∘L detector ∘L
          transport ∘L frame =
        (ContinuousLinearMap.id ℂ HAmbient - targetProjection) ∘L
          (detector ∘L targetProjection - targetProjection ∘L detector) ∘L
          transport ∘L frame := by
    apply ContinuousLinearMap.ext
    intro u
    change
      (ContinuousLinearMap.id ℂ HAmbient - targetProjection)
          (detector (transport (frame u))) =
        (ContinuousLinearMap.id ℂ HAmbient - targetProjection)
          (detector (targetProjection (transport (frame u))) -
            targetProjection (detector (transport (frame u))))
    rw [hProjectionRangeApply, map_sub, hComplementProjection, sub_zero]
  rw [hLeftReadback, hRetraction]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply]
  rw [hDetectorCommutesApply]
  have h := congrArg
    (fun operator : HSource →L[ℂ] HAmbient => operator u) hCrossing
  simpa only [ContinuousLinearMap.comp_apply] using congrArg
    (fun x : HAmbient => -((frame†) (transportInverse x))) h

/-- The left-normalized source Gram response
`G_S^-1 K_S^dagger W K_S-W_0`. -/
noncomputable def leftOrderedSourceGramResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
  finiteEulerGramInv lambda family ∘L
      ((finiteEulerFrame lambda family)† ∘L detectorOperator owner ∘L
        finiteEulerFrame lambda family) -
    (sourceInclusion lambda)† ∘L detectorOperator owner ∘L
      sourceInclusion lambda

/-- Route-band orientation of the same left-normalized response. -/
noncomputable def leftOrderedSourceBandGramResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
  -leftOrderedSourceGramResponse owner lambda family

/-- The actual finite-S target detector commutator `W P_S-P_S W`. -/
noncomputable def finiteEulerTargetDetectorCommutator
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  detectorOperator owner ∘L targetSoninProjection lambda family -
    targetSoninProjection lambda family ∘L detectorOperator owner

/-- Actual-carrier target-crossing owner of Proof 428.  The source inclusion
is rectangular; every composition below therefore has its genuine Hilbert
carrier rather than an artificial common ring. -/
noncomputable def finiteEulerTargetCommutatorResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
  -((sourceInclusion lambda)† ∘L finiteEulerInverseOperator family ∘L
    (ContinuousLinearMap.id ℂ finiteSCarrier -
      targetSoninProjection lambda family) ∘L
    finiteEulerTargetDetectorCommutator owner lambda family ∘L
    finiteEulerTransportOperator family ∘L sourceInclusion lambda)

/-- The canonical finite-S Sonin projection is the literal transported-frame
Gram projection used by the rectangular collapse. -/
theorem targetSoninProjection_eq_transport_frame_gramProjection
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    targetSoninProjection lambda family =
      finiteEulerTransportOperator family ∘L sourceInclusion lambda ∘L
        finiteEulerGramInv lambda family ∘L (sourceInclusion lambda)† ∘L
        (finiteEulerTransportOperator family)† := by
  rw [targetSoninProjection_eq_dualFrame_comp_frameAdjoint,
    finiteEulerDualFrame, finiteEulerFrame_eq_transport_comp_inclusion,
    finiteEulerTransportOperator, ContinuousLinearMap.adjoint_comp]
  apply ContinuousLinearMap.ext
  intro u
  rfl

/-- The actual target projection fixes the transported source Sonin frame. -/
theorem targetSoninProjection_comp_transport_frame
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    targetSoninProjection lambda family ∘L
        finiteEulerTransportOperator family ∘L sourceInclusion lambda =
      finiteEulerTransportOperator family ∘L sourceInclusion lambda := by
  rw [finiteEulerTransportOperator]
  rw [← finiteEulerFrame_eq_transport_comp_inclusion]
  rw [targetSoninProjection_eq_dualFrame_comp_frameAdjoint,
    finiteEulerDualFrame]
  apply ContinuousLinearMap.ext
  intro u
  change finiteEulerFrame lambda family
      (finiteEulerGramInv lambda family (finiteEulerGram lambda family u)) =
    finiteEulerFrame lambda family u
  have hu := congrArg
    (fun operator : sourceSoninCarrier lambda →L[ℂ]
      sourceSoninCarrier lambda => operator u)
    (finiteEulerGramInv_comp_gram lambda family)
  simpa only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply] using congrArg
      (finiteEulerFrame lambda family) hu

/-- Proof 428 on the literal source/ambient carriers.  This identifies the
left Gram order with one target projection commutator and uses no trace cycle. -/
theorem leftOrderedSourceGramResponse_eq_targetCommutator
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    leftOrderedSourceGramResponse owner lambda family =
      finiteEulerTargetCommutatorResponse owner lambda family := by
  have hProjectionSq :
      targetSoninProjection lambda family ∘L
          targetSoninProjection lambda family =
        targetSoninProjection lambda family := by
    simpa only [ContinuousLinearMap.mul_def] using
      (targetSoninProjection_isStarProjection lambda family).isIdempotentElem
  have hCollapse := rectangular_isometric_targetCommutator_collapse
    (sourceInclusion lambda)
    (finiteEulerTransportOperator family)
    (finiteEulerInverseOperator family)
    (detectorOperator owner)
    (targetSoninProjection lambda family)
    (finiteEulerGramInv lambda family)
    (sourceInclusion_adjoint_comp_self lambda)
    (inverse_comp_transport family)
    (targetSoninProjection_eq_transport_frame_gramProjection lambda family)
    hProjectionSq
    (targetSoninProjection_comp_transport_frame lambda family)
    (by
      exact (detectorOperator_comp_finiteEulerTransport owner
        family.visiblePrimes).symm)
  simpa only [leftOrderedSourceGramResponse,
    finiteEulerTargetCommutatorResponse,
    finiteEulerTargetDetectorCommutator,
    finiteEulerFrame_eq_transport_comp_inclusion,
    finiteEulerTransportOperator] using hCollapse

theorem frameDetectorCompression_adjoint_eq
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    ((finiteEulerFrame lambda family)† ∘L detectorOperator owner ∘L
        finiteEulerFrame lambda family)† =
      (finiteEulerFrame lambda family)† ∘L detectorOperator owner ∘L
        finiteEulerFrame lambda family := by
  rw [ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint,
    (detectorOperator_isSelfAdjoint owner).adjoint_eq]
  apply ContinuousLinearMap.ext
  intro u
  rfl

theorem sourceDetectorCompression_adjoint_eq
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    ((sourceInclusion lambda)† ∘L detectorOperator owner ∘L
        sourceInclusion lambda)† =
      (sourceInclusion lambda)† ∘L detectorOperator owner ∘L
        sourceInclusion lambda := by
  rw [ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint,
    (detectorOperator_isSelfAdjoint owner).adjoint_eq]
  apply ContinuousLinearMap.ext
  intro u
  rfl

/-- The two Gram orders are adjoints, not equal operators. -/
theorem leftOrderedSourceGramResponse_eq_adjoint
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    leftOrderedSourceGramResponse owner lambda family =
      (sourceGramResponse owner lambda family)† := by
  rw [leftOrderedSourceGramResponse, sourceGramResponse]
  exact left_comp_sub_eq_adjoint_right_comp_sub
    (finiteEulerGramInv lambda family)
    ((finiteEulerFrame lambda family)† ∘L detectorOperator owner ∘L
      finiteEulerFrame lambda family)
    ((sourceInclusion lambda)† ∘L detectorOperator owner ∘L
      sourceInclusion lambda)
    (finiteEulerGramInv_isSelfAdjoint lambda family)
    (frameDetectorCompression_adjoint_eq owner lambda family)
    (sourceDetectorCompression_adjoint_eq owner lambda)

/-- The route-band orientations inherit the same adjoint relation. -/
theorem leftOrderedSourceBandGramResponse_eq_adjoint
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    leftOrderedSourceBandGramResponse owner lambda family =
      (sourceBandGramResponse owner lambda family)† := by
  rw [leftOrderedSourceBandGramResponse, sourceBandGramResponse,
    leftOrderedSourceGramResponse_eq_adjoint]
  exact (adjoint_neg_eq_neg_adjoint
    (sourceGramResponse owner lambda family)).symm

/-- Adjoint passage conjugates the actual source trace; no trace-class premise
is needed for this diagonal-series identity. -/
theorem ordinaryTraceAlong_leftOrderedSourceBandGramResponse_eq_star
    {ι : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (basis : HilbertBasis ι ℂ (sourceSoninCarrier lambda)) :
    CC20Concrete.PositiveTrace.ordinaryTraceAlong basis
        (leftOrderedSourceBandGramResponse owner lambda family) =
      star (CC20Concrete.PositiveTrace.ordinaryTraceAlong basis
        (sourceBandGramResponse owner lambda family)) := by
  rw [leftOrderedSourceBandGramResponse_eq_adjoint,
    CC20Concrete.PositiveTrace.ordinaryTraceAlong_adjoint]

/-- Gate 3U uses the absolute trace size, which is invariant under the Gram
order reversal. -/
theorem norm_ordinaryTraceAlong_leftOrderedSourceBandGramResponse_eq
    {ι : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (basis : HilbertBasis ι ℂ (sourceSoninCarrier lambda)) :
    ‖CC20Concrete.PositiveTrace.ordinaryTraceAlong basis
        (leftOrderedSourceBandGramResponse owner lambda family)‖ =
      ‖CC20Concrete.PositiveTrace.ordinaryTraceAlong basis
        (sourceBandGramResponse owner lambda family)‖ := by
  rw [ordinaryTraceAlong_leftOrderedSourceBandGramResponse_eq_star,
    Complex.star_def, Complex.norm_conj]

/-- Fixed-S trace legality transfers to the left order by taking the adjoint. -/
theorem leftOrderedSourceBandGramResponse_isTraceClassAlong
    {ι : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (basis : HilbertBasis ι ℂ (sourceSoninCarrier lambda))
    (hresponse : CC20Concrete.PositiveTrace.IsTraceClassAlong basis
      (sourceBandGramResponse owner lambda family)) :
    CC20Concrete.PositiveTrace.IsTraceClassAlong basis
      (leftOrderedSourceBandGramResponse owner lambda family) := by
  rw [leftOrderedSourceBandGramResponse_eq_adjoint]
  exact CC20Concrete.PositiveTrace.isTraceClassAlong_adjoint basis _ hresponse

/-- The route-band sign converts the left Gram order into the negative of the
actual target-commutator response. -/
theorem leftOrderedSourceBandGramResponse_eq_neg_targetCommutator
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    leftOrderedSourceBandGramResponse owner lambda family =
      -finiteEulerTargetCommutatorResponse owner lambda family := by
  rw [leftOrderedSourceBandGramResponse,
    leftOrderedSourceGramResponse_eq_targetCommutator]

/-- A Gate 3U absolute trace bound for the actual target commutator is
exactly a bound for the route's right-ordered source response. -/
theorem norm_ordinaryTraceAlong_finiteEulerTargetCommutatorResponse_eq
    {ι : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (basis : HilbertBasis ι ℂ (sourceSoninCarrier lambda)) :
    ‖CC20Concrete.PositiveTrace.ordinaryTraceAlong basis
        (finiteEulerTargetCommutatorResponse owner lambda family)‖ =
      ‖CC20Concrete.PositiveTrace.ordinaryTraceAlong basis
        (sourceBandGramResponse owner lambda family)‖ := by
  have hTrace := congrArg
    (CC20Concrete.PositiveTrace.ordinaryTraceAlong basis)
    (leftOrderedSourceBandGramResponse_eq_neg_targetCommutator
      owner lambda family)
  rw [CCM24FiniteSProjectionTrace.PositiveTrace.ordinaryTraceAlong_neg]
    at hTrace
  calc
    ‖CC20Concrete.PositiveTrace.ordinaryTraceAlong basis
        (finiteEulerTargetCommutatorResponse owner lambda family)‖ =
      ‖-CC20Concrete.PositiveTrace.ordinaryTraceAlong basis
        (finiteEulerTargetCommutatorResponse owner lambda family)‖ :=
          (norm_neg _).symm
    _ = ‖CC20Concrete.PositiveTrace.ordinaryTraceAlong basis
        (leftOrderedSourceBandGramResponse owner lambda family)‖ :=
          (congrArg norm hTrace).symm
    _ = ‖CC20Concrete.PositiveTrace.ordinaryTraceAlong basis
        (sourceBandGramResponse owner lambda family)‖ :=
          norm_ordinaryTraceAlong_leftOrderedSourceBandGramResponse_eq
            owner lambda family basis

/-- Fixed-S trace legality for the route response also gives trace legality
for the literal target-commutator owner. -/
theorem finiteEulerTargetCommutatorResponse_isTraceClassAlong
    {ι : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (basis : HilbertBasis ι ℂ (sourceSoninCarrier lambda))
    (hresponse : CC20Concrete.PositiveTrace.IsTraceClassAlong basis
      (sourceBandGramResponse owner lambda family)) :
    CC20Concrete.PositiveTrace.IsTraceClassAlong basis
      (finiteEulerTargetCommutatorResponse owner lambda family) := by
  have hleft := leftOrderedSourceBandGramResponse_isTraceClassAlong
    owner lambda family basis hresponse
  have hneg :=
    CCM24FiniteSProjectionTrace.PositiveTrace.isTraceClassAlong_neg basis
      (leftOrderedSourceBandGramResponse owner lambda family) hleft
  rw [leftOrderedSourceBandGramResponse_eq_neg_targetCommutator] at hneg
  simpa only [neg_neg] using hneg

end CCM24FiniteSGramOrderingBridge
end CCM25Concrete
end Source
end ConnesWeilRH
