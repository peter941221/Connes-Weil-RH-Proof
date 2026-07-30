/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSActualSchurTransitionSkewTrace

/-!
# Physical owner for the transition-skew boundary moment

The transition-skew row from Proof 570 is built from the Schur boundary moment.
This file identifies the adjoint of that moment with the same signed physical
three-branch commutator used by the existing Hilbert--Schmidt owners.

The identity is conditional only on the forward coframe being in the Sonin
complement.  It holds for an arbitrary endpoint coframe.  It is an exact
signed bridge; it is not a norm estimate, a cancellation, or a Gate 3U proof.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSActualSchurSkewPhysicalOwner

open scoped InnerProduct

open CC20Concrete
open CCM24FiniteSCompletedJuliaRawCoframeBoundaryTelescope
open CCM24FiniteSCompletedJuliaPolarRawReadout
open CCM24FiniteSGramResponse
open CCM24FiniteSProjectionTrace
open CCM24FiniteSActualSchurForwardPhysicalDifference
open CCM24FiniteSActualSchurRowBoundaryMoment
open CCM24FiniteSCompletedJuliaRawPhysicalResidualLedger
open CCM24FiniteSActualJuliaInput
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSActualSchurTransitionOrientation

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

local notation "SourceOp" lambda =>
  sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda

/-! ## The signed source identity -/

set_option maxHeartbeats 4000000 in
-- The explicit rectangular-adjoint normalization below crosses several
-- nested subtype carriers and needs a larger deterministic heartbeat budget.
theorem rawCoframeBoundaryMoment_adjoint_eq_threeBranchDifference
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    (forward endpoint : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier)
    (hforward : sourceSoninProjection lambda ∘L forward = 0) :
    (rawCoframeBoundaryMoment owner lambda forward endpoint)† =
      (sourceInclusion lambda)† ∘L
          cc20ThreeBranchCommutator (radialSupportProjection lambda)
            (sourceFourierSupportProjection lambda)
            (sourceProlateRemainder lambda) (detectorOperator owner) ∘L endpoint -
        forward† ∘L
          cc20ThreeBranchCommutator (radialSupportProjection lambda)
            (sourceFourierSupportProjection lambda)
            (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
          sourceInclusion lambda := by
  let branch := cc20ThreeBranchCommutator (radialSupportProjection lambda)
    (sourceFourierSupportProjection lambda)
    (sourceProlateRemainder lambda) (detectorOperator owner)
  have hbranchAdj : branch† = -branch := by
    exact suffixActualBandThreeBranchCommutator_adjoint_eq_neg owner lambda
  have hbranchInclusion :
      branch ∘L sourceInclusion lambda =
        -(sourceSoninComplement lambda ∘L detectorOperator owner ∘L
          sourceInclusion lambda) := by
    simpa only [branch] using
      (threeBranch_comp_sourceInclusion_eq_neg_complement_detector_inclusion
        owner lambda)
  have hprojectionAdj :
      (sourceSoninProjection lambda)† = sourceSoninProjection lambda :=
    (sourceSoninProjection_isStarProjection lambda).isSelfAdjoint.adjoint_eq
  have hdetectorAdj :
      (detectorOperator owner)† = detectorOperator owner :=
    detectorOperator_isSelfAdjoint owner
  have hadjointSubAmbient
      (A B : finiteSCarrier →L[ℂ] finiteSCarrier) :
      (A - B)† = A† - B† := by
    apply ContinuousLinearMap.ext
    intro y
    exact ext_inner_right ℂ fun z => by
      simp only [ContinuousLinearMap.adjoint_inner_left,
        ContinuousLinearMap.sub_apply, inner_sub_left, inner_sub_right]
  have hcomplementAdj :
      (sourceSoninComplement lambda)† = sourceSoninComplement lambda := by
    unfold sourceSoninComplement
    rw [hadjointSubAmbient, ContinuousLinearMap.adjoint_id, hprojectionAdj]
  have hadjoint_neg (operator : finiteSCarrier →L[ℂ] finiteSCarrier) :
      (-operator)† = -(operator†) := by
    apply ContinuousLinearMap.ext
    intro y
    exact ext_inner_right ℂ fun z => by
      simp only [ContinuousLinearMap.adjoint_inner_left,
        ContinuousLinearMap.neg_apply, inner_neg_left, inner_neg_right]
  have hadjoint_neg_source
      (operator : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier) :
      (-operator)† = -(operator†) := by
    apply ContinuousLinearMap.ext
    intro y
    exact ext_inner_right ℂ fun z => by
      simp only [ContinuousLinearMap.adjoint_inner_left,
        ContinuousLinearMap.neg_apply, inner_neg_left, inner_neg_right]
  have hbranchEndpoint :
      (sourceInclusion lambda)† ∘L branch ∘L endpoint =
        (sourceInclusion lambda)† ∘L detectorOperator owner ∘L
          sourceSoninComplement lambda ∘L endpoint := by
    have h := congrArg ContinuousLinearMap.adjoint hbranchInclusion
    rw [ContinuousLinearMap.adjoint_comp] at h
    rw [hbranchAdj] at h
    rw [ContinuousLinearMap.comp_neg] at h
    rw [hadjoint_neg_source] at h
    simp only [ContinuousLinearMap.adjoint_comp, hdetectorAdj, hcomplementAdj]
      at h
    have hJ :
        (sourceInclusion lambda)† ∘L branch =
          (sourceInclusion lambda)† ∘L detectorOperator owner ∘L
            sourceSoninComplement lambda := by
      apply neg_inj.mp
      simpa only [ContinuousLinearMap.comp_assoc, map_neg] using h
    simpa only [ContinuousLinearMap.comp_assoc] using
      congrArg (fun q : finiteSCarrier →L[ℂ] sourceSoninCarrier lambda =>
        q ∘L endpoint) hJ
  have hforwardComplement :
      forward† ∘L sourceSoninComplement lambda = forward† := by
    have hforwardAdj := congrArg ContinuousLinearMap.adjoint hforward
    rw [ContinuousLinearMap.adjoint_comp, hprojectionAdj] at hforwardAdj
    rw [sourceSoninComplement]
    apply ContinuousLinearMap.ext
    intro x
    have hpoint := congrArg
      (fun operator : finiteSCarrier →L[ℂ] sourceSoninCarrier lambda =>
        operator x) hforwardAdj
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.id_apply, map_sub] at hpoint ⊢
    have hzeroMap :
        ContinuousLinearMap.adjoint
            (0 : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier) =
          (0 : finiteSCarrier →L[ℂ] sourceSoninCarrier lambda) := by
      apply ContinuousLinearMap.ext
      intro y
      exact ext_inner_right ℂ fun z => by
        simp only [ContinuousLinearMap.adjoint_inner_left,
          ContinuousLinearMap.zero_apply, inner_zero_left, inner_zero_right]
    rw [hzeroMap] at hpoint
    simp only [ContinuousLinearMap.zero_apply] at hpoint
    have hpoint' :
        (ContinuousLinearMap.adjoint forward)
            ((sourceSoninProjection lambda) x) = 0 := hpoint
    rw [hpoint']
    simp only [sub_zero]
  have hforwardInclusion :
      forward† ∘L branch ∘L sourceInclusion lambda =
        -(forward† ∘L detectorOperator owner ∘L sourceInclusion lambda) := by
    apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.neg_apply] at ⊢
    have hbranchPoint := congrArg
      (fun q : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier => q x)
      hbranchInclusion
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.neg_apply] at hbranchPoint
    rw [hbranchPoint]
    have hpoint := congrArg
      (fun q : finiteSCarrier →L[ℂ] sourceSoninCarrier lambda =>
        q (detectorOperator owner (sourceInclusion lambda x)))
      hforwardComplement
    have hpoint' :
        (ContinuousLinearMap.adjoint forward)
            (sourceSoninComplement lambda
              (detectorOperator owner (sourceInclusion lambda x))) =
          (ContinuousLinearMap.adjoint forward)
            (detectorOperator owner (sourceInclusion lambda x)) := by
      simpa only [ContinuousLinearMap.comp_apply] using hpoint
    simp only [map_neg]
    rw [hpoint']
  have hadjointAdd (A B : SourceOp lambda) :
      (A + B)† = A† + B† := by
    apply ContinuousLinearMap.ext
    intro y
    exact ext_inner_right ℂ fun z => by
      simp only [ContinuousLinearMap.adjoint_inner_left,
        ContinuousLinearMap.add_apply, inner_add_left, inner_add_right]
  unfold rawCoframeBoundaryMoment
  change
    (endpoint† ∘L sourceSoninComplement lambda ∘L
        detectorOperator owner ∘L sourceInclusion lambda +
      (sourceInclusion lambda)† ∘L detectorOperator owner ∘L forward)† = _
  have hleftAdj :
      (endpoint† ∘L sourceSoninComplement lambda ∘L
          detectorOperator owner ∘L sourceInclusion lambda)† =
        (sourceInclusion lambda)† ∘L detectorOperator owner ∘L
          sourceSoninComplement lambda ∘L endpoint := by
    simp only [ContinuousLinearMap.adjoint_comp, hdetectorAdj, hcomplementAdj,
      ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.comp_assoc]
  have hrightAdj :
      ((sourceInclusion lambda)† ∘L detectorOperator owner ∘L forward)† =
        forward† ∘L detectorOperator owner ∘L sourceInclusion lambda := by
    simp only [ContinuousLinearMap.adjoint_comp, hdetectorAdj,
      ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.comp_assoc]
  rw [hadjointAdd, hleftAdj, hrightAdj, ← hbranchEndpoint,
    hforwardInclusion]
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.neg_apply]
  dsimp only [branch]
  abel

/-! ## The actual named Schur row -/

theorem suffixActualBandNamedSchurBoundaryMomentRow_adjoint_eq_threeBranchDifference
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (S : List CCM24VisiblePrime) :
    (suffixActualBandNamedSchurBoundaryMomentRow owner lambda stepData S)† =
      (sourceInclusion lambda)† ∘L
          cc20ThreeBranchCommutator (radialSupportProjection lambda)
            (sourceFourierSupportProjection lambda)
            (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
        suffixActualSchurForwardEndpointCoframe lambda stepData S -
      (sourceActualBandForwardSchurCoframe lambda stepData S)† ∘L
          cc20ThreeBranchCommutator (radialSupportProjection lambda)
            (sourceFourierSupportProjection lambda)
            (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
        sourceInclusion lambda := by
  unfold suffixActualBandNamedSchurBoundaryMomentRow
  exact rawCoframeBoundaryMoment_adjoint_eq_threeBranchDifference
    owner lambda
    (sourceActualBandForwardSchurCoframe lambda stepData S)
    (suffixActualSchurForwardEndpointCoframe lambda stepData S)
    (sourceSoninProjection_comp_sourceActualBandForwardSchurCoframe_eq_zero
      lambda stepData S)

set_option maxHeartbeats 4000000 in
-- The two row specializations below are rewritten through nested rectangular
-- adjoints before the signed transition coboundary is normalized.
theorem suffixActualBandNamedSchurTransitionSkewRow_adjoint_eq_physicalCoboundary
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime) :
    (suffixActualBandNamedSchurTransitionSkewRow owner lambda stepData p S)† =
      ((suffixActualSchurFrameStep lambda stepData p S).transition -
          (suffixActualSchurFrameStep lambda stepData p S).transition†)† ∘L
        ((sourceInclusion lambda)† ∘L
            cc20ThreeBranchCommutator (radialSupportProjection lambda)
              (sourceFourierSupportProjection lambda)
              (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
          suffixActualSchurForwardEndpointCoframe lambda stepData S -
          (sourceActualBandForwardSchurCoframe lambda stepData S)† ∘L
            cc20ThreeBranchCommutator (radialSupportProjection lambda)
              (sourceFourierSupportProjection lambda)
              (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
            sourceInclusion lambda) -
      ((sourceInclusion lambda)† ∘L
          cc20ThreeBranchCommutator (radialSupportProjection lambda)
            (sourceFourierSupportProjection lambda)
            (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
        suffixActualSchurForwardEndpointCoframe lambda stepData (p :: S) -
        (sourceActualBandForwardSchurCoframe lambda stepData (p :: S))† ∘L
          cc20ThreeBranchCommutator (radialSupportProjection lambda)
            (sourceFourierSupportProjection lambda)
            (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
          sourceInclusion lambda) ∘L
        ((suffixActualSchurFrameStep lambda stepData p S).transition -
          (suffixActualSchurFrameStep lambda stepData p S).transition†)† := by
  have hadjoint_sub (A B : SourceOp lambda) :
      (A - B)† = A† - B† := by
    apply ContinuousLinearMap.ext
    intro y
    exact ext_inner_right ℂ fun z => by
      simp only [ContinuousLinearMap.adjoint_inner_left,
        ContinuousLinearMap.sub_apply, inner_sub_left, inner_sub_right]
  have hold :=
    suffixActualBandNamedSchurBoundaryMomentRow_adjoint_eq_threeBranchDifference
      owner lambda stepData S
  have hnew :=
    suffixActualBandNamedSchurBoundaryMomentRow_adjoint_eq_threeBranchDifference
      owner lambda stepData (p :: S)
  unfold suffixActualBandNamedSchurTransitionSkewRow
  rw [hadjoint_sub, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_comp, hold, hnew]

end CCM24FiniteSActualSchurSkewPhysicalOwner
end CCM25Concrete
end Source
end ConnesWeilRH
