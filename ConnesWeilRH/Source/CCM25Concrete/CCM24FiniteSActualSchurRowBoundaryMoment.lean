/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSJointResidualDouglasReadout
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSActualSchurTelescoping
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawCoframeBoundaryTelescope

/-!
# Source Schur-row boundary-moment telescope

The named Schur row from Proof 566 has a genuine source-level telescope.  Its
forward coframes lie in the source Sonin complement, so the physical
four-term row is exactly the difference of two `rawCoframeBoundaryMoment`
maps transported by the same adjacent source transition.

This is an exact carrier/orientation reduction.  It does not assert that the
boundary moment factors through the local Julia left co-defect, nor does it
prove the family-uniform Douglas estimate required by Gate 3U.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSActualSchurRowBoundaryMoment

open scoped InnerProduct

open CC20Concrete
open CCM24FiniteSActualJuliaInput
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSActualSchurForwardPhysicalDifference
open CCM24FiniteSActualSchurForwardTransport
open CCM24FiniteSActualSchurTelescoping
open CCM24FiniteSCompletedJuliaRawCoframeBoundaryTelescope
open CCM24FiniteSCompletedJuliaRawPhysicalResidualLedger
open CCM24FiniteSJointResidualDouglasReadout
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSProjectionTrace
open CCM24FiniteSRawRemainderCommonPair
open CCM24FiniteSRootCompletedFirstJet

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace
      (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

local notation "SourceOp" lambda =>
  sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda

/-! ## The Schur forward coframe is source-Sonin orthogonal -/

theorem sourceSoninProjection_comp_sourceActualBandForwardSchurCoframe_eq_zero
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (S : List CCM24VisiblePrime) :
    sourceSoninProjection lambda ∘L
        sourceActualBandForwardSchurCoframe lambda stepData S = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  have hzero := congrArg
    (fun operator : finiteSCarrier →L[ℂ] finiteSCarrier =>
      operator
        ((suffixActualSchurForwardAmbientProduct lambda stepData S)
          (CCM24FiniteSGramResponse.sourceInclusion lambda x)))
    (sourceSoninProjection_comp_sourceBandProjection_eq_zero lambda)
  simpa only [sourceActualBandForwardSchurCoframe,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply] using hzero

/-! ## The transition-orientation residual -/

theorem suffixEulerFrameTransition_sub_actualSchurTransitionAdjoint_eq_transportAdjointGap
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime) :
    suffixEulerFrameTransition lambda p S -
        (suffixActualSchurFrameStep lambda stepData p S).transition† =
      (oldSuffixFrame lambda p S)† ∘L
          (normalizedPrimeEulerFrameTransport p -
            (suffixActualSchurFrameStep lambda stepData p S).transport†) ∘L
        newSuffixFrame lambda S := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [suffixEulerFrameTransition, suffixActualSchurFrameStep,
    ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.sub_apply, map_sub]

/-! ## The named Schur boundary moment -/

noncomputable def suffixActualBandNamedSchurBoundaryMomentRow
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (S : List CCM24VisiblePrime) : SourceOp lambda :=
  rawCoframeBoundaryMoment owner lambda
    (sourceActualBandForwardSchurCoframe lambda stepData S)
    (suffixActualSchurForwardEndpointCoframe lambda stepData S)

noncomputable def suffixActualBandNamedSchurTransitionGapRow
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime) : SourceOp lambda :=
  suffixActualBandNamedSchurBoundaryMomentRow owner lambda stepData S ∘L
      ((suffixEulerFrameTransition lambda p S)† -
        (suffixActualSchurFrameStep lambda stepData p S).transition†) -
    ((suffixEulerFrameTransition lambda p S)† -
        (suffixActualSchurFrameStep lambda stepData p S).transition†) ∘L
      suffixActualBandNamedSchurBoundaryMomentRow owner lambda stepData (p :: S)

/-! ## Exact source-row telescope -/

theorem suffixActualBandNamedSchurRawPhysicalFourTermRow_eq_boundaryMoment_telescope
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime) :
    suffixActualBandNamedSchurRawPhysicalFourTermRow owner lambda stepData p S =
      suffixActualBandNamedSchurBoundaryMomentRow owner lambda stepData S ∘L
          (suffixEulerFrameTransition lambda p S)† -
        (suffixEulerFrameTransition lambda p S)† ∘L
          suffixActualBandNamedSchurBoundaryMomentRow owner lambda stepData (p :: S) := by
  unfold suffixActualBandNamedSchurRawPhysicalFourTermRow
    suffixActualBandNamedSchurBoundaryMomentRow
  exact rawPhysicalFourTermRowOfCoframes_eq_boundaryMoment_telescope
    owner lambda p S
    (sourceActualBandForwardSchurCoframe lambda stepData S)
    (suffixActualSchurForwardEndpointCoframe lambda stepData S)
    (suffixActualSchurForwardEndpointCoframe lambda stepData (p :: S))
    (sourceActualBandForwardSchurCoframe lambda stepData (p :: S))
    (sourceSoninProjection_comp_sourceActualBandForwardSchurCoframe_eq_zero
      lambda stepData S)
    (sourceSoninProjection_comp_sourceActualBandForwardSchurCoframe_eq_zero
      lambda stepData (p :: S))

set_option maxHeartbeats 4000000 in
-- The operator-valued distributive rearrangement expands the signed
-- transition coboundary after the source/target carriers are elaborated.
theorem suffixActualBandNamedSchurRawPhysicalFourTermRow_eq_actualSchurCoboundary_add_transitionGap
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime) :
    suffixActualBandNamedSchurRawPhysicalFourTermRow owner lambda stepData p S =
      suffixActualBandNamedSchurBoundaryMomentRow owner lambda stepData S ∘L
          (suffixActualSchurFrameStep lambda stepData p S).transition† -
        (suffixActualSchurFrameStep lambda stepData p S).transition† ∘L
          suffixActualBandNamedSchurBoundaryMomentRow owner lambda stepData (p :: S) +
        suffixActualBandNamedSchurTransitionGapRow owner lambda stepData p S := by
  rw [suffixActualBandNamedSchurRawPhysicalFourTermRow_eq_boundaryMoment_telescope
    owner lambda stepData p S]
  unfold suffixActualBandNamedSchurTransitionGapRow
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.comp_apply, map_sub]
  abel

end CCM24FiniteSActualSchurRowBoundaryMoment
end CCM25Concrete
end Source
end ConnesWeilRH
