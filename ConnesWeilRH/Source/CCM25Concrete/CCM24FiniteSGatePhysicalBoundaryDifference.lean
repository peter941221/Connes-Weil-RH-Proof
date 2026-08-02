/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSGateBoundaryMomentBridge
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSActualSchurSkewPhysicalOwner

/-!
# Physical boundary-difference owner for the Gate response

Proof 728 makes the Gate-facing response the adjoint of the complete boundary
moment.  The existing physical-owner theorem identifies that adjoint with one
signed difference built from the genuine three-branch Sonin commutator.  This
file joins those facts on the family-indexed endpoint and forward coframes.

Both terms remain inside one operator.  No branchwise estimate, uniform bound,
finite-S sign, or RH premise is asserted.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSGatePhysicalBoundaryDifference

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.PositiveTrace
open CCM24FiniteSActualSchurSkewPhysicalOwner
open CCM24FiniteSCombinedCoframeGuard
open CCM24FiniteSGateBoundaryMomentBridge
open CCM24FiniteSGramResponse
open CCM24FiniteSPhysicalCancellationBoundaryMomentBridge
open CCM24FiniteSProjectionTrace
open CCM24FiniteSRawCompletedGaugeOwner
open CCM24FiniteSRawRemainderCommonPair

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- The existing common physical difference is exactly the adjoint of Proof
727's complete signed boundary moment. -/
theorem sourceActualBandRawRemainderCommonPhysicalResponse_eq_boundaryMoment_adjoint
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceActualBandRawRemainderCommonPhysicalResponse owner lambda family =
      (sourceEndpointCancellationBoundaryMoment owner lambda family)† := by
  have hphysical := rawCoframeBoundaryMoment_adjoint_eq_threeBranchDifference
    owner lambda (sourceActualBandForwardCoframe lambda family)
      (sourceActualBandForwardEndpointCoframe lambda family)
      (sourceSoninProjection_comp_sourceActualBandForwardCoframe_eq_zero
        lambda family)
  rw [← rawCoframeBoundaryMoment_eq_sourceEndpointCancellationBoundaryMoment]
  simpa only [sourceActualBandRawRemainderCommonPhysicalResponse] using
    hphysical.symm

/-- The Gate-facing lower-factor-gauged response is literally the same
complete physical boundary difference. -/
theorem lowerFactorGaugedResponse_eq_commonPhysicalResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    lowerFactorGaugedActualBandCompletedRelativeResponse owner lambda family =
      sourceActualBandRawRemainderCommonPhysicalResponse
        owner lambda family := by
  exact
    (lowerFactorGaugedResponse_eq_sourceEndpointCancellationBoundaryMoment_adjoint
      owner lambda family).trans
      (sourceActualBandRawRemainderCommonPhysicalResponse_eq_boundaryMoment_adjoint
        owner lambda family).symm

/-- Expanded Gate-facing form.  This is the exact signed operator that the
uniform estimate must control. -/
theorem lowerFactorGaugedResponse_eq_completePhysicalBoundaryDifference
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    lowerFactorGaugedActualBandCompletedRelativeResponse owner lambda family =
      (sourceInclusion lambda)† ∘L
          cc20ThreeBranchCommutator (radialSupportProjection lambda)
            (sourceFourierSupportProjection lambda)
            (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
          sourceActualBandForwardEndpointCoframe lambda family -
        (sourceActualBandForwardCoframe lambda family)† ∘L
          cc20ThreeBranchCommutator (radialSupportProjection lambda)
            (sourceFourierSupportProjection lambda)
            (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
          sourceInclusion lambda := by
  rw [lowerFactorGaugedResponse_eq_commonPhysicalResponse]
  rfl

/-- Fixed-family trace legality is equivalent for the Gate response and its
complete physical boundary-difference owner. -/
theorem lowerFactorGaugedResponse_isTraceClassAlong_iff_commonPhysicalResponse
    {ι : Type*} (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (basis : HilbertBasis ι ℂ (sourceSoninCarrier lambda)) :
    IsTraceClassAlong basis
        (lowerFactorGaugedActualBandCompletedRelativeResponse
          owner lambda family) ↔
      IsTraceClassAlong basis
        (sourceActualBandRawRemainderCommonPhysicalResponse
          owner lambda family) := by
  rw [lowerFactorGaugedResponse_eq_commonPhysicalResponse]

/-- The ordinary Gate trace is the ordinary trace of the complete physical
boundary difference, with no cycle or conjugation remaining. -/
theorem ordinaryTraceAlong_lowerFactorGaugedResponse_eq_commonPhysicalResponse
    {ι : Type*} (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (basis : HilbertBasis ι ℂ (sourceSoninCarrier lambda)) :
    ordinaryTraceAlong basis
        (lowerFactorGaugedActualBandCompletedRelativeResponse
          owner lambda family) =
      ordinaryTraceAlong basis
        (sourceActualBandRawRemainderCommonPhysicalResponse
          owner lambda family) := by
  rw [lowerFactorGaugedResponse_eq_commonPhysicalResponse]

/-- Every scalar trace-norm upper bound transfers in both directions while
the two physical coordinates remain inside one signed operator. -/
theorem lowerFactorGaugedResponse_trace_norm_le_iff_commonPhysicalResponse
    {ι : Type*} (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (basis : HilbertBasis ι ℂ (sourceSoninCarrier lambda)) (bound : ℝ) :
    ‖ordinaryTraceAlong basis
        (lowerFactorGaugedActualBandCompletedRelativeResponse
          owner lambda family)‖ ≤ bound ↔
      ‖ordinaryTraceAlong basis
        (sourceActualBandRawRemainderCommonPhysicalResponse
          owner lambda family)‖ ≤
          bound := by
  rw [ordinaryTraceAlong_lowerFactorGaugedResponse_eq_commonPhysicalResponse]

end CCM24FiniteSGatePhysicalBoundaryDifference
end CCM25Concrete
end Source
end ConnesWeilRH
