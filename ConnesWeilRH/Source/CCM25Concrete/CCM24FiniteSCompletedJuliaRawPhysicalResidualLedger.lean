/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalFactorization
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSActualSchurForwardPhysicalDifference

/-!
# Actual versus Schur raw-physical residual ledger

The Schur telescope and the physical inverse use different coframes.  This
file records their exact four-term difference on the source carrier.  The
residual is not set to zero and no estimate is inferred from the telescope.

The useful downstream statement is deliberately conditional: if a Schur row
and its physical residual each factor through the two-channel analysis column,
then their sum is an actual component-row producer.  This isolates the missing
source theorem without changing the Gate 3U consumer.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedJuliaRawPhysicalResidualLedger

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCompletedJuliaAmbientDefectFactorization
open CCM24FiniteSCompletedJuliaRawPhysicalFactorization
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSProjectionTrace
open CCM24FiniteSActualJuliaInput
open CCM24FiniteSActualSchurForwardPhysicalDifference
open CCM24FiniteSActualSchurForwardTransport
open CCM24FiniteSCausalMarkov
open CCM24FiniteSRawLocalTraceFactorization

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) :
      CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

local notation "SourceOp" lambda =>
  sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda

/-! ## The common four-term row -/

/-- The raw physical four-term row for arbitrary forward and endpoint
coframes.  Keeping the coframes as arguments makes the residual ledger
independent of any proposed Schur/physical identification. -/
noncomputable def rawPhysicalFourTermRowOfCoframes
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime)
    (forwardS endpointS endpointPS forwardPS :
      sourceSoninCarrier lambda →L[ℂ] finiteSCarrier) : SourceOp lambda :=
  -((endpointS)† ∘L
      cc20ThreeBranchCommutator (radialSupportProjection lambda)
        (sourceFourierSupportProjection lambda)
        (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
      CCM24FiniteSGramResponse.sourceInclusion lambda ∘L
      (suffixEulerFrameTransition lambda p S)†) +
    (CCM24FiniteSGramResponse.sourceInclusion lambda)† ∘L
      cc20ThreeBranchCommutator (radialSupportProjection lambda)
        (sourceFourierSupportProjection lambda)
        (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
      forwardS ∘L (suffixEulerFrameTransition lambda p S)† +
    (suffixEulerFrameTransition lambda p S)† ∘L
      (endpointPS)† ∘L
      cc20ThreeBranchCommutator (radialSupportProjection lambda)
        (sourceFourierSupportProjection lambda)
        (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
      CCM24FiniteSGramResponse.sourceInclusion lambda -
    (suffixEulerFrameTransition lambda p S)† ∘L
      (CCM24FiniteSGramResponse.sourceInclusion lambda)† ∘L
      cc20ThreeBranchCommutator (radialSupportProjection lambda)
        (sourceFourierSupportProjection lambda)
        (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
      forwardPS

theorem actualRawPhysicalFourTermRow_eq_ofCoframes
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandRawPhysicalFourTermRow owner lambda p S =
      rawPhysicalFourTermRowOfCoframes owner lambda p S
        (suffixActualBandForwardCoframe lambda S)
        (suffixActualBandForwardEndpointCoframe lambda S)
        (suffixActualBandForwardEndpointCoframe lambda (p :: S))
        (suffixActualBandForwardCoframe lambda (p :: S)) := by
  rfl

/-! ## Named source-forward Schur coframes -/

/-- The source-forward Schur endpoint coframe with the actual metric coframe
on a literal suffix. -/
noncomputable def suffixActualSchurForwardEndpointCoframe
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (S : List CCM24VisiblePrime) :
    sourceSoninCarrier lambda →L[ℂ] finiteSCarrier :=
  sourceActualBandForwardSchurCoframe lambda stepData S +
    suffixActualBandMetricCoframe lambda S

/-- The physical forward coframe split is the literal-list specialization of
Proof 521's physical-inverse residual identity. -/
theorem suffixActualBandForwardCoframe_eq_namedSchur_add_transportResidual
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (S : List CCM24VisiblePrime) :
    suffixActualBandForwardCoframe lambda S =
      sourceActualBandForwardSchurCoframe lambda stepData S +
        sourceActualBandForwardTransportResidual lambda stepData S := by
  have hres :=
    normalizedFiniteEulerInverseList_sub_forwardAmbient_eq_residual
      lambda stepData S
  apply ContinuousLinearMap.ext
  intro x
  have hpoint := congrArg
    (fun operator : finiteSCarrier →L[ℂ] finiteSCarrier =>
      operator (CCM24FiniteSGramResponse.sourceInclusion lambda x)) hres
  simp only [suffixActualBandForwardCoframe,
    sourceActualBandForwardSchurCoframe,
    sourceActualBandForwardTransportResidual,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.add_apply] at hpoint ⊢
  rw [show normalizedFiniteEulerInverseList S
        (CCM24FiniteSGramResponse.sourceInclusion lambda x) =
      (suffixActualSchurForwardAmbientProduct lambda stepData S)
          (CCM24FiniteSGramResponse.sourceInclusion lambda x) +
        (suffixActualSchurForwardPhysicalTransportResidual lambda stepData S)
          (CCM24FiniteSGramResponse.sourceInclusion lambda x) by
    simpa only [ContinuousLinearMap.sub_apply, add_comm] using
      sub_eq_iff_eq_add.mp hpoint]
  exact (sourceBandProjection lambda).map_add _ _

theorem suffixActualBandForwardEndpointCoframe_eq_namedSchurEndpoint_add_transportResidual
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (S : List CCM24VisiblePrime) :
    suffixActualBandForwardEndpointCoframe lambda S =
      suffixActualSchurForwardEndpointCoframe lambda stepData S +
        sourceActualBandForwardTransportResidual lambda stepData S := by
  rw [suffixActualBandForwardEndpointCoframe,
    suffixActualSchurForwardEndpointCoframe,
    suffixActualBandForwardCoframe_eq_namedSchur_add_transportResidual
      lambda stepData S]
  abel

/-! ## Exact residual decomposition -/

/-- The four coframe deltas between an actual physical row and a proposed
Schur row. -/
noncomputable def rawPhysicalCoframeResidualRow
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime)
    (actualForwardS actualEndpointS actualEndpointPS actualForwardPS :
      sourceSoninCarrier lambda →L[ℂ] finiteSCarrier)
    (schurForwardS schurEndpointS schurEndpointPS schurForwardPS :
      sourceSoninCarrier lambda →L[ℂ] finiteSCarrier) : SourceOp lambda :=
  rawPhysicalFourTermRowOfCoframes owner lambda p S
      actualForwardS actualEndpointS actualEndpointPS actualForwardPS -
    rawPhysicalFourTermRowOfCoframes owner lambda p S
      schurForwardS schurEndpointS schurEndpointPS schurForwardPS

set_option maxHeartbeats 4000000 in
-- The four-term continuous-linear-map extensionality proof normalizes a
-- deeply nested signed composition expression.
set_option maxRecDepth 10000 in
/- Exact row-level bookkeeping: actual physical row equals the proposed
Schur row plus the four coframe residual channels. -/
theorem rawPhysicalFourTermRow_eq_schur_add_residual
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime)
    (actualForwardS actualEndpointS actualEndpointPS actualForwardPS :
      sourceSoninCarrier lambda →L[ℂ] finiteSCarrier)
    (schurForwardS schurEndpointS schurEndpointPS schurForwardPS :
      sourceSoninCarrier lambda →L[ℂ] finiteSCarrier) :
    rawPhysicalFourTermRowOfCoframes owner lambda p S
        actualForwardS actualEndpointS actualEndpointPS actualForwardPS =
      rawPhysicalFourTermRowOfCoframes owner lambda p S
          schurForwardS schurEndpointS schurEndpointPS schurForwardPS +
    rawPhysicalCoframeResidualRow owner lambda p S
          actualForwardS actualEndpointS actualEndpointPS actualForwardPS
          schurForwardS schurEndpointS schurEndpointPS schurForwardPS := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [rawPhysicalCoframeResidualRow,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply]
  abel

/-- Specialization of the ledger to the repository's actual row. -/
theorem suffixActualBandRawPhysicalFourTermRow_eq_schur_add_residual
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime)
    (schurForwardS schurEndpointS schurEndpointPS schurForwardPS :
      sourceSoninCarrier lambda →L[ℂ] finiteSCarrier) :
    suffixActualBandRawPhysicalFourTermRow owner lambda p S =
      rawPhysicalFourTermRowOfCoframes owner lambda p S
          schurForwardS schurEndpointS schurEndpointPS schurForwardPS +
        rawPhysicalCoframeResidualRow owner lambda p S
          (suffixActualBandForwardCoframe lambda S)
          (suffixActualBandForwardEndpointCoframe lambda S)
          (suffixActualBandForwardEndpointCoframe lambda (p :: S))
          (suffixActualBandForwardCoframe lambda (p :: S))
          schurForwardS schurEndpointS schurEndpointPS schurForwardPS := by
  rw [actualRawPhysicalFourTermRow_eq_ofCoframes,
    rawPhysicalFourTermRow_eq_schur_add_residual]

/-! ## The named source-forward Schur row -/

/-- The generic residual ledger instantiated with the actual Proof 521
source-forward Schur coframes. -/
theorem suffixActualBandRawPhysicalFourTermRow_eq_namedSchur_add_residual
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime) :
    suffixActualBandRawPhysicalFourTermRow owner lambda p S =
      rawPhysicalFourTermRowOfCoframes owner lambda p S
          (sourceActualBandForwardSchurCoframe lambda stepData S)
          (suffixActualSchurForwardEndpointCoframe lambda stepData S)
          (suffixActualSchurForwardEndpointCoframe lambda stepData (p :: S))
          (sourceActualBandForwardSchurCoframe lambda stepData (p :: S)) +
        rawPhysicalCoframeResidualRow owner lambda p S
          (suffixActualBandForwardCoframe lambda S)
          (suffixActualBandForwardEndpointCoframe lambda S)
          (suffixActualBandForwardEndpointCoframe lambda (p :: S))
          (suffixActualBandForwardCoframe lambda (p :: S))
          (sourceActualBandForwardSchurCoframe lambda stepData S)
          (suffixActualSchurForwardEndpointCoframe lambda stepData S)
          (suffixActualSchurForwardEndpointCoframe lambda stepData (p :: S))
          (sourceActualBandForwardSchurCoframe lambda stepData (p :: S)) := by
  exact suffixActualBandRawPhysicalFourTermRow_eq_schur_add_residual
    owner lambda p S
    (sourceActualBandForwardSchurCoframe lambda stepData S)
    (suffixActualSchurForwardEndpointCoframe lambda stepData S)
    (suffixActualSchurForwardEndpointCoframe lambda stepData (p :: S))
    (sourceActualBandForwardSchurCoframe lambda stepData (p :: S))

/-! ## Conditional component-row handoff -/

/-- If the proposed Schur row and the physical coframe residual each have
component rows, their sum is an actual component-row factorization.  This is
the precise producer contract left after the residual ledger. -/
theorem componentRows_add_of_schur_and_residual
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    {lambda : CCM24SoninScale}
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
    (schurAmbientRow schurBoundaryRow residualAmbientRow residualBoundaryRow :
      finiteSCarrier →L[ℂ] sourceSoninCarrier lambda)
    (schurFactorization residualFactorization :
      SourceOp lambda) :
    schurFactorization + residualFactorization =
        suffixActualBandRawPhysicalFourTermRow owner lambda p S →
    schurAmbientRow ∘L suffixEulerFrameAmbientLossColumn lambda p S +
          schurBoundaryRow ∘L ContinuousLinearMap.adjoint
            (suffixEulerFrameSchurStep lambda p S).boundary =
        schurFactorization →
    residualAmbientRow ∘L suffixEulerFrameAmbientLossColumn lambda p S +
          residualBoundaryRow ∘L ContinuousLinearMap.adjoint
            (suffixEulerFrameSchurStep lambda p S).boundary =
        residualFactorization →
    (schurAmbientRow + residualAmbientRow) ∘L
          suffixEulerFrameAmbientLossColumn lambda p S +
        (schurBoundaryRow + residualBoundaryRow) ∘L
          ContinuousLinearMap.adjoint
            (suffixEulerFrameSchurStep lambda p S).boundary =
      suffixActualBandRawPhysicalFourTermRow owner lambda p S := by
  intro hrow hschur hresidual
  calc
    (schurAmbientRow + residualAmbientRow) ∘L
          suffixEulerFrameAmbientLossColumn lambda p S +
        (schurBoundaryRow + residualBoundaryRow) ∘L
          ContinuousLinearMap.adjoint
            (suffixEulerFrameSchurStep lambda p S).boundary =
      (schurAmbientRow ∘L suffixEulerFrameAmbientLossColumn lambda p S +
          schurBoundaryRow ∘L ContinuousLinearMap.adjoint
            (suffixEulerFrameSchurStep lambda p S).boundary) +
        (residualAmbientRow ∘L suffixEulerFrameAmbientLossColumn lambda p S +
          residualBoundaryRow ∘L ContinuousLinearMap.adjoint
            (suffixEulerFrameSchurStep lambda p S).boundary) := by
      apply ContinuousLinearMap.ext
      intro x
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply]
      abel
    _ = schurFactorization + residualFactorization := by
      rw [hschur, hresidual]
    _ = suffixActualBandRawPhysicalFourTermRow owner lambda p S := hrow

end CCM24FiniteSCompletedJuliaRawPhysicalResidualLedger
end CCM25Concrete
end Source
end ConnesWeilRH
