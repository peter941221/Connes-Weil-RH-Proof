/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSPhysicalCancellationBoundaryMomentBridge
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSRawCompletedGaugeOwner

/-!
# Gate-trace bridge for the physical cancellation boundary moment

Proof 727 identifies the complete signed boundary moment with the adjoint of
the actual finite-S remainder response.  The existing lower-factor gauge owner
is exactly that same remainder response.  This file composes those two
same-object identities and transfers ordinary-trace legality, conjugation, and
absolute bounds without a trace cycle or a real-trace premise.

No uniform bound, residual cancellation, finite-S sign, or RH premise is
asserted.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSGateBoundaryMomentBridge

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.PositiveTrace
open CCM24FiniteSGramResponse
open CCM24FiniteSPhysicalCancellationBoundaryMomentBridge
open CCM24FiniteSProjectionTrace
open CCM24FiniteSRawCompletedGaugeOwner

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- The complete signed boundary moment is the adjoint of the Gate-facing
lower-factor-gauged response on the same source Sonin carrier. -/
theorem sourceEndpointCancellationBoundaryMoment_eq_lowerFactorGaugedResponse_adjoint
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceEndpointCancellationBoundaryMoment owner lambda family =
      (lowerFactorGaugedActualBandCompletedRelativeResponse
        owner lambda family)† := by
  rw [sourceEndpointCancellationBoundaryMoment_eq_remainderResponse_adjoint,
    lowerFactorGaugedActualBandCompletedRelativeResponse_eq_sourceRemainder]

/-- Conversely, the Gate-facing response is the adjoint of the complete
signed boundary moment. -/
theorem lowerFactorGaugedResponse_eq_sourceEndpointCancellationBoundaryMoment_adjoint
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    lowerFactorGaugedActualBandCompletedRelativeResponse owner lambda family =
      (sourceEndpointCancellationBoundaryMoment owner lambda family)† := by
  rw [sourceEndpointCancellationBoundaryMoment_eq_lowerFactorGaugedResponse_adjoint,
    ContinuousLinearMap.adjoint_adjoint]

/-- Fixed-family trace legality is equivalent for the Gate-facing response
and the complete signed boundary moment. -/
theorem lowerFactorGaugedResponse_isTraceClassAlong_iff_boundaryMoment
    {ι : Type*} (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (basis : HilbertBasis ι ℂ (sourceSoninCarrier lambda)) :
    IsTraceClassAlong basis
        (lowerFactorGaugedActualBandCompletedRelativeResponse
          owner lambda family) ↔
      IsTraceClassAlong basis
        (sourceEndpointCancellationBoundaryMoment owner lambda family) := by
  constructor
  · intro hgate
    rw [sourceEndpointCancellationBoundaryMoment_eq_lowerFactorGaugedResponse_adjoint]
    exact isTraceClassAlong_adjoint basis _ hgate
  · intro hboundary
    rw [lowerFactorGaugedResponse_eq_sourceEndpointCancellationBoundaryMoment_adjoint]
    exact isTraceClassAlong_adjoint basis _ hboundary

/-- The boundary-moment trace is the complex conjugate of the Gate-facing
trace.  This uses only adjoint orientation, not cyclicity. -/
theorem ordinaryTraceAlong_boundaryMoment_eq_star_lowerFactorGaugedResponse
    {ι : Type*} (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (basis : HilbertBasis ι ℂ (sourceSoninCarrier lambda)) :
    ordinaryTraceAlong basis
        (sourceEndpointCancellationBoundaryMoment owner lambda family) =
      star (ordinaryTraceAlong basis
        (lowerFactorGaugedActualBandCompletedRelativeResponse
          owner lambda family)) := by
  rw [sourceEndpointCancellationBoundaryMoment_eq_lowerFactorGaugedResponse_adjoint]
  exact ordinaryTraceAlong_adjoint basis _

/-- The Gate-facing trace is likewise the complex conjugate of the complete
signed boundary-moment trace. -/
theorem ordinaryTraceAlong_lowerFactorGaugedResponse_eq_star_boundaryMoment
    {ι : Type*} (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (basis : HilbertBasis ι ℂ (sourceSoninCarrier lambda)) :
    ordinaryTraceAlong basis
        (lowerFactorGaugedActualBandCompletedRelativeResponse
          owner lambda family) =
      star (ordinaryTraceAlong basis
        (sourceEndpointCancellationBoundaryMoment owner lambda family)) := by
  rw [lowerFactorGaugedResponse_eq_sourceEndpointCancellationBoundaryMoment_adjoint]
  exact ordinaryTraceAlong_adjoint basis _

/-- Gate 3U only sees the norm of the ordinary trace, which is unchanged by
the exact adjoint orientation. -/
theorem norm_ordinaryTraceAlong_lowerFactorGaugedResponse_eq_boundaryMoment
    {ι : Type*} (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (basis : HilbertBasis ι ℂ (sourceSoninCarrier lambda)) :
    ‖ordinaryTraceAlong basis
        (lowerFactorGaugedActualBandCompletedRelativeResponse
          owner lambda family)‖ =
      ‖ordinaryTraceAlong basis
        (sourceEndpointCancellationBoundaryMoment owner lambda family)‖ := by
  rw [ordinaryTraceAlong_lowerFactorGaugedResponse_eq_star_boundaryMoment,
    Complex.star_def, Complex.norm_conj]

/-- Every scalar upper bound transfers in both directions between the
Gate-facing response and the complete signed boundary moment. -/
theorem lowerFactorGaugedResponse_trace_norm_le_iff_boundaryMoment
    {ι : Type*} (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (basis : HilbertBasis ι ℂ (sourceSoninCarrier lambda)) (bound : ℝ) :
    ‖ordinaryTraceAlong basis
        (lowerFactorGaugedActualBandCompletedRelativeResponse
          owner lambda family)‖ ≤ bound ↔
      ‖ordinaryTraceAlong basis
        (sourceEndpointCancellationBoundaryMoment owner lambda family)‖ ≤
          bound := by
  rw [norm_ordinaryTraceAlong_lowerFactorGaugedResponse_eq_boundaryMoment]

end CCM24FiniteSGateBoundaryMomentBridge
end CCM25Concrete
end Source
end ConnesWeilRH
