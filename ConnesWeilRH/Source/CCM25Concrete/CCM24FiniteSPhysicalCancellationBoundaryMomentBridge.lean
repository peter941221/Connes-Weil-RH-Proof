/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSPhysicalCancellationEndpointNormalForm
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSActualSchurEndpointAlignmentResidual
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawCoframeBoundaryTelescope

/-!
# Boundary-moment bridge for the endpoint cancellation residual

Proof 726 names the complete endpoint residual. The raw coframe telescope
already has a physical boundary moment whose first coordinate is
`(endpoint - inclusion)^dagger`. This file identifies that coordinate with the
named residual and reads the complete signed moment back to the existing
finite-S remainder response.

No residual-only factorization, cancellation, norm estimate, Gate 3U bound,
finite-S sign, or RH premise is asserted.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSPhysicalCancellationBoundaryMomentBridge

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.PositiveTrace
open CCM24FiniteSActualBandSourceRemainder
open CCM24FiniteSActualSchurEndpointAlignmentResidual
open CCM24FiniteSCombinedCoframeGuard
open CCM24FiniteSCompletedJuliaRawCoframeBoundaryTelescope
open CCM24FiniteSGramResponse
open CCM24FiniteSPhysicalCancellationEndpointNormalForm
open CCM24FiniteSProjectionTrace
open CCM24FiniteSRawLocalTraceFactorization
open CCM24FiniteSRawRemainderCommonPair

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- The complete signed boundary moment with the Proof 726 endpoint residual
kept as its first coordinate. -/
noncomputable def sourceEndpointCancellationBoundaryMoment
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
  (sourceEndpointCancellationResidual lambda family)† ∘L
      detectorOperator owner ∘L sourceInclusion lambda +
    (sourceInclusion lambda)† ∘L detectorOperator owner ∘L
      sourceActualBandForwardCoframe lambda family

/-- The named moment is exactly the existing raw coframe boundary moment on
the family-indexed forward and endpoint coframes. -/
theorem rawCoframeBoundaryMoment_eq_sourceEndpointCancellationBoundaryMoment
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    rawCoframeBoundaryMoment owner lambda
        (sourceActualBandForwardCoframe lambda family)
        (sourceActualBandForwardEndpointCoframe lambda family) =
      sourceEndpointCancellationBoundaryMoment owner lambda family := by
  rw [rawCoframeBoundaryMoment_eq_leakage_of_endpoint_compression
    owner lambda (sourceActualBandForwardCoframe lambda family)
      (sourceActualBandForwardEndpointCoframe lambda family)
      (sourceSoninProjection_comp_sourceActualBandForwardEndpointCoframe
        lambda family)]
  rw [← sourceEndpointCancellationResidual_eq_endpoint_sub_inclusion]
  rfl

/-- The family-indexed moment and the literal visible-prime suffix moment are
the same operator. -/
theorem sourceEndpointCancellationBoundaryMoment_eq_suffixBoundaryMoment
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceEndpointCancellationBoundaryMoment owner lambda family =
      rawCoframeBoundaryMoment owner lambda
        (suffixActualBandForwardCoframe lambda family.visiblePrimes)
        (suffixActualBandForwardEndpointCoframe lambda family.visiblePrimes) := by
  rw [suffixActualBandForwardCoframe_visiblePrimes_eq_sourceActualBandForwardCoframe,
    suffixActualBandForwardEndpointCoframe_visiblePrimes_eq_sourceActualBandForwardEndpointCoframe]
  exact
    (rawCoframeBoundaryMoment_eq_sourceEndpointCancellationBoundaryMoment
      owner lambda family).symm

/-- The complete residual/forward moment is not a new owner: it is exactly the
adjoint of the existing finite-S remainder response. -/
theorem sourceEndpointCancellationBoundaryMoment_eq_remainderResponse_adjoint
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceEndpointCancellationBoundaryMoment owner lambda family =
      (sourceActualBandFiniteEulerRemainderResponse owner lambda family)† := by
  rw [sourceEndpointCancellationBoundaryMoment_eq_suffixBoundaryMoment]
  exact suffixActualBandRawCoframeBoundaryMoment_eq_remainderResponse_adjoint
    owner lambda family

/-- Trace legality transfers from the existing remainder response to the
named complete boundary moment. -/
theorem sourceEndpointCancellationBoundaryMoment_isTraceClassAlong
    {ι : Type*} (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (basis : HilbertBasis ι ℂ (sourceSoninCarrier lambda))
    (hresponse : IsTraceClassAlong basis
      (sourceActualBandFiniteEulerRemainderResponse owner lambda family)) :
    IsTraceClassAlong basis
      (sourceEndpointCancellationBoundaryMoment owner lambda family) := by
  rw [sourceEndpointCancellationBoundaryMoment_eq_remainderResponse_adjoint]
  exact isTraceClassAlong_adjoint basis _ hresponse

/-- The ordinary trace of the complete boundary moment has the exact adjoint
orientation of the existing remainder response. -/
theorem sourceEndpointCancellationBoundaryMoment_ordinaryTraceAlong_eq_star
    {ι : Type*} (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (basis : HilbertBasis ι ℂ (sourceSoninCarrier lambda)) :
    ordinaryTraceAlong basis
        (sourceEndpointCancellationBoundaryMoment owner lambda family) =
      star (ordinaryTraceAlong basis
        (sourceActualBandFiniteEulerRemainderResponse owner lambda family)) := by
  rw [sourceEndpointCancellationBoundaryMoment_eq_remainderResponse_adjoint]
  exact ordinaryTraceAlong_adjoint basis _

/-- Even if the endpoint residual vanishes, the forward coordinate remains in
the complete signed moment. This guard prevents a residual-only zero claim. -/
theorem sourceEndpointCancellationBoundaryMoment_eq_forwardTerm_of_residual_eq_zero
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (hresidual : sourceEndpointCancellationResidual lambda family = 0) :
    sourceEndpointCancellationBoundaryMoment owner lambda family =
      (sourceInclusion lambda)† ∘L detectorOperator owner ∘L
        sourceActualBandForwardCoframe lambda family := by
  have hadjointZero :
      ContinuousLinearMap.adjoint
          (0 : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier) = 0 := by
    apply ContinuousLinearMap.ext
    intro y
    apply ext_inner_right ℂ
    intro x
    simp only [ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearMap.zero_apply, inner_zero_left, inner_zero_right]
  rw [sourceEndpointCancellationBoundaryMoment, hresidual, hadjointZero]
  simp

end CCM24FiniteSPhysicalCancellationBoundaryMomentBridge
end CCM25Concrete
end Source
end ConnesWeilRH
