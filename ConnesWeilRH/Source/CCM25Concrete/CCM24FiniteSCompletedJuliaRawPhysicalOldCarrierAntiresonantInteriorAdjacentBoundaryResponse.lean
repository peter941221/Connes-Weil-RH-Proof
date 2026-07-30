/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorBoundaryCommutator

/-!
# Actual adjacent boundary response of the antiresonant interior owner

Proof 619 identifies the surviving interior owner with the synchronized
boundary-moment gap followed by the adjoint reverse transition.  This module
expands that exact owner one step further.  The first transition cancels
against the reverse transition only after the complete adjacent difference is
formed:

```text
Interior_(p,S)
  = rho_p * BoundaryResponse_S
    - Transition_(p,S)^dagger
        * BoundaryResponse_(p::S)
        * ReverseTransition_(p,S)^dagger.
```

Each boundary response is the complete outer, second-support, reflected, and
prolate three-branch response with the actual endpoint and forward coframes.
It is not the radial corrected quotient bracket.  No term is estimated and no
uniform Bone 1 readout is asserted.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorAdjacentBoundaryResponse

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCompletedJuliaPolarRawReadout
open CCM24FiniteSCompletedJuliaRawCoframeBoundaryTelescope
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorGap
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeJointPullback
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeOrientationLedger
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSGramResponse
open CCM24FiniteSProjectionTrace
open CCM24FiniteSRawLocalTraceFactorization
open CCM24FiniteSSchurMarkovPairing

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace
      (CCM24FiniteSFrameGramCalculus.sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

local notation "SourceOp" lambda =>
  CCM24FiniteSFrameGramCalculus.sourceSoninCarrier lambda →L[ℂ]
    CCM24FiniteSFrameGramCalculus.sourceSoninCarrier lambda

/-! ## The complete physical boundary response -/

/-- One actual suffix boundary response with every fixed physical branch
retained inside the three-branch commutator. -/
noncomputable def suffixActualBandCompleteBoundaryResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    SourceOp lambda :=
  -((suffixActualBandForwardEndpointCoframe lambda S)† ∘L
      cc20ThreeBranchCommutator (radialSupportProjection lambda)
        (sourceFourierSupportProjection lambda)
        (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
      sourceInclusion lambda) +
    (sourceInclusion lambda)† ∘L
      cc20ThreeBranchCommutator (radialSupportProjection lambda)
        (sourceFourierSupportProjection lambda)
        (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
      suffixActualBandForwardCoframe lambda S

/-- The source-facing boundary moment is exactly the complete physical
three-branch response, not merely one radial quotient correction. -/
theorem suffixActualBandRawCoframeBoundaryMoment_eq_completeBoundaryResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    rawCoframeBoundaryMoment owner lambda
        (suffixActualBandForwardCoframe lambda S)
        (suffixActualBandForwardEndpointCoframe lambda S) =
      suffixActualBandCompleteBoundaryResponse owner lambda S := by
  rw [suffixActualBandRawCoframeBoundaryMoment_eq_rawResponse_adjoint,
    suffixActualBandRawQuadraticCycledResponse_adjoint_eq_physical]
  rfl

/-! ## Adjacent response identity -/

/-- Adjointing the genuine reverse/forward scalar cancellation gives the
orientation needed by the adjacent boundary response. -/
theorem suffixEulerFrameTransitionAdjoint_comp_reverseTransitionAdjoint_eq_scalar
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    (suffixEulerFrameTransition lambda p S)† ∘L
        (suffixEulerFrameReverseTransition lambda p S)† =
      (primeSchurMarkovScalar p : ℂ) •
        ContinuousLinearMap.id ℂ
          (CCM24FiniteSFrameGramCalculus.sourceSoninCarrier lambda) := by
  have hscalarAdjoint :
      ContinuousLinearMap.adjoint
          ((primeSchurMarkovScalar p : ℂ) •
            ContinuousLinearMap.id ℂ
              (CCM24FiniteSFrameGramCalculus.sourceSoninCarrier lambda)) =
        (primeSchurMarkovScalar p : ℂ) •
          ContinuousLinearMap.id ℂ
            (CCM24FiniteSFrameGramCalculus.sourceSoninCarrier lambda) := by
    have hstar : star (primeSchurMarkovScalar p : ℂ) =
        (primeSchurMarkovScalar p : ℂ) := by
      rw [RCLike.star_def, Complex.conj_ofReal]
    simpa only [map_smulₛₗ, hstar, starRingEnd_apply,
      ContinuousLinearMap.adjoint_id] using
      (ContinuousLinearMap.adjoint.map_smulₛₗ
        (primeSchurMarkovScalar p : ℂ)
        (ContinuousLinearMap.id ℂ
          (CCM24FiniteSFrameGramCalculus.sourceSoninCarrier lambda)))
  have h := congrArg ContinuousLinearMap.adjoint
    (suffixEulerFrameReverse_comp_transition lambda p S)
  simpa only [ContinuousLinearMap.adjoint_comp, hscalarAdjoint] using h

/-- The genuine Proof 619 interior owner is one signed adjacent pair of the
actual complete boundary responses.  The old response acquires the scalar
`rho_p`; the new response retains both transition orientations. -/
theorem signedCompressedInteriorOwner_eq_adjacentCompleteBoundaryResponses
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    signedCompressedInteriorOwner owner lambda p S =
      (primeSchurMarkovScalar p : ℂ) •
          suffixActualBandCompleteBoundaryResponse owner lambda S -
        (suffixEulerFrameTransition lambda p S)† ∘L
          suffixActualBandCompleteBoundaryResponse owner lambda (p :: S) ∘L
            (suffixEulerFrameReverseTransition lambda p S)† := by
  have hS :=
    suffixActualBandRawCoframeBoundaryMoment_eq_completeBoundaryResponse
      owner lambda S
  have hpS :=
    suffixActualBandRawCoframeBoundaryMoment_eq_completeBoundaryResponse
      owner lambda (p :: S)
  have hpair :=
    suffixEulerFrameTransitionAdjoint_comp_reverseTransitionAdjoint_eq_scalar
      lambda p S
  have hraw :
      signedCompressedInteriorOwner owner lambda p S =
        (primeSchurMarkovScalar p : ℂ) •
            rawCoframeBoundaryMoment owner lambda
              (suffixActualBandForwardCoframe lambda S)
              (suffixActualBandForwardEndpointCoframe lambda S) -
          (suffixEulerFrameTransition lambda p S)† ∘L
            rawCoframeBoundaryMoment owner lambda
              (suffixActualBandForwardCoframe lambda (p :: S))
              (suffixActualBandForwardEndpointCoframe lambda (p :: S)) ∘L
              (suffixEulerFrameReverseTransition lambda p S)† := by
    rw [signedCompressedInteriorOwner_eq_gap_comp_reverseAdjoint]
    unfold coframeBoundaryMomentGap
    apply ContinuousLinearMap.ext
    intro x
    have hpairPoint := DFunLike.congr_fun hpair x
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply]
      at hpairPoint
    simp only [frameTransitionAdjoint, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply]
    rw [hpairPoint, map_smul]
  calc
    signedCompressedInteriorOwner owner lambda p S =
        (primeSchurMarkovScalar p : ℂ) •
            rawCoframeBoundaryMoment owner lambda
              (suffixActualBandForwardCoframe lambda S)
              (suffixActualBandForwardEndpointCoframe lambda S) -
          (suffixEulerFrameTransition lambda p S)† ∘L
            rawCoframeBoundaryMoment owner lambda
              (suffixActualBandForwardCoframe lambda (p :: S))
              (suffixActualBandForwardEndpointCoframe lambda (p :: S)) ∘L
              (suffixEulerFrameReverseTransition lambda p S)† := hraw
    _ = (primeSchurMarkovScalar p : ℂ) •
          suffixActualBandCompleteBoundaryResponse owner lambda S -
        (suffixEulerFrameTransition lambda p S)† ∘L
          suffixActualBandCompleteBoundaryResponse owner lambda (p :: S) ∘L
            (suffixEulerFrameReverseTransition lambda p S)† := by
      exact congrArg₂
        (fun oldResponse newResponse : SourceOp lambda =>
          (primeSchurMarkovScalar p : ℂ) • oldResponse -
            (suffixEulerFrameTransition lambda p S)† ∘L newResponse ∘L
              (suffixEulerFrameReverseTransition lambda p S)†)
        hS hpS

end CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorAdjacentBoundaryResponse
end CCM25Concrete
end Source
end ConnesWeilRH
