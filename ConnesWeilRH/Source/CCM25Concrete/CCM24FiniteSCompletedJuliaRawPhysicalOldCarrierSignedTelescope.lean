/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierReduction
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawCoframeBoundaryTelescope

/-!
# Old-carrier signed telescope readback

The reduced old-carrier row is the complete signed boundary-moment telescope
evaluated on the old-frame adjoint.  This module names that operator on the
literal old carrier and records its exact response-level readback.

No norm estimate is taken here.  In particular, the two moments stay inside
one signed difference until a source theorem supplies a bounded quotient.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierSignedTelescope

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSProjectionTrace
open CCM24FiniteSCompletedJuliaRawCoframeBoundaryTelescope
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierReduction
open CCM24FiniteSRawCompletedSchurCocycle
open CCM24FiniteSRawLocalTraceFactorization

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! ## The single signed old-carrier object -/

noncomputable def suffixActualBandRawPhysicalOldCarrierSignedTelescope
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    finiteSCarrier →L[ℂ] sourceSoninCarrier lambda :=
  (rawCoframeBoundaryMoment owner lambda
      (suffixActualBandForwardCoframe lambda S)
      (suffixActualBandForwardEndpointCoframe lambda S) ∘L
    (suffixEulerFrameTransition lambda p S)†) ∘L
      ContinuousLinearMap.adjoint
        (suffixEulerFrameSchurStep lambda p S).oldFrame -
    ((suffixEulerFrameTransition lambda p S)† ∘L
      rawCoframeBoundaryMoment owner lambda
        (suffixActualBandForwardCoframe lambda (p :: S))
        (suffixActualBandForwardEndpointCoframe lambda (p :: S))) ∘L
      ContinuousLinearMap.adjoint
        (suffixEulerFrameSchurStep lambda p S).oldFrame

/-! ## Exact source-facing readbacks -/

theorem suffixActualBandRawPhysicalReducedRow_eq_signedTelescope
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandRawPhysicalReducedRow owner lambda p S =
      suffixActualBandRawPhysicalOldCarrierSignedTelescope
        owner lambda p S := by
  rw [suffixActualBandRawPhysicalReducedRow,
    suffixActualBandRawPhysicalFourTermRow_eq_boundaryMoment_telescope]
  apply ContinuousLinearMap.ext
  intro y
  simp only [suffixActualBandRawPhysicalOldCarrierSignedTelescope,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply]

theorem suffixActualBandRawPhysicalReducedRow_eq_rawResponseAdjoint_signedTelescope
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandRawPhysicalReducedRow owner lambda p S =
      ((suffixActualBandRawQuadraticCycledResponse owner lambda S)† ∘L
          (suffixEulerFrameTransition lambda p S)†) ∘L
          ContinuousLinearMap.adjoint
            (suffixEulerFrameSchurStep lambda p S).oldFrame -
        ((suffixEulerFrameTransition lambda p S)† ∘L
          (suffixActualBandRawQuadraticCycledResponse owner lambda (p :: S))†) ∘L
          ContinuousLinearMap.adjoint
    (suffixEulerFrameSchurStep lambda p S).oldFrame := by
  rw [suffixActualBandRawPhysicalReducedRow,
    suffixActualBandRawPhysicalFourTermRow_eq_rawResponse_adjoint_telescope]
  apply ContinuousLinearMap.ext
  intro y
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply]

theorem suffixActualBandRawPhysicalOldCarrierSignedTelescope_comp_oldFrameComplement_eq_zero
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandRawPhysicalOldCarrierSignedTelescope owner lambda p S ∘L
        (ContinuousLinearMap.id ℂ finiteSCarrier -
          (suffixEulerFrameSchurStep lambda p S).oldFrame ∘L
            ContinuousLinearMap.adjoint
              (suffixEulerFrameSchurStep lambda p S).oldFrame) = 0 := by
  rw [suffixActualBandRawPhysicalOldCarrierSignedTelescope]
  apply ContinuousLinearMap.ext
  intro y
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply, map_sub]
  have hframe := (suffixEulerFrameSchurStep lambda p S).oldFrame_isometry
  have hframePoint := congrArg
    (fun T : sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda =>
      T (ContinuousLinearMap.adjoint
        (suffixEulerFrameSchurStep lambda p S).oldFrame y)) hframe
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply] at hframePoint
  rw [hframePoint]
  simp

end CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierSignedTelescope
end CCM25Concrete
end Source
end ConnesWeilRH
