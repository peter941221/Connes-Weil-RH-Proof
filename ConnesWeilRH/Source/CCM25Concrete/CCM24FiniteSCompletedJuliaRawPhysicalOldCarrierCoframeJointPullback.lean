/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeScalarRightInverse

/-!
# Joint pullback of the old-carrier coframe telescope

The scalar-normalized right inverse does not annihilate the individual hard
boundary row.  The correct object to test is the complete signed telescope.
This file records its exact pullback as one synchronized boundary-moment gap.
No cancellation or estimate is asserted here.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeJointPullback

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSProjectionTrace
open CCM24FiniteSRawLocalTraceFactorization
open CCM24FiniteSCompletedJuliaRawCoframeBoundaryTelescope
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierSignedTelescope
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeOrientationLedger
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeDivideConquer
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeScalarRightInverse
open CCM24FiniteSSchurMarkovPairing

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) :
      CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

local notation "SourceOp" lambda =>
  sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda

/-! The synchronized gap before the scalar pullback. -/

noncomputable def coframeBoundaryMomentGap
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) : SourceOp lambda :=
  rawCoframeBoundaryMoment owner lambda
      (suffixActualBandForwardCoframe lambda S)
      (suffixActualBandForwardEndpointCoframe lambda S) ∘L
      frameTransitionAdjoint lambda p S -
    frameTransitionAdjoint lambda p S ∘L
      rawCoframeBoundaryMoment owner lambda
        (suffixActualBandForwardCoframe lambda (p :: S))
        (suffixActualBandForwardEndpointCoframe lambda (p :: S))

theorem suffixActualBandRawPhysicalOldCarrierSignedTelescope_eq_gap_comp_oldFrameAdjoint
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandRawPhysicalOldCarrierSignedTelescope owner lambda p S =
      coframeBoundaryMomentGap owner lambda p S ∘L
        frameOldFrameAdjoint lambda p S := by
  rw [suffixActualBandRawPhysicalOldCarrierSignedTelescope]
  unfold coframeBoundaryMomentGap
  simp only [frameTransitionAdjoint, frameOldFrameAdjoint]
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply]

/-!
The exact joint range test.  The scalar coefficient is kept outside the
operator gap; this is the same non-unit scalar correction used by the
scalar-normalized right inverse owner.
-/

theorem suffixActualBandRawPhysicalOldCarrierSignedTelescope_comp_scalarNormalizedInverseAdjoint_comp_newFrame_eq
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandRawPhysicalOldCarrierSignedTelescope owner lambda p S ∘L
        (scalarNormalizedPrimeEulerInverse p)† ∘L
          (suffixEulerFrameSchurStep lambda p S).newFrame =
      (primeSchurMarkovScalar p : ℂ)⁻¹ •
        (coframeBoundaryMomentGap owner lambda p S ∘L
          (suffixEulerFrameReverseTransition lambda p S)†) := by
  rw [suffixActualBandRawPhysicalOldCarrierSignedTelescope_eq_gap_comp_oldFrameAdjoint]
  have hrow :=
    oldFrameAdjoint_comp_scalarNormalizedInverseAdjoint_comp_newFrame_eq
      lambda p S
  have hrow' :
      frameOldFrameAdjoint lambda p S ∘L
          (scalarNormalizedPrimeEulerInverse p)† ∘L
            (suffixEulerFrameSchurStep lambda p S).newFrame =
        (primeSchurMarkovScalar p : ℂ)⁻¹ •
          (suffixEulerFrameReverseTransition lambda p S)† := by
    simpa only [frameOldFrameAdjoint] using hrow
  calc
    (coframeBoundaryMomentGap owner lambda p S ∘L
        frameOldFrameAdjoint lambda p S) ∘L
        (scalarNormalizedPrimeEulerInverse p)† ∘L
          (suffixEulerFrameSchurStep lambda p S).newFrame =
      coframeBoundaryMomentGap owner lambda p S ∘L
        (frameOldFrameAdjoint lambda p S ∘L
          (scalarNormalizedPrimeEulerInverse p)† ∘L
            (suffixEulerFrameSchurStep lambda p S).newFrame) := by
      rfl
    _ = coframeBoundaryMomentGap owner lambda p S ∘L
        ((primeSchurMarkovScalar p : ℂ)⁻¹ •
          (suffixEulerFrameReverseTransition lambda p S)†) := by
      rw [hrow']
    _ = (primeSchurMarkovScalar p : ℂ)⁻¹ •
        (coframeBoundaryMomentGap owner lambda p S ∘L
          (suffixEulerFrameReverseTransition lambda p S)†) := by
      apply ContinuousLinearMap.ext
      intro x
      simp only [ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.smul_apply, map_smul]

end CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeJointPullback
end CCM25Concrete
end Source
end ConnesWeilRH
