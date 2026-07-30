/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeJointPullback
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierLeakageExpansion

/-!
# Exact leakage expansion of the synchronized coframe gap

The joint pullback is the adjacent difference of two complete boundary
moments.  This file expands those moments into their endpoint and
forward-coframe leakage channels, while keeping each adjacent difference
signed.  It supplies an exact source-facing normal form; it does not estimate
either difference or discard the transition skew.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeJointGapExpansion

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCompletedJuliaRawCoframeBoundaryTelescope
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierLeakageExpansion
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeJointPullback
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeOrientationLedger
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSProjectionTrace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) :
      CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

local notation "SourceOp" lambda =>
  sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda

/-- The complete synchronized gap is the adjacent difference of the two
endpoint/forward leakage channel sums.  The differences remain grouped so
that a later source estimate can exploit cancellation before taking a norm. -/
theorem coframeBoundaryMomentGap_eq_leakage_channel_telescope
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    coframeBoundaryMomentGap owner lambda p S =
      (suffixActualBandRawCoframeBoundaryAmbientLeakage owner lambda S +
          suffixActualBandRawCoframeBoundaryForwardLeakage owner lambda S) ∘L
          frameTransitionAdjoint lambda p S -
        frameTransitionAdjoint lambda p S ∘L
          (suffixActualBandRawCoframeBoundaryAmbientLeakage owner lambda
              (p :: S) +
            suffixActualBandRawCoframeBoundaryForwardLeakage owner lambda
              (p :: S)) := by
  unfold coframeBoundaryMomentGap
  rw [suffixActualBandRawCoframeBoundaryMoment_eq_leakage_channels,
    suffixActualBandRawCoframeBoundaryMoment_eq_leakage_channels]

/-- The same gap, with the endpoint and forward adjacent differences exposed.
This is only an algebraic regrouping; it is not permission to estimate the two
terms separately. -/
theorem coframeBoundaryMomentGap_eq_ambientGap_add_forwardGap
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    coframeBoundaryMomentGap owner lambda p S =
      (suffixActualBandRawCoframeBoundaryAmbientLeakage owner lambda S ∘L
          frameTransitionAdjoint lambda p S -
        frameTransitionAdjoint lambda p S ∘L
          suffixActualBandRawCoframeBoundaryAmbientLeakage owner lambda
            (p :: S)) +
      (suffixActualBandRawCoframeBoundaryForwardLeakage owner lambda S ∘L
          frameTransitionAdjoint lambda p S -
        frameTransitionAdjoint lambda p S ∘L
          suffixActualBandRawCoframeBoundaryForwardLeakage owner lambda
            (p :: S)) := by
  rw [coframeBoundaryMomentGap_eq_leakage_channel_telescope]
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, map_add]
  abel

end CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeJointGapExpansion
end CCM25Concrete
end Source
end ConnesWeilRH
