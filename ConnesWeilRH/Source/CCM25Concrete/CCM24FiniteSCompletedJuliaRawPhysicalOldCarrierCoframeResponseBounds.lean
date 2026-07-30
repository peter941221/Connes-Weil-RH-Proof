/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeOrientationLedger

/-!
# Low-level bounds for the old-carrier coframe response

This module isolates the elementary contraction estimates used by the
old-carrier ledger.  The source Sonin carrier gets its local completeness
instance here, so the owner file does not have to elaborate these adjoints
while it is also expanding the signed telescope.

These are bounded-leg facts only.  They do not estimate the signed orientation
row or the survivor residual row, and they do not manufacture a two-channel
Douglas readout.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeResponseBounds

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSFixedQuotientCarrier
open CCM24FiniteSGramResponse
open CCM24FiniteSNormalizedPhysicalResponse
open CCM24FiniteSProjectionTrace
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSActualSchurPhysicalResidualUniformControl
open CCM24FiniteSCausalMarkov
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierLeakageExpansion
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeOrientationLedger

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (frameCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

theorem frameForwardCoframe_norm_le_one
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    ‖frameForwardCoframe lambda S‖ ≤ (1 : ℝ) := by
  have hband : ‖sourceBandProjection lambda‖ ≤ (1 : ℝ) :=
    IsStarProjection.norm_le _ (sourceBandProjection_isStarProjection lambda)
  have hinverse : ‖normalizedFiniteEulerInverseList S‖ ≤ (1 : ℝ) :=
    norm_normalizedFiniteEulerInverseList_le_one S
  have hinclusion : ‖CCM24FiniteSGramResponse.sourceInclusion lambda‖ ≤
      (1 : ℝ) :=
    Submodule.norm_subtypeL_le _
  change ‖(sourceBandProjection lambda ∘L
      normalizedFiniteEulerInverseList S) ∘L
        CCM24FiniteSGramResponse.sourceInclusion lambda‖ ≤ (1 : ℝ)
  calc
    ‖(sourceBandProjection lambda ∘L
        normalizedFiniteEulerInverseList S) ∘L
          CCM24FiniteSGramResponse.sourceInclusion lambda‖ ≤
        ‖sourceBandProjection lambda ∘L
          normalizedFiniteEulerInverseList S‖ *
          ‖CCM24FiniteSGramResponse.sourceInclusion lambda‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (‖sourceBandProjection lambda‖ *
        ‖normalizedFiniteEulerInverseList S‖) *
          ‖CCM24FiniteSGramResponse.sourceInclusion lambda‖ := by
      exact mul_le_mul_of_nonneg_right
        (ContinuousLinearMap.opNorm_comp_le _ _)
        (norm_nonneg _)
    _ ≤ 1 := by
      simpa only [mul_one] using
        (mul_le_mul (mul_le_mul hband hinverse
          (norm_nonneg _) zero_le_one) hinclusion
          (norm_nonneg _) (mul_nonneg zero_le_one zero_le_one))

theorem detectorLeg_norm_le
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    ‖suffixActualBandRawCoframeBoundaryDetectorLeg owner lambda‖ ≤
      ‖detectorOperator owner‖ := by
  have hinclusion : ‖CCM24FiniteSGramResponse.sourceInclusion lambda‖ ≤
      (1 : ℝ) :=
    Submodule.norm_subtypeL_le _
  change ‖detectorOperator owner ∘L
      CCM24FiniteSGramResponse.sourceInclusion lambda‖ ≤
        ‖detectorOperator owner‖
  calc
    ‖detectorOperator owner ∘L
        CCM24FiniteSGramResponse.sourceInclusion lambda‖ ≤
        ‖detectorOperator owner‖ *
          ‖CCM24FiniteSGramResponse.sourceInclusion lambda‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖detectorOperator owner‖ := by
      exact le_trans
        (mul_le_mul_of_nonneg_left hinclusion
          (norm_nonneg (detectorOperator owner)))
        (by simp)

theorem forwardAdjointLeakage_norm_le
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (T : List CCM24VisiblePrime) :
    ‖suffixActualBandRawCoframeBoundaryForwardAdjointLeakage
        owner lambda T‖ ≤ ‖detectorOperator owner‖ := by
  have hleg := detectorLeg_norm_le owner lambda
  have hforward := frameForwardCoframe_norm_le_one lambda T
  have hforwardAdj : ‖(frameForwardCoframe lambda T)†‖ ≤ (1 : ℝ) := by
    calc
      ‖(frameForwardCoframe lambda T)†‖ =
          ‖frameForwardCoframe lambda T‖ :=
        ContinuousLinearMap.adjoint.norm_map _
      _ ≤ 1 := hforward
  change ‖(frameForwardCoframe lambda T)† ∘L
      suffixActualBandRawCoframeBoundaryDetectorLeg owner lambda‖ ≤
        ‖detectorOperator owner‖
  calc
    ‖(frameForwardCoframe lambda T)† ∘L
        suffixActualBandRawCoframeBoundaryDetectorLeg owner lambda‖ ≤
        ‖(frameForwardCoframe lambda T)†‖ *
          ‖suffixActualBandRawCoframeBoundaryDetectorLeg owner lambda‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * ‖detectorOperator owner‖ :=
      mul_le_mul hforwardAdj hleg (norm_nonneg _) zero_le_one
    _ = ‖detectorOperator owner‖ := by simp

-- The final rectangular composition needs a larger deterministic elaboration
-- budget after the source-carrier adjoints are exposed explicitly.
set_option maxHeartbeats 16000000 in
theorem forwardLeakage_norm_le
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (T : List CCM24VisiblePrime) :
    ‖suffixActualBandRawCoframeBoundaryForwardLeakage
        owner lambda T‖ ≤ ‖detectorOperator owner‖ := by
  have hinclusion : ‖CCM24FiniteSGramResponse.sourceInclusion lambda‖ ≤
      (1 : ℝ) :=
    Submodule.norm_subtypeL_le _
  have hinclusionAdj :
      ‖(CCM24FiniteSGramResponse.sourceInclusion lambda)†‖ ≤ (1 : ℝ) := by
    calc
      ‖(CCM24FiniteSGramResponse.sourceInclusion lambda)†‖ =
          ‖CCM24FiniteSGramResponse.sourceInclusion lambda‖ :=
        ContinuousLinearMap.adjoint.norm_map _
      _ ≤ 1 := hinclusion
  have hforward := frameForwardCoframe_norm_le_one lambda T
  have hfirst :
      ‖(CCM24FiniteSGramResponse.sourceInclusion lambda)† ∘L
          detectorOperator owner‖ ≤ ‖detectorOperator owner‖ := by
    calc
      ‖(CCM24FiniteSGramResponse.sourceInclusion lambda)† ∘L
          detectorOperator owner‖ ≤
          ‖(CCM24FiniteSGramResponse.sourceInclusion lambda)†‖ *
            ‖detectorOperator owner‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * ‖detectorOperator owner‖ :=
        mul_le_mul hinclusionAdj (le_refl _) (norm_nonneg _) zero_le_one
      _ = ‖detectorOperator owner‖ := by simp
  change ‖((CCM24FiniteSGramResponse.sourceInclusion lambda)† ∘L
      detectorOperator owner) ∘L frameForwardCoframe lambda T‖ ≤
      ‖detectorOperator owner‖
  calc
    ‖((CCM24FiniteSGramResponse.sourceInclusion lambda)† ∘L
        detectorOperator owner) ∘L frameForwardCoframe lambda T‖ ≤
        ‖(CCM24FiniteSGramResponse.sourceInclusion lambda)† ∘L
          detectorOperator owner‖ * ‖frameForwardCoframe lambda T‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖detectorOperator owner‖ * 1 :=
      mul_le_mul hfirst hforward (norm_nonneg _) (norm_nonneg _)
    _ = ‖detectorOperator owner‖ := by simp

end CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeResponseBounds
end CCM25Concrete
end Source
end ConnesWeilRH
