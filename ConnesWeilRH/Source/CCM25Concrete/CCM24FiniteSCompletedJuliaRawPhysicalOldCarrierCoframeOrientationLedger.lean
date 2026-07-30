/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeResidual
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSActualSchurPhysicalResidualUniformControl
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSNormalizedPhysicalResponse

/-!
# Orientation ledger for the Bone 1 old-carrier row

The metric-coframe recurrence is stated in the forward adjoint orientation,
while the raw old-carrier telescope uses the opposite placement of the
source transition.  This module keeps that mismatch explicit.

The exact row decomposition proved here is

```text
signed telescope
  = coframe orientation row
    + coframe residual row
    + bounded inclusion/forward row.
```

The last row has a uniform bound `6 * ||detector||`.  The first two rows are
not declared to factor through the physical two-channel analysis column.  The
remaining Bone 1 producer is therefore isolated to those two rows rather than
being hidden by an unsupported recurrence cancellation.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeOrientationLedger

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSActualSchurPhysicalResidualUniformControl
open CCM24FiniteSCompletedJuliaAmbientDefectFactorization
open CCM24FiniteSCompletedJuliaPolarRawReadout
open CCM24FiniteSCompletedJuliaRawCoframeBoundaryTelescope
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeResidual
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierLeakageExpansion
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierReduction
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierSignedTelescope
open CCM24FiniteSProjectionTrace
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSCausalMarkov
open CCM24FiniteSRawLocalTraceFactorization
open CCM24FiniteSSchurPolarTelescoping
open CCM24FiniteSFixedQuotientCarrier
open CCM24FiniteSNormalizedPhysicalResponse

noncomputable abbrev frameCarrier (lambda : CCM24SoninScale) :=
  CCM24FiniteSFrameGramCalculus.sourceSoninCarrier lambda

noncomputable def frameSourceInclusion
    (lambda : CCM24SoninScale) :
    frameCarrier lambda →L[ℂ] finiteSCarrier :=
  CCM24FiniteSGramResponse.sourceInclusion lambda

noncomputable def frameMetricCoframe
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    frameCarrier lambda →L[ℂ] finiteSCarrier :=
  suffixActualBandMetricCoframe lambda S

noncomputable def frameForwardCoframe
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    frameCarrier lambda →L[ℂ] finiteSCarrier :=
  suffixActualBandForwardCoframe lambda S

local notation "sourceInclusion" =>
  frameSourceInclusion

local notation "SourceOp" lambda =>
  frameCarrier lambda →L[ℂ] frameCarrier lambda

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (frameCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

noncomputable def frameTransitionAdjoint
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    frameCarrier lambda →L[ℂ] frameCarrier lambda :=
  ContinuousLinearMap.adjoint (suffixEulerFrameTransition lambda p S)

noncomputable def frameOldFrameAdjoint
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    finiteSCarrier →L[ℂ] frameCarrier lambda :=
  ContinuousLinearMap.adjoint
    (suffixEulerFrameSchurStep lambda p S).oldFrame

/-! ## Boundary-leg decomposition -/

/-- The common source-to-ambient detector leg in the endpoint leakage. -/
noncomputable def suffixActualBandRawCoframeBoundaryDetectorLeg
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
  frameCarrier lambda →L[ℂ] finiteSCarrier :=
  detectorOperator owner ∘L sourceInclusion lambda

/-- The metric-coframe contribution to the endpoint leakage. -/
noncomputable def suffixActualBandRawCoframeBoundaryMetricLeakage
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) : SourceOp lambda :=
  (frameMetricCoframe lambda S - sourceInclusion lambda)† ∘L
    suffixActualBandRawCoframeBoundaryDetectorLeg owner lambda

/-- The forward-coframe contribution to the adjoint endpoint leakage. -/
noncomputable def suffixActualBandRawCoframeBoundaryForwardAdjointLeakage
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) : SourceOp lambda :=
  (frameForwardCoframe lambda S)† ∘L
    suffixActualBandRawCoframeBoundaryDetectorLeg owner lambda

theorem suffixActualBandRawCoframeBoundaryAmbientLeakage_eq_metric_add_forwardAdjoint
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    suffixActualBandRawCoframeBoundaryAmbientLeakage owner lambda S =
      suffixActualBandRawCoframeBoundaryMetricLeakage owner lambda S +
        suffixActualBandRawCoframeBoundaryForwardAdjointLeakage
          owner lambda S := by
  have hadjointAdd
      (A B : frameCarrier lambda →L[ℂ] finiteSCarrier) :
      (A + B)† = A† + B† :=
    ContinuousLinearMap.adjoint.map_add _ _
  have hadjointSub
      (A B : frameCarrier lambda →L[ℂ] finiteSCarrier) :
      (A - B)† = A† - B† :=
    ContinuousLinearMap.adjoint.map_sub _ _
  have hmetricSub :
      (frameMetricCoframe lambda S - sourceInclusion lambda)† =
        (frameMetricCoframe lambda S)† - (sourceInclusion lambda)† :=
    hadjointSub _ _
  rw [suffixActualBandRawCoframeBoundaryAmbientLeakage,
    suffixActualBandRawCoframeBoundaryMetricLeakage,
    suffixActualBandRawCoframeBoundaryForwardAdjointLeakage,
    suffixActualBandForwardEndpointCoframe, hadjointSub, hadjointAdd,
    hmetricSub]
  apply ContinuousLinearMap.ext
  intro x
  simp [frameMetricCoframe, frameForwardCoframe, frameSourceInclusion,
    suffixActualBandRawCoframeBoundaryDetectorLeg,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.add_apply]
  abel

/-! ## The three exact old-carrier pieces -/

noncomputable def suffixActualBandRawPhysicalOldCarrierMetricLeakageTelescope
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    finiteSCarrier →L[ℂ] frameCarrier lambda :=
  suffixActualBandRawCoframeBoundaryMetricLeakage owner lambda S ∘L
      frameTransitionAdjoint lambda p S ∘L
        frameOldFrameAdjoint lambda p S -
    (frameTransitionAdjoint lambda p S ∘L
      suffixActualBandRawCoframeBoundaryMetricLeakage owner lambda (p :: S)) ∘L
      frameOldFrameAdjoint lambda p S

noncomputable def suffixActualBandRawPhysicalOldCarrierForwardAdjointLeakageTelescope
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    finiteSCarrier →L[ℂ] frameCarrier lambda :=
  suffixActualBandRawCoframeBoundaryForwardAdjointLeakage owner lambda S ∘L
      frameTransitionAdjoint lambda p S ∘L
        frameOldFrameAdjoint lambda p S -
    (frameTransitionAdjoint lambda p S ∘L
      suffixActualBandRawCoframeBoundaryForwardAdjointLeakage
        owner lambda (p :: S)) ∘L
      frameOldFrameAdjoint lambda p S

noncomputable def suffixActualBandRawPhysicalOldCarrierForwardCompleteLeakageTelescope
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    finiteSCarrier →L[ℂ] frameCarrier lambda :=
  suffixActualBandRawPhysicalOldCarrierForwardAdjointLeakageTelescope
      owner lambda p S +
    suffixActualBandRawPhysicalOldCarrierForwardLeakageTelescope
      owner lambda p S

theorem suffixActualBandRawPhysicalOldCarrierAmbientLeakageTelescope_eq_metric_add_forwardAdjoint
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandRawPhysicalOldCarrierAmbientLeakageTelescope
        owner lambda p S =
      suffixActualBandRawPhysicalOldCarrierMetricLeakageTelescope
          owner lambda p S +
        suffixActualBandRawPhysicalOldCarrierForwardAdjointLeakageTelescope
          owner lambda p S := by
  rw [suffixActualBandRawPhysicalOldCarrierAmbientLeakageTelescope,
    suffixActualBandRawPhysicalOldCarrierMetricLeakageTelescope,
    suffixActualBandRawPhysicalOldCarrierForwardAdjointLeakageTelescope,
    suffixActualBandRawCoframeBoundaryAmbientLeakage_eq_metric_add_forwardAdjoint,
    suffixActualBandRawCoframeBoundaryAmbientLeakage_eq_metric_add_forwardAdjoint]
  apply ContinuousLinearMap.ext
  intro y
  dsimp [frameTransitionAdjoint, frameOldFrameAdjoint]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.add_apply, map_add, frameTransitionAdjoint,
    frameOldFrameAdjoint]
  abel

theorem suffixActualBandRawPhysicalOldCarrierSignedTelescope_eq_metric_add_forwardComplete
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandRawPhysicalOldCarrierSignedTelescope owner lambda p S =
      suffixActualBandRawPhysicalOldCarrierMetricLeakageTelescope
          owner lambda p S +
        suffixActualBandRawPhysicalOldCarrierForwardCompleteLeakageTelescope
          owner lambda p S := by
  rw [suffixActualBandRawPhysicalOldCarrierSignedTelescope_eq_leakage_telescopes,
    suffixActualBandRawPhysicalOldCarrierAmbientLeakageTelescope_eq_metric_add_forwardAdjoint]
  apply ContinuousLinearMap.ext
  intro y
  simp only [suffixActualBandRawPhysicalOldCarrierForwardCompleteLeakageTelescope,
    ContinuousLinearMap.add_apply]
  abel

/-! ## The recurrence orientation and its exact residual readback -/

/-- The adjoint-oriented coframe gap which is actually seen by the raw row. -/
noncomputable def suffixActualBandMetricCoframeAdjointOrientationGap
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    finiteSCarrier →L[ℂ] frameCarrier lambda :=
  (frameMetricCoframe lambda (p :: S) -
      frameMetricCoframe lambda S ∘L
        frameTransitionAdjoint lambda p S)†

theorem suffixActualBandMetricCoframeAdjointOrientationGap_eq_expanded
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandMetricCoframeAdjointOrientationGap lambda p S =
      (frameMetricCoframe lambda (p :: S))† -
        (suffixEulerFrameTransition lambda p S) ∘L
          (frameMetricCoframe lambda S)† := by
  have hadjointSub
      (A B : frameCarrier lambda →L[ℂ] finiteSCarrier) :
      (A - B)† = A† - B† :=
    ContinuousLinearMap.adjoint.map_sub _ _
  unfold suffixActualBandMetricCoframeAdjointOrientationGap
  rw [hadjointSub, ContinuousLinearMap.adjoint_comp]
  simp only [frameTransitionAdjoint, ContinuousLinearMap.adjoint_adjoint]

theorem suffixActualBandMetricCoframeAdjointOrientationGap_eq_residualAdjoint_comp_ambientProduct
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandMetricCoframeAdjointOrientationGap lambda p S =
      (suffixActualBandMetricCoframeSurvivorResidual lambda p S +
          suffixActualBandMetricCoframeBoundaryResidual lambda p S)† ∘L
        suffixEulerAmbientProduct S := by
  unfold suffixActualBandMetricCoframeAdjointOrientationGap
    frameMetricCoframe frameTransitionAdjoint
  rw [suffixActualBandMetricCoframe_cons_sub_comp_transitionAdj_eq_ambientAdjoint_comp_residual]
  simp only [ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint]

/-! ## The exact orientation split of the metric telescope -/

noncomputable def suffixActualBandRawPhysicalOldCarrierMetricOrientationRow
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    finiteSCarrier →L[ℂ] frameCarrier lambda :=
  let detectorLeg : frameCarrier lambda →L[ℂ] finiteSCarrier :=
    suffixActualBandRawCoframeBoundaryDetectorLeg owner lambda
  let left : frameCarrier lambda →L[ℂ] frameCarrier lambda :=
    (frameMetricCoframe lambda S)† ∘L detectorLeg ∘L
      frameTransitionAdjoint lambda p S
  let right : frameCarrier lambda →L[ℂ] frameCarrier lambda :=
    frameTransitionAdjoint lambda p S ∘L
      suffixEulerFrameTransition lambda p S ∘L
        (frameMetricCoframe lambda S)† ∘L detectorLeg
  (left - right) ∘L (frameOldFrameAdjoint lambda p S)

noncomputable def suffixActualBandRawPhysicalOldCarrierMetricResidualRow
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    finiteSCarrier →L[ℂ] frameCarrier lambda :=
  let detectorLeg : frameCarrier lambda →L[ℂ] finiteSCarrier :=
    suffixActualBandRawCoframeBoundaryDetectorLeg owner lambda
  let row : frameCarrier lambda →L[ℂ] frameCarrier lambda :=
    frameTransitionAdjoint lambda p S ∘L
      suffixActualBandMetricCoframeAdjointOrientationGap lambda p S ∘L
        detectorLeg
  (-row) ∘L (frameOldFrameAdjoint lambda p S)

noncomputable def suffixActualBandRawPhysicalOldCarrierMetricInclusionRow
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    finiteSCarrier →L[ℂ] frameCarrier lambda :=
  let detectorLeg : frameCarrier lambda →L[ℂ] finiteSCarrier :=
    suffixActualBandRawCoframeBoundaryDetectorLeg owner lambda
  let inclusion : frameCarrier lambda →L[ℂ] finiteSCarrier :=
    sourceInclusion lambda
  let left : frameCarrier lambda →L[ℂ] frameCarrier lambda :=
    (inclusion)† ∘L detectorLeg ∘L frameTransitionAdjoint lambda p S
  let right : frameCarrier lambda →L[ℂ] frameCarrier lambda :=
    frameTransitionAdjoint lambda p S ∘L (inclusion)† ∘L detectorLeg
  (-left) ∘L (frameOldFrameAdjoint lambda p S) +
    right ∘L (frameOldFrameAdjoint lambda p S)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem suffixActualBandRawPhysicalOldCarrierMetricLeakageTelescope_eq_orientation_add_residual_add_inclusion
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandRawPhysicalOldCarrierMetricLeakageTelescope
        owner lambda p S =
      suffixActualBandRawPhysicalOldCarrierMetricOrientationRow
          owner lambda p S +
        suffixActualBandRawPhysicalOldCarrierMetricResidualRow
          owner lambda p S +
        suffixActualBandRawPhysicalOldCarrierMetricInclusionRow
          owner lambda p S := by
  have hadjointSub
      (A B : frameCarrier lambda →L[ℂ] finiteSCarrier) :
      (A - B)† = A† - B† :=
    ContinuousLinearMap.adjoint.map_sub _ _
  rw [suffixActualBandRawPhysicalOldCarrierMetricLeakageTelescope,
    suffixActualBandRawPhysicalOldCarrierMetricOrientationRow,
    suffixActualBandRawPhysicalOldCarrierMetricResidualRow,
    suffixActualBandRawPhysicalOldCarrierMetricInclusionRow,
    suffixActualBandRawCoframeBoundaryMetricLeakage,
    suffixActualBandRawCoframeBoundaryMetricLeakage, hadjointSub, hadjointSub,
    suffixActualBandMetricCoframeAdjointOrientationGap_eq_expanded]
  apply ContinuousLinearMap.ext
  intro y
  simp only [suffixActualBandRawCoframeBoundaryDetectorLeg,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.neg_apply, map_sub]
  abel

/-! ## The commutator source compression vanishes -/

/-- The fixed Sonin projection kills the commutator after source compression.
This is the exact cancellation supplied by the projection identities; the raw
detector leg remains `detectorOperator ∘ sourceInclusion` and is not silently
replaced by this commutator. -/
theorem suffixActualBandRawCoframeBoundaryDetectorLeg_commutator_sourceCompression_eq_zero
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    (sourceInclusion lambda)† ∘L
        cc20Commutator (sourceSoninProjection lambda) (detectorOperator owner) ∘L
          sourceInclusion lambda = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  have hleft := congrArg
    (fun operator : finiteSCarrier →L[ℂ] frameCarrier lambda =>
      operator (detectorOperator owner (sourceInclusion lambda x)))
    (CCM24FiniteSGramResponse.sourceInclusionAdjoint_comp_sourceProjection
      lambda)
  have hright := congrArg
    (fun operator : frameCarrier lambda →L[ℂ] finiteSCarrier =>
      detectorOperator owner (operator x))
    (CCM24FiniteSActualBandQuadraticCycle.sourceSoninProjection_comp_sourceInclusion_eq_self
      lambda)
  simp only [cc20Commutator, frameSourceInclusion,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply] at hleft hright ⊢
  rw [map_sub, hleft, hright]
  simp

theorem suffixActualBandRawPhysicalOldCarrierMetricResidualRow_eq_residual_readback
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandRawPhysicalOldCarrierMetricResidualRow
        owner lambda p S =
      -frameTransitionAdjoint lambda p S ∘L
        (suffixActualBandMetricCoframeSurvivorResidual lambda p S +
          suffixActualBandMetricCoframeBoundaryResidual lambda p S)† ∘L
        suffixEulerAmbientProduct S ∘L
          suffixActualBandRawCoframeBoundaryDetectorLeg owner lambda ∘L
            frameOldFrameAdjoint lambda p S := by
  dsimp [suffixActualBandRawPhysicalOldCarrierMetricResidualRow,
    frameTransitionAdjoint, frameOldFrameAdjoint]
  rw [suffixActualBandMetricCoframeAdjointOrientationGap_eq_residualAdjoint_comp_ambientProduct]
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply]

theorem suffixActualBandRawPhysicalOldCarrierSignedTelescope_eq_orientation_add_residual_add_forwardComplete
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandRawPhysicalOldCarrierSignedTelescope owner lambda p S =
      suffixActualBandRawPhysicalOldCarrierMetricOrientationRow
          owner lambda p S +
        suffixActualBandRawPhysicalOldCarrierMetricResidualRow
          owner lambda p S +
        suffixActualBandRawPhysicalOldCarrierMetricInclusionRow
          owner lambda p S +
        suffixActualBandRawPhysicalOldCarrierForwardCompleteLeakageTelescope
          owner lambda p S := by
  rw [suffixActualBandRawPhysicalOldCarrierSignedTelescope_eq_metric_add_forwardComplete,
    suffixActualBandRawPhysicalOldCarrierMetricLeakageTelescope_eq_orientation_add_residual_add_inclusion]

/- ## Uniformly bounded pieces

set_option maxHeartbeats 16000000 in
theorem suffixActualBandForwardCoframe_norm_le_one
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    ‖frameForwardCoframe lambda S‖ ≤ (1 : ℝ) := by
  have hband : ‖sourceBandProjection lambda‖ ≤ (1 : ℝ) :=
    IsStarProjection.norm_le _ (sourceBandProjection_isStarProjection lambda)
  have hinverse : ‖normalizedFiniteEulerInverseList S‖ ≤ (1 : ℝ) :=
    norm_normalizedFiniteEulerInverseList_le_one S
  have hinclusion : ‖sourceInclusion lambda‖ ≤ (1 : ℝ) :=
    Submodule.norm_subtypeL_le _
  unfold frameForwardCoframe
  calc
    ‖(sourceBandProjection lambda ∘L
        normalizedFiniteEulerInverseList S) ∘L sourceInclusion lambda‖ ≤
        ‖sourceBandProjection lambda ∘L
          normalizedFiniteEulerInverseList S‖ *
          ‖sourceInclusion lambda‖ :=
      ContinuousLinearMap.opNorm_comp_le
        (sourceBandProjection lambda ∘L normalizedFiniteEulerInverseList S)
        (sourceInclusion lambda)
    _ ≤ (‖sourceBandProjection lambda‖ *
        ‖normalizedFiniteEulerInverseList S‖) *
          ‖sourceInclusion lambda‖ := by
      exact mul_le_mul_of_nonneg_right
        (ContinuousLinearMap.opNorm_comp_le
          (sourceBandProjection lambda)
          (normalizedFiniteEulerInverseList S))
        (norm_nonneg _)
    _ ≤ 1 := by
      have hprod :
          (‖sourceBandProjection lambda‖ *
            ‖normalizedFiniteEulerInverseList S‖) *
              ‖sourceInclusion lambda‖ ≤ (1 : ℝ) := by
        exact mul_le_mul (mul_le_mul hband hinverse
          (norm_nonneg _) zero_le_one) hinclusion
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
          (mul_nonneg zero_le_one zero_le_one)
      exact hprod

set_option maxHeartbeats 64000000 in
theorem suffixActualBandRawCoframeBoundaryDetectorLeg_norm_le
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    ‖suffixActualBandRawCoframeBoundaryDetectorLeg owner lambda‖ ≤
      ‖detectorOperator owner‖ := by
  have hinclusion : ‖sourceInclusion lambda‖ ≤ (1 : ℝ) :=
    Submodule.norm_subtypeL_le _
  unfold suffixActualBandRawCoframeBoundaryDetectorLeg
  calc
    ‖detectorOperator owner ∘L sourceInclusion lambda‖ ≤
        ‖detectorOperator owner‖ * ‖sourceInclusion lambda‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖detectorOperator owner‖ := by
      exact le_trans
        (mul_le_mul_of_nonneg_left hinclusion
          (norm_nonneg (detectorOperator owner)))
        (by simp)

set_option maxHeartbeats 64000000 in
theorem suffixActualBandRawPhysicalOldCarrierMetricInclusionRow_norm_le
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    ‖suffixActualBandRawPhysicalOldCarrierMetricInclusionRow
        owner lambda p S‖ ≤ 2 * ‖detectorOperator owner‖ := by
  have hleg := suffixActualBandRawCoframeBoundaryDetectorLeg_norm_le owner lambda
  have hT : ‖suffixEulerFrameTransition lambda p S‖ ≤ (1 : ℝ) :=
    suffixEulerFrameTransition_norm_le_one lambda p S
  have hTAdj : ‖frameTransitionAdjoint lambda p S‖ ≤ (1 : ℝ) := by
    calc
      ‖frameTransitionAdjoint lambda p S‖ =
          ‖suffixEulerFrameTransition lambda p S‖ :=
        ContinuousLinearMap.adjoint.norm_map _
      _ ≤ 1 := hT
  have hlegAdj : ‖(suffixActualBandRawCoframeBoundaryDetectorLeg owner lambda)†‖ ≤
      ‖detectorOperator owner‖ := by
    calc
      ‖(suffixActualBandRawCoframeBoundaryDetectorLeg owner lambda)†‖ =
          ‖suffixActualBandRawCoframeBoundaryDetectorLeg owner lambda‖ :=
        ContinuousLinearMap.adjoint.norm_map _
      _ ≤ ‖detectorOperator owner‖ := hleg
  unfold suffixActualBandRawPhysicalOldCarrierMetricInclusionRow
  calc
    ‖-((suffixActualBandRawCoframeBoundaryDetectorLeg owner lambda)† ∘L
          frameTransitionAdjoint lambda p S) +
        frameTransitionAdjoint lambda p S ∘L
          (suffixActualBandRawCoframeBoundaryDetectorLeg owner lambda)†‖ ≤
        ‖(suffixActualBandRawCoframeBoundaryDetectorLeg owner lambda)† ∘L
            frameTransitionAdjoint lambda p S‖ +
          ‖frameTransitionAdjoint lambda p S ∘L
            (suffixActualBandRawCoframeBoundaryDetectorLeg owner lambda)†‖ := by
      exact norm_add_le _ _
    _ ≤ ‖detectorOperator owner‖ * 1 +
          1 * ‖detectorOperator owner‖ := by
      exact add_le_add
        (le_trans (ContinuousLinearMap.opNorm_comp_le _ _)
          (mul_le_mul hlegAdj hTAdj (norm_nonneg _)
            (norm_nonneg _)))
        (le_trans (ContinuousLinearMap.opNorm_comp_le _ _)
          (mul_le_mul hTAdj hlegAdj (norm_nonneg _) zero_le_one))
    _ = 2 * ‖detectorOperator owner‖ := by ring

set_option maxHeartbeats 64000000 in
theorem suffixActualBandRawPhysicalOldCarrierForwardCompleteLeakageTelescope_norm_le
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    ‖suffixActualBandRawPhysicalOldCarrierForwardCompleteLeakageTelescope
        owner lambda p S‖ ≤ 4 * ‖detectorOperator owner‖ := by
  have hleg := suffixActualBandRawCoframeBoundaryDetectorLeg_norm_le owner lambda
  have hF0 := suffixActualBandForwardCoframe_norm_le_one lambda S
  have hF1 := suffixActualBandForwardCoframe_norm_le_one lambda (p :: S)
  have hJ : ‖sourceInclusion lambda‖ ≤ (1 : ℝ) :=
    Submodule.norm_subtypeL_le _
  have hJAdj : ‖(sourceInclusion lambda)†‖ ≤ (1 : ℝ) := by
    calc
      ‖(sourceInclusion lambda)†‖ = ‖sourceInclusion lambda‖ :=
        ContinuousLinearMap.adjoint.norm_map _
      _ ≤ 1 := hJ
  have hT : ‖suffixEulerFrameTransition lambda p S‖ ≤ (1 : ℝ) :=
    suffixEulerFrameTransition_norm_le_one lambda p S
  have hTAdj : ‖frameTransitionAdjoint lambda p S‖ ≤ (1 : ℝ) := by
    calc
      ‖frameTransitionAdjoint lambda p S‖ =
          ‖suffixEulerFrameTransition lambda p S‖ :=
        ContinuousLinearMap.adjoint.norm_map _
      _ ≤ 1 := hT
  have hold : ‖(suffixEulerFrameSchurStep lambda p S).oldFrame‖ ≤ (1 : ℝ) := by
    simpa only [suffixEulerFrameSchurStep, oldSuffixFrame] using
      (newSuffixFrame_norm_le_one lambda (p :: S))
  have holdAdj : ‖frameOldFrameAdjoint lambda p S‖ ≤ (1 : ℝ) := by
    calc
      ‖frameOldFrameAdjoint lambda p S‖ =
          ‖(suffixEulerFrameSchurStep lambda p S).oldFrame‖ :=
        ContinuousLinearMap.adjoint.norm_map _
      _ ≤ 1 := hold
  have hforwardAdj0 :
      ‖suffixActualBandRawCoframeBoundaryForwardAdjointLeakage owner lambda S‖ ≤
        ‖detectorOperator owner‖ := by
    unfold suffixActualBandRawCoframeBoundaryForwardAdjointLeakage
    calc
      ‖(frameForwardCoframe lambda S)† ∘L
          suffixActualBandRawCoframeBoundaryDetectorLeg owner lambda‖ ≤
          ‖(frameForwardCoframe lambda S)†‖ *
            ‖suffixActualBandRawCoframeBoundaryDetectorLeg owner lambda‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖detectorOperator owner‖ := by
        have hFAdj : ‖(frameForwardCoframe lambda S)†‖ ≤ 1 := by
          calc
            ‖(frameForwardCoframe lambda S)†‖ =
                ‖frameForwardCoframe lambda S‖ :=
              ContinuousLinearMap.adjoint.norm_map _
            _ ≤ 1 := hF0
        exact le_trans
          (mul_le_mul hFAdj hleg
            (norm_nonneg
              (suffixActualBandRawCoframeBoundaryDetectorLeg owner lambda))
            zero_le_one)
          (by simpa using (mul_one (‖detectorOperator owner‖)))
  have hforwardAdj1 :
      ‖suffixActualBandRawCoframeBoundaryForwardAdjointLeakage
          owner lambda (p :: S)‖ ≤ ‖detectorOperator owner‖ := by
    unfold suffixActualBandRawCoframeBoundaryForwardAdjointLeakage
    calc
      ‖(frameForwardCoframe lambda (p :: S))† ∘L
          suffixActualBandRawCoframeBoundaryDetectorLeg owner lambda‖ ≤
          ‖(frameForwardCoframe lambda (p :: S))†‖ *
            ‖suffixActualBandRawCoframeBoundaryDetectorLeg owner lambda‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖detectorOperator owner‖ := by
        have hFAdj : ‖(frameForwardCoframe lambda (p :: S))†‖ ≤ 1 := by
          calc
            ‖(frameForwardCoframe lambda (p :: S))†‖ =
                ‖frameForwardCoframe lambda (p :: S)‖ :=
              ContinuousLinearMap.adjoint.norm_map _
            _ ≤ 1 := hF1
        exact le_trans
          (mul_le_mul hFAdj hleg
            (norm_nonneg
              (suffixActualBandRawCoframeBoundaryDetectorLeg owner lambda))
            zero_le_one)
          (by simpa using (mul_one (‖detectorOperator owner‖)))
  have hforward0 :
      ‖suffixActualBandRawCoframeBoundaryForwardLeakage owner lambda S‖ ≤
        ‖detectorOperator owner‖ := by
    unfold suffixActualBandRawCoframeBoundaryForwardLeakage
    calc
      ‖(sourceInclusion lambda)† ∘L detectorOperator owner ∘L
          frameForwardCoframe lambda S‖ ≤
          ‖(sourceInclusion lambda)† ∘L detectorOperator owner‖ *
          ‖frameForwardCoframe lambda S‖ :=
        ContinuousLinearMap.opNorm_comp_le
          ((sourceInclusion lambda)† ∘L detectorOperator owner)
          (frameForwardCoframe lambda S)
      _ ≤ ‖detectorOperator owner‖ := by
        have hfirst : ‖(sourceInclusion lambda)† ∘L detectorOperator owner‖ ≤
            ‖detectorOperator owner‖ := by
          calc
            ‖(sourceInclusion lambda)† ∘L detectorOperator owner‖ ≤
                ‖(sourceInclusion lambda)†‖ * ‖detectorOperator owner‖ :=
              ContinuousLinearMap.opNorm_comp_le _ _
            _ ≤ ‖detectorOperator owner‖ := by
              exact le_trans
                (mul_le_mul hJAdj (le_refl _) (norm_nonneg _)
                  (norm_nonneg _))
                (by simpa using (one_mul (‖detectorOperator owner‖)))
        exact le_trans
          (mul_le_mul hfirst hF0 (norm_nonneg _)
            (norm_nonneg _))
          (by simpa using (mul_one (‖detectorOperator owner‖)))
  have hforward1 :
      ‖suffixActualBandRawCoframeBoundaryForwardLeakage owner lambda (p :: S)‖ ≤
        ‖detectorOperator owner‖ := by
    unfold suffixActualBandRawCoframeBoundaryForwardLeakage
    calc
      ‖(sourceInclusion lambda)† ∘L detectorOperator owner ∘L
          frameForwardCoframe lambda (p :: S)‖ ≤
          ‖(sourceInclusion lambda)† ∘L detectorOperator owner‖ *
          ‖frameForwardCoframe lambda (p :: S)‖ :=
        ContinuousLinearMap.opNorm_comp_le
          ((sourceInclusion lambda)† ∘L detectorOperator owner)
          (frameForwardCoframe lambda (p :: S))
      _ ≤ ‖detectorOperator owner‖ := by
        have hfirst : ‖(sourceInclusion lambda)† ∘L detectorOperator owner‖ ≤
            ‖detectorOperator owner‖ := by
          calc
            ‖(sourceInclusion lambda)† ∘L detectorOperator owner‖ ≤
                ‖(sourceInclusion lambda)†‖ * ‖detectorOperator owner‖ :=
              ContinuousLinearMap.opNorm_comp_le _ _
            _ ≤ ‖detectorOperator owner‖ := by
              exact le_trans
                (mul_le_mul hJAdj (le_refl _) (norm_nonneg _)
                  (norm_nonneg _))
                (by simpa using (one_mul (‖detectorOperator owner‖)))
        exact le_trans
          (mul_le_mul hfirst hF1 (norm_nonneg _)
            (norm_nonneg _))
          (by simpa using (mul_one (‖detectorOperator owner‖)))
  have hAdjTelescope :
      ‖suffixActualBandRawPhysicalOldCarrierForwardAdjointLeakageTelescope
          owner lambda p S‖ ≤ 2 * ‖detectorOperator owner‖ := by
    unfold suffixActualBandRawPhysicalOldCarrierForwardAdjointLeakageTelescope
    have hfirst :
        ‖suffixActualBandRawCoframeBoundaryForwardAdjointLeakage
            owner lambda S ∘L frameTransitionAdjoint lambda p S ∘L
              frameOldFrameAdjoint lambda p S‖ ≤
          ‖detectorOperator owner‖ * 1 * 1 := by
      calc
        ‖suffixActualBandRawCoframeBoundaryForwardAdjointLeakage
              owner lambda S ∘L frameTransitionAdjoint lambda p S ∘L
                frameOldFrameAdjoint lambda p S‖ ≤
            ‖suffixActualBandRawCoframeBoundaryForwardAdjointLeakage
                owner lambda S ∘L frameTransitionAdjoint lambda p S‖ *
              ‖frameOldFrameAdjoint lambda p S‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ (‖suffixActualBandRawCoframeBoundaryForwardAdjointLeakage
                owner lambda S‖ * ‖frameTransitionAdjoint lambda p S‖) *
              ‖frameOldFrameAdjoint lambda p S‖ := by
          exact mul_le_mul
            (ContinuousLinearMap.opNorm_comp_le _ _)
            (le_refl _)
            (norm_nonneg _)
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        _ ≤ ‖detectorOperator owner‖ * 1 * 1 := by
          exact mul_le_mul
            (mul_le_mul hforwardAdj0 hTAdj (norm_nonneg _)
              (norm_nonneg _))
            holdAdj
            (norm_nonneg _)
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    have hsecond :
        ‖frameTransitionAdjoint lambda p S ∘L
            suffixActualBandRawCoframeBoundaryForwardAdjointLeakage
              owner lambda (p :: S) ∘L frameOldFrameAdjoint lambda p S‖ ≤
          1 * ‖detectorOperator owner‖ * 1 := by
      calc
        ‖frameTransitionAdjoint lambda p S ∘L
              suffixActualBandRawCoframeBoundaryForwardAdjointLeakage
                owner lambda (p :: S) ∘L
              frameOldFrameAdjoint lambda p S‖ ≤
            ‖frameTransitionAdjoint lambda p S ∘L
                suffixActualBandRawCoframeBoundaryForwardAdjointLeakage
                  owner lambda (p :: S)‖ *
              ‖frameOldFrameAdjoint lambda p S‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ (‖frameTransitionAdjoint lambda p S‖ *
              ‖suffixActualBandRawCoframeBoundaryForwardAdjointLeakage
                owner lambda (p :: S)‖) *
              ‖frameOldFrameAdjoint lambda p S‖ := by
          exact mul_le_mul
            (ContinuousLinearMap.opNorm_comp_le _ _)
            (le_refl _)
            (norm_nonneg _)
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        _ ≤ 1 * ‖detectorOperator owner‖ * 1 := by
          exact mul_le_mul
            (mul_le_mul hTAdj hforwardAdj1 (norm_nonneg _)
              zero_le_one)
            holdAdj
            (norm_nonneg _)
            (mul_nonneg zero_le_one (norm_nonneg _))
    calc
      ‖suffixActualBandRawCoframeBoundaryForwardAdjointLeakage owner lambda S ∘L
            frameTransitionAdjoint lambda p S ∘L
              frameOldFrameAdjoint lambda p S -
          (frameTransitionAdjoint lambda p S ∘L
            suffixActualBandRawCoframeBoundaryForwardAdjointLeakage
              owner lambda (p :: S)) ∘L
            frameOldFrameAdjoint lambda p S‖ ≤
        ‖suffixActualBandRawCoframeBoundaryForwardAdjointLeakage owner lambda S ∘L
            frameTransitionAdjoint lambda p S ∘L
              frameOldFrameAdjoint lambda p S‖ +
        ‖(frameTransitionAdjoint lambda p S ∘L
            suffixActualBandRawCoframeBoundaryForwardAdjointLeakage
              owner lambda (p :: S)) ∘L
            frameOldFrameAdjoint lambda p S‖ :=
        norm_sub_le _ _
      _ ≤ ‖detectorOperator owner‖ * 1 * 1 +
          1 * ‖detectorOperator owner‖ * 1 := by
        exact add_le_add hfirst hsecond
      _ = 2 * ‖detectorOperator owner‖ := by ring
  have hForwardTelescope :
      ‖suffixActualBandRawPhysicalOldCarrierForwardLeakageTelescope
          owner lambda p S‖ ≤ 2 * ‖detectorOperator owner‖ := by
    unfold suffixActualBandRawPhysicalOldCarrierForwardLeakageTelescope
    have hfirst :
        ‖suffixActualBandRawCoframeBoundaryForwardLeakage owner lambda S ∘L
            frameTransitionAdjoint lambda p S ∘L
              frameOldFrameAdjoint lambda p S‖ ≤
          ‖detectorOperator owner‖ * 1 * 1 := by
      calc
        ‖suffixActualBandRawCoframeBoundaryForwardLeakage owner lambda S ∘L
              frameTransitionAdjoint lambda p S ∘L
                frameOldFrameAdjoint lambda p S‖ ≤
            ‖suffixActualBandRawCoframeBoundaryForwardLeakage owner lambda S ∘L
                frameTransitionAdjoint lambda p S‖ *
              ‖frameOldFrameAdjoint lambda p S‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ (‖suffixActualBandRawCoframeBoundaryForwardLeakage
                owner lambda S‖ * ‖frameTransitionAdjoint lambda p S‖) *
              ‖frameOldFrameAdjoint lambda p S‖ := by
          exact mul_le_mul
            (ContinuousLinearMap.opNorm_comp_le _ _)
            (le_refl _)
            (norm_nonneg _)
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        _ ≤ ‖detectorOperator owner‖ * 1 * 1 := by
          exact mul_le_mul
            (mul_le_mul hforward0 hTAdj (norm_nonneg _)
              (norm_nonneg _))
            holdAdj
            (norm_nonneg _)
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    have hsecond :
        ‖frameTransitionAdjoint lambda p S ∘L
            suffixActualBandRawCoframeBoundaryForwardLeakage
              owner lambda (p :: S) ∘L frameOldFrameAdjoint lambda p S‖ ≤
          1 * ‖detectorOperator owner‖ * 1 := by
      calc
        ‖frameTransitionAdjoint lambda p S ∘L
              suffixActualBandRawCoframeBoundaryForwardLeakage
                owner lambda (p :: S) ∘L
              frameOldFrameAdjoint lambda p S‖ ≤
            ‖frameTransitionAdjoint lambda p S ∘L
                suffixActualBandRawCoframeBoundaryForwardLeakage
                  owner lambda (p :: S)‖ *
              ‖frameOldFrameAdjoint lambda p S‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ (‖frameTransitionAdjoint lambda p S‖ *
              ‖suffixActualBandRawCoframeBoundaryForwardLeakage
                owner lambda (p :: S)‖) *
              ‖frameOldFrameAdjoint lambda p S‖ := by
          exact mul_le_mul
            (ContinuousLinearMap.opNorm_comp_le _ _)
            (le_refl _)
            (norm_nonneg _)
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        _ ≤ 1 * ‖detectorOperator owner‖ * 1 := by
          exact mul_le_mul
            (mul_le_mul hTAdj hforward1 (norm_nonneg _)
              zero_le_one)
            holdAdj
            (norm_nonneg _)
            (mul_nonneg zero_le_one (norm_nonneg _))
    calc
      ‖suffixActualBandRawCoframeBoundaryForwardLeakage owner lambda S ∘L
            frameTransitionAdjoint lambda p S ∘L
              frameOldFrameAdjoint lambda p S -
          (frameTransitionAdjoint lambda p S ∘L
            suffixActualBandRawCoframeBoundaryForwardLeakage
              owner lambda (p :: S)) ∘L
            frameOldFrameAdjoint lambda p S‖ ≤
        ‖suffixActualBandRawCoframeBoundaryForwardLeakage owner lambda S ∘L
            frameTransitionAdjoint lambda p S ∘L
              frameOldFrameAdjoint lambda p S‖ +
        ‖(frameTransitionAdjoint lambda p S ∘L
            suffixActualBandRawCoframeBoundaryForwardLeakage
              owner lambda (p :: S)) ∘L
            frameOldFrameAdjoint lambda p S‖ :=
        norm_sub_le _ _
      _ ≤ ‖detectorOperator owner‖ * 1 * 1 +
          1 * ‖detectorOperator owner‖ * 1 := by
        exact add_le_add hfirst hsecond
      _ = 2 * ‖detectorOperator owner‖ := by ring
  unfold suffixActualBandRawPhysicalOldCarrierForwardCompleteLeakageTelescope
  calc
    ‖suffixActualBandRawPhysicalOldCarrierForwardAdjointLeakageTelescope
          owner lambda p S +
        suffixActualBandRawPhysicalOldCarrierForwardLeakageTelescope
          owner lambda p S‖ ≤
        ‖suffixActualBandRawPhysicalOldCarrierForwardAdjointLeakageTelescope
          owner lambda p S‖ +
          ‖suffixActualBandRawPhysicalOldCarrierForwardLeakageTelescope
            owner lambda p S‖ := norm_add_le _ _
    _ ≤ 4 * ‖detectorOperator owner‖ := by linarith

/-! ## The reduced Bone 1 target -/

noncomputable def suffixActualBandRawPhysicalOldCarrierKnownBoundedRow
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    finiteSCarrier →L[ℂ] frameCarrier lambda :=
  suffixActualBandRawPhysicalOldCarrierMetricInclusionRow owner lambda p S +
    suffixActualBandRawPhysicalOldCarrierForwardCompleteLeakageTelescope
      owner lambda p S

theorem suffixActualBandRawPhysicalOldCarrierKnownBoundedRow_norm_le
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    ‖suffixActualBandRawPhysicalOldCarrierKnownBoundedRow
        owner lambda p S‖ ≤ 6 * ‖detectorOperator owner‖ := by
  unfold suffixActualBandRawPhysicalOldCarrierKnownBoundedRow
  calc
    ‖suffixActualBandRawPhysicalOldCarrierMetricInclusionRow owner lambda p S +
          suffixActualBandRawPhysicalOldCarrierForwardCompleteLeakageTelescope
            owner lambda p S‖ ≤
        ‖suffixActualBandRawPhysicalOldCarrierMetricInclusionRow
            owner lambda p S‖ +
          ‖suffixActualBandRawPhysicalOldCarrierForwardCompleteLeakageTelescope
            owner lambda p S‖ := norm_add_le _ _
    _ ≤ 2 * ‖detectorOperator owner‖ +
          4 * ‖detectorOperator owner‖ := by
      exact add_le_add
        (suffixActualBandRawPhysicalOldCarrierMetricInclusionRow_norm_le
          owner lambda p S)
        (suffixActualBandRawPhysicalOldCarrierForwardCompleteLeakageTelescope_norm_le
          owner lambda p S)
    _ = 6 * ‖detectorOperator owner‖ := by ring

theorem suffixActualBandRawPhysicalOldCarrierSignedTelescope_eq_orientation_add_residual_add_knownBounded
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandRawPhysicalOldCarrierSignedTelescope owner lambda p S =
      suffixActualBandRawPhysicalOldCarrierMetricOrientationRow owner lambda p S +
        suffixActualBandRawPhysicalOldCarrierMetricResidualRow owner lambda p S +
        suffixActualBandRawPhysicalOldCarrierKnownBoundedRow owner lambda p S := by
  rw [suffixActualBandRawPhysicalOldCarrierSignedTelescope_eq_metric_add_forwardComplete,
    suffixActualBandRawPhysicalOldCarrierMetricLeakageTelescope_eq_orientation_add_residual_add_inclusion,
    suffixActualBandRawPhysicalOldCarrierKnownBoundedRow]
  apply ContinuousLinearMap.ext
  intro y
  simp only [ContinuousLinearMap.add_apply]
  abel


 -/

end CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeOrientationLedger
end CCM25Concrete
end Source
end ConnesWeilRH
