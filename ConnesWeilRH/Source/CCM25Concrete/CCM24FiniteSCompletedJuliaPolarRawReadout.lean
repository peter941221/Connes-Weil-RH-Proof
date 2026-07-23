/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaPhysicalDouglasReadout
import ConnesWeilRH.Source.CC20Concrete.SelfAdjointBoundaryCommutator

/-!
# Polar readout and raw antiresonant gate

Proof 507 packages the complete signed mismatch through the actual
ambient-plus-boundary analysis column, but only under the still-open Douglas
domination.  The polar part needs no such premise: it is exactly the moving
boundary row and therefore reads only the second physical coordinate.

This module constructs that readout unconditionally.  Subtracting any
complete mismatch readout then produces a bounded readout of the whole raw
intertwining adjoint.  Consequently every successful Gate 3U producer must
make the raw row decay on the same ambient antiresonant and moving-boundary
channels.  The raw row is also expanded into its exact four-term physical
normal form; no inverse of the antiresonant factor is introduced.

No raw domination producer, family-uniform bound, Gate 3U conclusion, sign
statement, or RH premise is introduced here.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedJuliaPolarRawReadout

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCompletedJuliaAmbientDefectFactorization
open CCM24FiniteSCompletedJuliaMismatchFactorization
open CCM24FiniteSCompletedJuliaPhysicalDouglasReadout
open CCM24FiniteSCompletedJuliaSynthesis
open CCM24FiniteSFixedSourcePolar
open CCM24FiniteSProjectionTrace
open CCM24FiniteSRawCompletedSchurCocycle
open CCM24FiniteSRawLocalTraceFactorization
open CCM24FiniteSSchurMarkovPairing

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) :
      CompleteSpace (CCM24FiniteSFrameGramCalculus.sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

local notation "SourceOp" lambda =>
  CCM24FiniteSFrameGramCalculus.sourceSoninCarrier lambda →L[ℂ]
    CCM24FiniteSFrameGramCalculus.sourceSoninCarrier lambda

/-! ## The unconditional polar readout -/

/-- Projection onto the genuine moving-boundary coordinate of the physical
ambient-plus-boundary carrier. -/
noncomputable def suffixEulerFrameAmbientBoundaryRightProjection :
    suffixEulerFrameAmbientBoundaryCarrier →L[ℂ] finiteSCarrier :=
  WithLp.sndL (p := 2) (𝕜 := ℂ)
    (α := finiteSCarrier) (β := finiteSCarrier)

@[simp]
theorem suffixEulerFrameAmbientBoundaryRightProjection_apply
    (x : suffixEulerFrameAmbientBoundaryCarrier) :
    suffixEulerFrameAmbientBoundaryRightProjection x = x.snd := by
  rfl

theorem suffixEulerFrameAmbientBoundaryRightProjection_norm_le_one :
    ‖suffixEulerFrameAmbientBoundaryRightProjection‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [suffixEulerFrameAmbientBoundaryRightProjection, one_mul] using
    WithLp.norm_snd_le
      (α := finiteSCarrier) (β := finiteSCarrier) (p := 2) x

/-- The one-sided intertwinement of the actual polar detector compressions. -/
noncomputable def suffixActualBandPolarIntertwiningDefect
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) : SourceOp lambda :=
  suffixEulerFrameTransition lambda p S ∘L
      suffixPolarDetectorCompression owner lambda S -
    suffixPolarDetectorCompression owner lambda (p :: S) ∘L
      suffixEulerFrameTransition lambda p S

theorem suffixActualBandPolarIntertwiningDefect_eq_boundary
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandPolarIntertwiningDefect owner lambda p S =
      suffixEulerDetectorBoundaryDefect owner lambda p S := by
  exact suffixEulerDetectorIntertwiningDefect_eq_boundary owner lambda p S

/-- The polar adjoint readout ignores the ambient coordinate and applies the
actual detector and new-frame adjoint to the moving-boundary coordinate. -/
noncomputable def suffixActualBandPolarPhysicalReadout
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    suffixEulerFrameAmbientBoundaryCarrier →L[ℂ]
      CCM24FiniteSFrameGramCalculus.sourceSoninCarrier lambda :=
  -((newSuffixFrame lambda S)† ∘L detectorOperator owner ∘L
    suffixEulerFrameAmbientBoundaryRightProjection)

@[simp]
theorem suffixActualBandPolarPhysicalReadout_apply
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime)
    (x : suffixEulerFrameAmbientBoundaryCarrier) :
    suffixActualBandPolarPhysicalReadout owner lambda S x =
      -(((newSuffixFrame lambda S)†) (detectorOperator owner x.snd)) := by
  rfl

/-- The explicit readout reconstructs the full polar intertwinement adjoint
from physical analysis, with no Douglas premise. -/
theorem suffixActualBandPolarPhysicalReadout_comp_analysis
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandPolarPhysicalReadout owner lambda S ∘L
        suffixEulerFrameAmbientBoundaryAnalysis lambda p S =
      (suffixActualBandPolarIntertwiningDefect owner lambda p S)† := by
  rw [suffixActualBandPolarIntertwiningDefect_eq_boundary,
    suffixEulerDetectorBoundaryDefect_eq_stepBoundary]
  have hadjoint_neg (operator : SourceOp lambda) :
      (-operator)† = -(operator†) := by
    apply ContinuousLinearMap.ext
    intro y
    exact ext_inner_right ℂ fun z => by
      simp only [ContinuousLinearMap.adjoint_inner_left,
        ContinuousLinearMap.neg_apply, inner_neg_left, inner_neg_right]
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℂ
  intro y
  rw [hadjoint_neg]
  simp only [suffixActualBandPolarPhysicalReadout,
    suffixEulerFrameAmbientBoundaryAnalysis_apply,
    suffixEulerFrameAmbientBoundaryRightProjection_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.adjoint_comp,
    WithLp.toLp_snd,
    (CCM24FiniteSGramResponse.detectorOperator_isSelfAdjoint owner).adjoint_eq]

set_option maxHeartbeats 1000000 in
-- The isometric-frame norm chain needs a larger local elaboration budget.
/-- The normalized suffix frame is contractive because it is an isometric
source-frame inclusion. -/
theorem newSuffixFrame_norm_le_one
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    ‖newSuffixFrame lambda S‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  calc
    ‖newSuffixFrame lambda S x‖ = ‖x‖ := by
      dsimp [newSuffixFrame]
      exact CCM24FiniteSFixedSourcePolar.parameterizedSoninPolarFrame_isometry
        lambda 1 S (by norm_num) x
    _ ≤ 1 * ‖x‖ := by simp

theorem norm_neg_adjoint_comp_comp_le_detector
    {H K L : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup L] [NormedSpace ℂ L]
    (frame : H →L[ℂ] K) (detector : K →L[ℂ] K)
    (projection : L →L[ℂ] K)
    (hframe : ‖frame‖ ≤ 1) (hprojection : ‖projection‖ ≤ 1) :
    ‖-(frame† ∘L detector ∘L projection)‖ ≤ ‖detector‖ := by
  have hframeAdjoint : ‖frame†‖ ≤ 1 := by
    calc
      ‖frame†‖ = ‖frame‖ := ContinuousLinearMap.adjoint.norm_map _
      _ ≤ 1 := hframe
  rw [ContinuousLinearMap.opNorm_neg]
  calc
    ‖frame† ∘L detector ∘L projection‖ ≤
        ‖frame† ∘L detector‖ * ‖projection‖ :=
      by
        simpa only [ContinuousLinearMap.comp_assoc] using
          (ContinuousLinearMap.opNorm_comp_le
            (frame† ∘L detector) projection)
    _ ≤ (‖frame†‖ * ‖detector‖) * ‖projection‖ := by
      exact mul_le_mul_of_nonneg_right
        (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
    _ ≤ (1 * ‖detector‖) * ‖projection‖ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hframeAdjoint (norm_nonneg _))
        (norm_nonneg _)
    _ ≤ (1 * ‖detector‖) * 1 := by
      exact mul_le_mul_of_nonneg_left hprojection
        (mul_nonneg (by norm_num) (norm_nonneg _))
    _ = ‖detector‖ := by ring

set_option maxHeartbeats 1000000 in
-- The nested adjoint/composition norm bound needs a larger local elaboration budget.
/-- The polar readout has a family-independent norm bound: only the selected
detector norm remains. -/
theorem suffixActualBandPolarPhysicalReadout_norm_le
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    ‖suffixActualBandPolarPhysicalReadout owner lambda S‖ ≤
      ‖detectorOperator owner‖ := by
  exact norm_neg_adjoint_comp_comp_le_detector
    (newSuffixFrame lambda S) (detectorOperator owner)
    suffixEulerFrameAmbientBoundaryRightProjection
    (newSuffixFrame_norm_le_one lambda S)
    suffixEulerFrameAmbientBoundaryRightProjection_norm_le_one

/-! ## The raw correction forced by every complete readout -/

/-- Subtracting a complete mismatch readout from the explicit polar readout
is the only possible bounded readout of the whole raw intertwinement adjoint. -/
noncomputable def rawCorrectionReadout
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {bound : ℝ}
    (data : SuffixMismatchAmbientBoundaryReadoutData
      owner lambda p S bound) :
    suffixEulerFrameAmbientBoundaryCarrier →L[ℂ]
      CCM24FiniteSFrameGramCalculus.sourceSoninCarrier lambda :=
  suffixActualBandPolarPhysicalReadout owner lambda S - data.readout

/-- Any complete physical mismatch readout necessarily gives an exact raw
readout on the same two-channel physical carrier. -/
theorem rawCorrection_factorization
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {bound : ℝ}
    (data : SuffixMismatchAmbientBoundaryReadoutData
      owner lambda p S bound) :
    rawCorrectionReadout data ∘L
        suffixEulerFrameAmbientBoundaryAnalysis lambda p S =
      (suffixActualBandRawQuadraticIntertwiningDefect
        owner lambda p S)† := by
  have hpolar := suffixActualBandPolarPhysicalReadout_comp_analysis
    owner lambda p S
  have hmismatch := data.factorization
  have hsplit := suffixActualBandRoutePolarRawMismatchIntertwiningDefect_eq_polar_sub_raw
    owner lambda p S
  apply ContinuousLinearMap.ext
  intro x
  have hpolarPoint := congrArg
    (fun operator : SourceOp lambda => operator x) hpolar
  have hmismatchPoint := congrArg
    (fun operator : SourceOp lambda => operator x) hmismatch
  have hsplitAdjoint := congrArg ContinuousLinearMap.adjoint hsplit
  have hsplitPoint := congrArg
    (fun operator : SourceOp lambda => operator x) hsplitAdjoint
  have hpolarDef :
      suffixActualBandPolarIntertwiningDefect owner lambda p S =
        suffixEulerFrameTransition lambda p S ∘L
            suffixPolarDetectorCompression owner lambda S -
          suffixPolarDetectorCompression owner lambda (p :: S) ∘L
            suffixEulerFrameTransition lambda p S := rfl
  have hadjoint_sub (A B : SourceOp lambda) :
      (A - B)† = A† - B† := by
    apply ContinuousLinearMap.ext
    intro y
    exact ext_inner_right ℂ fun z => by
      simp only [ContinuousLinearMap.adjoint_inner_left,
        ContinuousLinearMap.sub_apply, inner_sub_left, inner_sub_right]
  have hpolarAdjoint :
      (suffixEulerFrameTransition lambda p S ∘L
          suffixPolarDetectorCompression owner lambda S -
        suffixPolarDetectorCompression owner lambda (p :: S) ∘L
          suffixEulerFrameTransition lambda p S)† =
        (suffixEulerFrameTransition lambda p S ∘L
          suffixPolarDetectorCompression owner lambda S)† -
          (suffixPolarDetectorCompression owner lambda (p :: S) ∘L
            suffixEulerFrameTransition lambda p S)† :=
    hadjoint_sub _ _
  have hpolarAdjointPoint :
      (ContinuousLinearMap.adjoint
        (suffixEulerFrameTransition lambda p S ∘L
          suffixPolarDetectorCompression owner lambda S -
        suffixPolarDetectorCompression owner lambda (p :: S) ∘L
          suffixEulerFrameTransition lambda p S)) x =
        (ContinuousLinearMap.adjoint
          (suffixEulerFrameTransition lambda p S ∘L
            suffixPolarDetectorCompression owner lambda S)) x -
          (ContinuousLinearMap.adjoint
            (suffixPolarDetectorCompression owner lambda (p :: S) ∘L
              suffixEulerFrameTransition lambda p S)) x := by
    simpa only [ContinuousLinearMap.sub_apply] using congrArg
      (fun operator : SourceOp lambda => operator x) hpolarAdjoint
  rw [hadjoint_sub, hadjoint_sub] at hsplitPoint
  simp only [rawCorrectionReadout,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply]
    at hpolarPoint hmismatchPoint ⊢
  simp only [ContinuousLinearMap.sub_apply] at hsplitPoint
  rw [hpolarDef] at hpolarPoint
  rw [hpolarPoint, hmismatchPoint]
  rw [hsplitPoint]
  have hstep := congrArg
    (fun z : CCM24FiniteSFrameGramCalculus.sourceSoninCarrier lambda =>
      z -
        ((ContinuousLinearMap.adjoint
            (suffixEulerFrameTransition lambda p S ∘L
              suffixPolarDetectorCompression owner lambda S)) x -
          (ContinuousLinearMap.adjoint
            (suffixPolarDetectorCompression owner lambda (p :: S) ∘L
              suffixEulerFrameTransition lambda p S)) x -
          (ContinuousLinearMap.adjoint
            (suffixActualBandRawQuadraticIntertwiningDefect owner lambda p S)) x))
    hpolarAdjointPoint
  simpa only [sub_sub_cancel] using hstep

theorem rawCorrection_norm_le
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {bound : ℝ}
    (data : SuffixMismatchAmbientBoundaryReadoutData
      owner lambda p S bound) :
    ‖rawCorrectionReadout data‖ ≤
      ‖detectorOperator owner‖ + bound := by
  change ‖suffixActualBandPolarPhysicalReadout owner lambda S - data.readout‖ ≤
    ‖detectorOperator owner‖ + bound
  calc
    ‖suffixActualBandPolarPhysicalReadout owner lambda S - data.readout‖ =
        ‖suffixActualBandPolarPhysicalReadout owner lambda S + -data.readout‖ := by
      rw [sub_eq_add_neg]
    _ ≤ ‖suffixActualBandPolarPhysicalReadout owner lambda S‖ +
          ‖-data.readout‖ := ContinuousLinearMap.opNorm_add_le _ _
    _ = ‖suffixActualBandPolarPhysicalReadout owner lambda S‖ +
          ‖data.readout‖ := by rw [ContinuousLinearMap.opNorm_neg]
    _ ≤ ‖detectorOperator owner‖ + bound :=
      add_le_add
        (suffixActualBandPolarPhysicalReadout_norm_le owner lambda S)
        data.readout_norm_le

/-- Quantitative antiresonant necessity: every successful complete readout
forces the raw row to decay against the same summed physical energy. -/
theorem SuffixMismatchAmbientBoundaryReadoutData.rawAdjoint_norm_le
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {bound : ℝ}
    (data : SuffixMismatchAmbientBoundaryReadoutData
    owner lambda p S bound)
    (x : CCM24FiniteSFrameGramCalculus.sourceSoninCarrier lambda) :
    ‖((suffixActualBandRawQuadraticIntertwiningDefect
        owner lambda p S)†) x‖ ≤
      (‖detectorOperator owner‖ + bound) *
        ‖suffixEulerFrameAmbientBoundaryAnalysis lambda p S x‖ := by
  rw [← rawCorrection_factorization data]
  simp only [ContinuousLinearMap.comp_apply]
  calc
    ‖rawCorrectionReadout data
        (suffixEulerFrameAmbientBoundaryAnalysis lambda p S x)‖ ≤
        ‖rawCorrectionReadout data‖ *
          ‖suffixEulerFrameAmbientBoundaryAnalysis lambda p S x‖ :=
      (rawCorrectionReadout data).le_opNorm _
    _ ≤ (‖detectorOperator owner‖ + bound) *
          ‖suffixEulerFrameAmbientBoundaryAnalysis lambda p S x‖ := by
      exact mul_le_mul_of_nonneg_right (rawCorrection_norm_le data)
        (norm_nonneg _)

/-! ## Exact four-term raw normal form -/

/-- The physical three-branch commutator is skew-adjoint on the actual source
carrier. -/
theorem suffixActualBandThreeBranchCommutator_adjoint_eq_neg
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    (cc20ThreeBranchCommutator (radialSupportProjection lambda)
        (sourceFourierSupportProjection lambda)
        (sourceProlateRemainder lambda) (detectorOperator owner))† =
      -cc20ThreeBranchCommutator (radialSupportProjection lambda)
        (sourceFourierSupportProjection lambda)
        (sourceProlateRemainder lambda) (detectorOperator owner) := by
  rw [← CCM24FiniteSGramResponse.sourceSoninCommutator_eq_threeBranch]
  exact cc20Commutator_adjoint_eq_neg _ _
    (sourceSoninProjection_isStarProjection lambda).isSelfAdjoint
    (CCM24FiniteSGramResponse.detectorOperator_isSelfAdjoint owner)

/-- Adjoint normal form for one raw suffix response. -/
theorem suffixActualBandRawQuadraticCycledResponse_adjoint_eq_physical
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    (suffixActualBandRawQuadraticCycledResponse owner lambda S)† =
      -((suffixActualBandForwardEndpointCoframe lambda S)† ∘L
        cc20ThreeBranchCommutator (radialSupportProjection lambda)
          (sourceFourierSupportProjection lambda)
          (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
        CCM24FiniteSGramResponse.sourceInclusion lambda) +
      (CCM24FiniteSGramResponse.sourceInclusion lambda)† ∘L
        cc20ThreeBranchCommutator (radialSupportProjection lambda)
          (sourceFourierSupportProjection lambda)
          (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
        suffixActualBandForwardCoframe lambda S := by
  rw [← suffixActualBandRawCommonPhysicalResponse_eq_raw]
  have hadjoint_sub (A B : SourceOp lambda) :
      (A - B)† = A† - B† := by
    apply ContinuousLinearMap.ext
    intro y
    exact ext_inner_right ℂ fun z => by
      simp only [ContinuousLinearMap.adjoint_inner_left,
        ContinuousLinearMap.sub_apply, inner_sub_left, inner_sub_right]
  have hrawAdjoint :
      ((CCM24FiniteSGramResponse.sourceInclusion lambda)† ∘L
          cc20ThreeBranchCommutator (radialSupportProjection lambda)
            (sourceFourierSupportProjection lambda)
            (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
          suffixActualBandForwardEndpointCoframe lambda S -
        (suffixActualBandForwardCoframe lambda S)† ∘L
          cc20ThreeBranchCommutator (radialSupportProjection lambda)
            (sourceFourierSupportProjection lambda)
            (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
          CCM24FiniteSGramResponse.sourceInclusion lambda)† =
        ((CCM24FiniteSGramResponse.sourceInclusion lambda)† ∘L
          cc20ThreeBranchCommutator (radialSupportProjection lambda)
            (sourceFourierSupportProjection lambda)
            (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
          suffixActualBandForwardEndpointCoframe lambda S)† -
          ((suffixActualBandForwardCoframe lambda S)† ∘L
            cc20ThreeBranchCommutator (radialSupportProjection lambda)
              (sourceFourierSupportProjection lambda)
              (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
            CCM24FiniteSGramResponse.sourceInclusion lambda)† :=
    hadjoint_sub _ _
  have hfirstAdjoint :
      ((CCM24FiniteSGramResponse.sourceInclusion lambda)† ∘L
          cc20ThreeBranchCommutator (radialSupportProjection lambda)
            (sourceFourierSupportProjection lambda)
            (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
          suffixActualBandForwardEndpointCoframe lambda S)† =
        (suffixActualBandForwardEndpointCoframe lambda S)† ∘L
          (cc20ThreeBranchCommutator (radialSupportProjection lambda)
            (sourceFourierSupportProjection lambda)
            (sourceProlateRemainder lambda) (detectorOperator owner))† ∘L
          CCM24FiniteSGramResponse.sourceInclusion lambda := by
    simp only [ContinuousLinearMap.comp_assoc,
      ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint]
  have hsecondAdjoint :
      ((suffixActualBandForwardCoframe lambda S)† ∘L
          cc20ThreeBranchCommutator (radialSupportProjection lambda)
            (sourceFourierSupportProjection lambda)
            (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
          CCM24FiniteSGramResponse.sourceInclusion lambda)† =
        (CCM24FiniteSGramResponse.sourceInclusion lambda)† ∘L
          (cc20ThreeBranchCommutator (radialSupportProjection lambda)
            (sourceFourierSupportProjection lambda)
            (sourceProlateRemainder lambda) (detectorOperator owner))† ∘L
          suffixActualBandForwardCoframe lambda S := by
    simp only [ContinuousLinearMap.comp_assoc,
      ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint]
  rw [suffixActualBandRawCommonPhysicalResponse, hrawAdjoint]
  simp only [hfirstAdjoint, hsecondAdjoint]
  rw [suffixActualBandThreeBranchCommutator_adjoint_eq_neg]
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.neg_apply,
    map_neg]
  abel

/-- The raw adjacent intertwinement adjoint has four exact physical terms.
This is the source-specific expression which must be divisible by the summed
ambient antiresonant and moving-boundary analysis column. -/
theorem suffixActualBandRawQuadraticIntertwiningDefect_adjoint_eq_fourTerm
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    (suffixActualBandRawQuadraticIntertwiningDefect owner lambda p S)† =
      -((suffixActualBandForwardEndpointCoframe lambda S)† ∘L
          cc20ThreeBranchCommutator (radialSupportProjection lambda)
            (sourceFourierSupportProjection lambda)
            (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
          CCM24FiniteSGramResponse.sourceInclusion lambda ∘L
          (suffixEulerFrameTransition lambda p S)†) +
        (CCM24FiniteSGramResponse.sourceInclusion lambda)† ∘L
          cc20ThreeBranchCommutator (radialSupportProjection lambda)
            (sourceFourierSupportProjection lambda)
            (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
          suffixActualBandForwardCoframe lambda S ∘L
          (suffixEulerFrameTransition lambda p S)† +
        (suffixEulerFrameTransition lambda p S)† ∘L
          (suffixActualBandForwardEndpointCoframe lambda (p :: S))† ∘L
          cc20ThreeBranchCommutator (radialSupportProjection lambda)
            (sourceFourierSupportProjection lambda)
            (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
          CCM24FiniteSGramResponse.sourceInclusion lambda -
        (suffixEulerFrameTransition lambda p S)† ∘L
          (CCM24FiniteSGramResponse.sourceInclusion lambda)† ∘L
          cc20ThreeBranchCommutator (radialSupportProjection lambda)
            (sourceFourierSupportProjection lambda)
            (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
          suffixActualBandForwardCoframe lambda (p :: S) := by
  calc
    (suffixActualBandRawQuadraticIntertwiningDefect owner lambda p S)† =
        ((suffixEulerFrameTransition lambda p S ∘L
            suffixActualBandRawQuadraticCycledResponse owner lambda S)† -
          (suffixActualBandRawQuadraticCycledResponse owner lambda (p :: S) ∘L
            suffixEulerFrameTransition lambda p S)†) := by
      rw [suffixActualBandRawQuadraticIntertwiningDefect]
      apply ContinuousLinearMap.ext
      intro y
      exact ext_inner_right ℂ fun z => by
        simp only [ContinuousLinearMap.adjoint_inner_left,
          ContinuousLinearMap.sub_apply, inner_sub_left, inner_sub_right]
    _ = ((suffixActualBandRawQuadraticCycledResponse owner lambda S)† ∘L
          (suffixEulerFrameTransition lambda p S)† -
        (suffixEulerFrameTransition lambda p S)† ∘L
          (suffixActualBandRawQuadraticCycledResponse owner lambda (p :: S))†) := by
      congr 1
      · exact ContinuousLinearMap.adjoint_comp _ _
      · exact ContinuousLinearMap.adjoint_comp _ _
    _ =
        ((-((suffixActualBandForwardEndpointCoframe lambda S)† ∘L
              cc20ThreeBranchCommutator (radialSupportProjection lambda)
                (sourceFourierSupportProjection lambda)
                (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
              CCM24FiniteSGramResponse.sourceInclusion lambda) +
            (CCM24FiniteSGramResponse.sourceInclusion lambda)† ∘L
              cc20ThreeBranchCommutator (radialSupportProjection lambda)
                (sourceFourierSupportProjection lambda)
                (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
              suffixActualBandForwardCoframe lambda S) ∘L
          (suffixEulerFrameTransition lambda p S)† -
        (suffixEulerFrameTransition lambda p S)† ∘L
          (-((suffixActualBandForwardEndpointCoframe lambda (p :: S))† ∘L
              cc20ThreeBranchCommutator (radialSupportProjection lambda)
                (sourceFourierSupportProjection lambda)
                (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
              CCM24FiniteSGramResponse.sourceInclusion lambda) +
            (CCM24FiniteSGramResponse.sourceInclusion lambda)† ∘L
              cc20ThreeBranchCommutator (radialSupportProjection lambda)
                (sourceFourierSupportProjection lambda)
                (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
              suffixActualBandForwardCoframe lambda (p :: S))) := by
      have hS :=
        suffixActualBandRawQuadraticCycledResponse_adjoint_eq_physical
          owner lambda S
      have hP :=
        suffixActualBandRawQuadraticCycledResponse_adjoint_eq_physical
          owner lambda (p :: S)
      exact congrArg₂
        (fun left right : SourceOp lambda => left - right)
        (congrArg
          (fun operator : SourceOp lambda =>
            operator ∘L (suffixEulerFrameTransition lambda p S)†) hS)
        (congrArg
          (fun operator : SourceOp lambda =>
            (suffixEulerFrameTransition lambda p S)† ∘L operator) hP)
    _ = _ := by
      have hlinear (A B C D E : SourceOp lambda) :
          (-A + B) ∘L E - E ∘L (-C + D) =
            -(A ∘L E) + B ∘L E + E ∘L C - E ∘L D := by
        apply ContinuousLinearMap.ext
        intro x
        simp only [ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
          ContinuousLinearMap.neg_apply, map_add, map_neg]
        abel
      simpa only [ContinuousLinearMap.comp_assoc] using
        hlinear
          ((suffixActualBandForwardEndpointCoframe lambda S)† ∘L
            cc20ThreeBranchCommutator (radialSupportProjection lambda)
              (sourceFourierSupportProjection lambda)
              (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
            CCM24FiniteSGramResponse.sourceInclusion lambda)
          ((CCM24FiniteSGramResponse.sourceInclusion lambda)† ∘L
            cc20ThreeBranchCommutator (radialSupportProjection lambda)
              (sourceFourierSupportProjection lambda)
              (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
            suffixActualBandForwardCoframe lambda S)
          ((suffixActualBandForwardEndpointCoframe lambda (p :: S))† ∘L
            cc20ThreeBranchCommutator (radialSupportProjection lambda)
              (sourceFourierSupportProjection lambda)
              (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
            CCM24FiniteSGramResponse.sourceInclusion lambda)
          ((CCM24FiniteSGramResponse.sourceInclusion lambda)† ∘L
            cc20ThreeBranchCommutator (radialSupportProjection lambda)
              (sourceFourierSupportProjection lambda)
              (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
            suffixActualBandForwardCoframe lambda (p :: S))
          ((suffixEulerFrameTransition lambda p S)†)

end CCM24FiniteSCompletedJuliaPolarRawReadout
end CCM25Concrete
end Source
end ConnesWeilRH
