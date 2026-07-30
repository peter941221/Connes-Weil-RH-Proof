/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSJointResidualDouglasReadout

/-!
# Uniform norm control for the actual Schur/physical residual

The physical inverse and the source-forward actual Schur product are both
contractions after the same Euler lower normalization.  Their genuine
variation-of-constants residual is therefore uniformly bounded by `2`, with no
dependence on the visible prime list.

This is an operator-norm producer only.  It does not turn the residual into a
readout through the two-channel Schur analysis column.  That stronger step is a
Douglas estimate and remains a separate source theorem.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSActualSchurPhysicalResidualUniformControl

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSActualJuliaInput
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSActualSchurForwardPhysicalDifference
open CCM24FiniteSActualSchurForwardTransport
open CCM24FiniteSActualSchurTelescoping
open CCM24FiniteSCausalMarkov
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSFixedQuotientCarrier
open CCM24FiniteSProjectionTrace
open CCM24FiniteSCompletedJuliaRawPhysicalResidualLedger
open CCM24FiniteSJointResidualDouglasReadout
open CCM24FiniteSActualSchurEndpointAlignmentResidual

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace
      (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

local notation "SourceOp" lambda =>
  sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda

/-! ## The normalized physical inverse -/

theorem norm_normalizedFiniteEulerInverseList_le_one
    (S : List CCM24VisiblePrime) :
    ‖normalizedFiniteEulerInverseList S‖ ≤ (1 : ℝ) := by
  induction S with
  | nil =>
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro x
      simp [normalizedFiniteEulerInverseList,
        CCM24FiniteSGramResponse.finiteEulerLowerFactor]
  | cons p S ih =>
      rw [normalizedFiniteEulerInverseList_cons]
      calc
        ‖normalizedFiniteEulerInverseList S ∘L
            normalizedPrimeEulerInverse p‖ ≤
            ‖normalizedFiniteEulerInverseList S‖ *
              ‖normalizedPrimeEulerInverse p‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ 1 * 1 := by
          exact mul_le_mul ih
            (norm_normalizedPrimeEulerInverse_le_one p)
            (norm_nonneg _) zero_le_one
        _ = 1 := by norm_num

/-! ## The actual residual -/

theorem suffixActualSchurForwardPhysicalTransportResidual_norm_le_two
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (S : List CCM24VisiblePrime) :
    ‖suffixActualSchurForwardPhysicalTransportResidual lambda stepData S‖ ≤
      (2 : ℝ) := by
  rw [← normalizedFiniteEulerInverseList_sub_forwardAmbient_eq_residual
    lambda stepData S]
  calc
    ‖normalizedFiniteEulerInverseList S -
        suffixActualSchurForwardAmbientProduct lambda stepData S‖ ≤
      ‖normalizedFiniteEulerInverseList S‖ +
        ‖suffixActualSchurForwardAmbientProduct lambda stepData S‖ :=
      norm_sub_le _ _
    _ ≤ 1 + 1 := by
      exact add_le_add
        (norm_normalizedFiniteEulerInverseList_le_one S)
        (suffixActualSchurForwardAmbientProduct_norm_le_one
          lambda stepData S)
    _ = 2 := by norm_num

set_option maxHeartbeats 4000000 in
-- The source projection/inclusion norm chain needs a larger deterministic
-- elaboration budget after the rectangular carrier coercions are exposed.
theorem sourceActualBandForwardTransportResidual_norm_le_two
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (S : List CCM24VisiblePrime) :
    ‖sourceActualBandForwardTransportResidual lambda stepData S‖ ≤
      (2 : ℝ) := by
  unfold sourceActualBandForwardTransportResidual
  have hband : ‖sourceBandProjection lambda‖ ≤ (1 : ℝ) :=
    IsStarProjection.norm_le _ (sourceBandProjection_isStarProjection lambda)
  have hinclusion : ‖CCM24FiniteSGramResponse.sourceInclusion lambda‖ ≤
      (1 : ℝ) :=
    Submodule.norm_subtypeL_le _
  have hres :=
    suffixActualSchurForwardPhysicalTransportResidual_norm_le_two
      lambda stepData S
  calc
    ‖sourceBandProjection lambda ∘L
        suffixActualSchurForwardPhysicalTransportResidual lambda stepData S ∘L
          CCM24FiniteSGramResponse.sourceInclusion lambda‖ ≤
        ‖sourceBandProjection lambda‖ *
          ‖suffixActualSchurForwardPhysicalTransportResidual lambda stepData S ∘L
            CCM24FiniteSGramResponse.sourceInclusion lambda‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖sourceBandProjection lambda‖ *
        (‖suffixActualSchurForwardPhysicalTransportResidual lambda stepData S‖ *
          ‖CCM24FiniteSGramResponse.sourceInclusion lambda‖) := by
      exact mul_le_mul_of_nonneg_left
        (ContinuousLinearMap.opNorm_comp_le _ _)
        (norm_nonneg _)
    _ ≤ 1 * (2 * 1) := by
      exact mul_le_mul hband
        (mul_le_mul hres hinclusion
          (norm_nonneg (CCM24FiniteSGramResponse.sourceInclusion lambda))
          (by norm_num))
        (mul_nonneg
          (norm_nonneg
            (suffixActualSchurForwardPhysicalTransportResidual lambda
              stepData S))
          (norm_nonneg (CCM24FiniteSGramResponse.sourceInclusion lambda)))
        zero_le_one
    _ = 2 := by norm_num

/-! ## Endpoint residual ledger -/

theorem suffixActualSchurEndpointAlignmentResidual_add_endpointResidual_norm_le_two
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (family : FinitePrimePowerFamily) :
    ‖suffixActualSchurEndpointAlignmentResidual lambda stepData family +
        suffixActualSchurEndpointResidual lambda stepData family‖ ≤
      (2 : ℝ) := by
  rw [suffixActualSchurEndpointAlignmentResidual_add_endpointResidual_eq_transportResidual
    lambda stepData family]
  exact sourceActualBandForwardTransportResidual_norm_le_two lambda stepData
    family.visiblePrimes

/-! ## The signed physical residual row -/

/-- The exact signed row carried by the two physical-versus-Schur suffix
residual coframes.  The four terms are kept together; this definition is not a
termwise norm estimate. -/
noncomputable def rawPhysicalTransportResidualRow
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime)
    (residualS residualPS :
      sourceSoninCarrier lambda →L[ℂ] finiteSCarrier) : SourceOp lambda :=
  -((residualS)† ∘L
      cc20ThreeBranchCommutator (radialSupportProjection lambda)
        (sourceFourierSupportProjection lambda)
        (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
      CCM24FiniteSGramResponse.sourceInclusion lambda ∘L
      (suffixEulerFrameTransition lambda p S)†) +
    (CCM24FiniteSGramResponse.sourceInclusion lambda)† ∘L
      cc20ThreeBranchCommutator (radialSupportProjection lambda)
        (sourceFourierSupportProjection lambda)
        (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
      residualS ∘L (suffixEulerFrameTransition lambda p S)† +
    (suffixEulerFrameTransition lambda p S)† ∘L
      (residualPS)† ∘L
      cc20ThreeBranchCommutator (radialSupportProjection lambda)
        (sourceFourierSupportProjection lambda)
        (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
      CCM24FiniteSGramResponse.sourceInclusion lambda -
    (suffixEulerFrameTransition lambda p S)† ∘L
      (CCM24FiniteSGramResponse.sourceInclusion lambda)† ∘L
      cc20ThreeBranchCommutator (radialSupportProjection lambda)
        (sourceFourierSupportProjection lambda)
        (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
      residualPS

set_option maxHeartbeats 4000000 in
-- The four-term rectangular-adjoint extensionality crosses several subtype
-- carriers and needs a larger deterministic elaboration budget.
set_option maxRecDepth 10000 in
theorem rawPhysicalCoframeResidualRow_eq_transportResidualRow
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime)
    (actualForwardS actualEndpointS actualEndpointPS actualForwardPS :
      sourceSoninCarrier lambda →L[ℂ] finiteSCarrier)
    (schurForwardS schurEndpointS schurEndpointPS schurForwardPS :
      sourceSoninCarrier lambda →L[ℂ] finiteSCarrier)
    (residualS residualPS :
      sourceSoninCarrier lambda →L[ℂ] finiteSCarrier)
    (hforwardS : actualForwardS = schurForwardS + residualS)
    (hendpointS : actualEndpointS = schurEndpointS + residualS)
    (hendpointPS : actualEndpointPS = schurEndpointPS + residualPS)
    (hforwardPS : actualForwardPS = schurForwardPS + residualPS) :
    rawPhysicalCoframeResidualRow owner lambda p S
        actualForwardS actualEndpointS actualEndpointPS actualForwardPS
        schurForwardS schurEndpointS schurEndpointPS schurForwardPS =
      rawPhysicalTransportResidualRow owner lambda p S residualS residualPS := by
  rw [rawPhysicalCoframeResidualRow, hforwardS, hendpointS, hendpointPS,
    hforwardPS]
  have hadjoint_add (A B : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier) :
      (A + B)† = A† + B† := by
    apply ContinuousLinearMap.ext
    intro y
    exact ext_inner_right ℂ fun z => by
      simp only [ContinuousLinearMap.adjoint_inner_left,
        ContinuousLinearMap.add_apply, inner_add_left, inner_add_right]
  apply ContinuousLinearMap.ext
  intro x
  simp only [rawPhysicalFourTermRowOfCoframes,
    rawPhysicalTransportResidualRow, hadjoint_add,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, map_add]
  simp; abel

theorem suffixActualBandNamedSchurCoframeResidualRow_eq_transportResidualRow
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime) :
    suffixActualBandNamedSchurCoframeResidualRow owner lambda stepData p S =
      rawPhysicalTransportResidualRow owner lambda p S
        (sourceActualBandForwardTransportResidual lambda stepData S)
        (sourceActualBandForwardTransportResidual lambda stepData (p :: S)) := by
  apply rawPhysicalCoframeResidualRow_eq_transportResidualRow
  · exact suffixActualBandForwardCoframe_eq_namedSchur_add_transportResidual
      lambda stepData S
  · exact suffixActualBandForwardEndpointCoframe_eq_namedSchurEndpoint_add_transportResidual
      lambda stepData S
  · exact suffixActualBandForwardEndpointCoframe_eq_namedSchurEndpoint_add_transportResidual
      lambda stepData (p :: S)
  · exact suffixActualBandForwardCoframe_eq_namedSchur_add_transportResidual
      lambda stepData (p :: S)

/-! ## A signed-row norm bound -/

theorem norm_comp_four_le
    {H₀ H₁ H₂ H₃ H₄ : Type*}
    [NormedAddCommGroup H₀] [NormedSpace ℂ H₀]
    [NormedAddCommGroup H₁] [NormedSpace ℂ H₁]
    [NormedAddCommGroup H₂] [NormedSpace ℂ H₂]
    [NormedAddCommGroup H₃] [NormedSpace ℂ H₃]
    [NormedAddCommGroup H₄] [NormedSpace ℂ H₄]
    (A : H₃ →L[ℂ] H₄) (B : H₂ →L[ℂ] H₃)
    (C : H₁ →L[ℂ] H₂) (D : H₀ →L[ℂ] H₁) :
    ‖A ∘L B ∘L C ∘L D‖ ≤ ‖A‖ * ‖B‖ * ‖C‖ * ‖D‖ := by
  calc
    ‖A ∘L B ∘L C ∘L D‖ ≤
        ‖A‖ * ‖B ∘L C ∘L D‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖A‖ * (‖B‖ * ‖C ∘L D‖) := by
      exact mul_le_mul_of_nonneg_left
        (ContinuousLinearMap.opNorm_comp_le _ _)
        (norm_nonneg _)
    _ ≤ ‖A‖ * (‖B‖ * (‖C‖ * ‖D‖)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (ContinuousLinearMap.opNorm_comp_le _ _)
          (norm_nonneg _))
        (norm_nonneg _)
    _ = ‖A‖ * ‖B‖ * ‖C‖ * ‖D‖ := by ring

set_option maxHeartbeats 4000000 in
-- The four-row operator-norm expansion is elaborated through nested adjoints
-- and needs a larger deterministic heartbeat budget.
theorem rawPhysicalTransportResidualRow_norm_le_eight_mul_commutator
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime)
    (residualS residualPS :
      sourceSoninCarrier lambda →L[ℂ] finiteSCarrier)
    (hresidualS : ‖residualS‖ ≤ (2 : ℝ))
    (hresidualPS : ‖residualPS‖ ≤ (2 : ℝ)) :
    ‖rawPhysicalTransportResidualRow owner lambda p S residualS residualPS‖ ≤
      8 * ‖cc20ThreeBranchCommutator (radialSupportProjection lambda)
        (sourceFourierSupportProjection lambda)
        (sourceProlateRemainder lambda) (detectorOperator owner)‖ := by
  let K : finiteSCarrier →L[ℂ] finiteSCarrier :=
    cc20ThreeBranchCommutator (radialSupportProjection lambda)
      (sourceFourierSupportProjection lambda)
      (sourceProlateRemainder lambda) (detectorOperator owner)
  let J : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier :=
    CCM24FiniteSGramResponse.sourceInclusion lambda
  let T : sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
    suffixEulerFrameTransition lambda p S
  let rowA : SourceOp lambda :=
    (residualS)† ∘L K ∘L J ∘L T†
  let rowB : SourceOp lambda :=
    J† ∘L K ∘L residualS ∘L T†
  let rowC : SourceOp lambda :=
    T† ∘L (residualPS)† ∘L K ∘L J
  let rowD : SourceOp lambda :=
    T† ∘L J† ∘L K ∘L residualPS
  have hJ : ‖J‖ ≤ (1 : ℝ) := by
    exact Submodule.norm_subtypeL_le _
  have hJAdjNorm : ‖J†‖ = ‖J‖ :=
    ContinuousLinearMap.adjoint.norm_map _
  have hJadj : ‖J†‖ ≤ (1 : ℝ) := by
    calc
      ‖J†‖ = ‖J‖ := hJAdjNorm
      _ ≤ 1 := hJ
  have hT : ‖T‖ ≤ (1 : ℝ) := by
    exact suffixEulerFrameTransition_norm_le_one lambda p S
  have hTAdjNorm : ‖T†‖ = ‖T‖ :=
    ContinuousLinearMap.adjoint.norm_map _
  have hTadj : ‖T†‖ ≤ (1 : ℝ) := by
    calc
      ‖T†‖ = ‖T‖ := hTAdjNorm
      _ ≤ 1 := hT
  have hresidualSAdjNorm : ‖residualS†‖ = ‖residualS‖ :=
    ContinuousLinearMap.adjoint.norm_map _
  have hresidualPSAdjNorm : ‖residualPS†‖ = ‖residualPS‖ :=
    ContinuousLinearMap.adjoint.norm_map _
  have hfour (r k j t : ℝ)
      (hr : r ≤ 2) (hj : j ≤ 1) (ht : t ≤ 1)
      (hk : 0 ≤ k) (hj0 : 0 ≤ j) (ht0 : 0 ≤ t) :
      r * k * j * t ≤ 2 * k := by
    calc
      r * k * j * t ≤ (2 * k) * j * t := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hr hk)
            hj0)
          ht0
      _ ≤ (2 * k) * 1 * t := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hj
            (mul_nonneg (by norm_num) hk))
          ht0
      _ ≤ (2 * k) * 1 * 1 := by
        exact mul_le_mul_of_nonneg_left ht
          (mul_nonneg (mul_nonneg (by norm_num) hk) (by norm_num))
      _ = 2 * k := by ring
  have hrowA : ‖rowA‖ ≤ 2 * ‖K‖ := by
    dsimp only [rowA]
    calc
      ‖(residualS)† ∘L K ∘L J ∘L T†‖ ≤
          ‖(residualS)†‖ * ‖K‖ * ‖J‖ * ‖T†‖ := by
        exact norm_comp_four_le _ _ _ _
      _ = ‖residualS‖ * ‖K‖ * ‖J‖ * ‖T‖ := by
        rw [hresidualSAdjNorm, hTAdjNorm]
      _ ≤ 2 * ‖K‖ := by
        exact hfour _ _ _ _ hresidualS hJ hT
          (norm_nonneg K) (norm_nonneg J) (norm_nonneg T)
  have hrowB : ‖rowB‖ ≤ 2 * ‖K‖ := by
    dsimp only [rowB]
    calc
      ‖J† ∘L K ∘L residualS ∘L T†‖ ≤
          ‖J†‖ * ‖K‖ * ‖residualS‖ * ‖T†‖ := by
        exact norm_comp_four_le _ _ _ _
      _ = ‖residualS‖ * ‖K‖ * ‖J‖ * ‖T‖ := by
        rw [hJAdjNorm, hTAdjNorm]
        ring
      _ ≤ 2 * ‖K‖ := by
        exact hfour _ _ _ _ hresidualS hJ hT
          (norm_nonneg K) (norm_nonneg J) (norm_nonneg T)
  have hrowC : ‖rowC‖ ≤ 2 * ‖K‖ := by
    dsimp only [rowC]
    calc
      ‖T† ∘L (residualPS)† ∘L K ∘L J‖ ≤
          ‖T†‖ * ‖(residualPS)†‖ * ‖K‖ * ‖J‖ := by
        exact norm_comp_four_le _ _ _ _
      _ = ‖residualPS‖ * ‖K‖ * ‖J‖ * ‖T‖ := by
        rw [hTAdjNorm, hresidualPSAdjNorm]
        ring
      _ ≤ 2 * ‖K‖ := by
        exact hfour _ _ _ _ hresidualPS hJ hT
          (norm_nonneg K) (norm_nonneg J) (norm_nonneg T)
  have hrowD : ‖rowD‖ ≤ 2 * ‖K‖ := by
    dsimp only [rowD]
    calc
      ‖T† ∘L J† ∘L K ∘L residualPS‖ ≤
          ‖T†‖ * ‖J†‖ * ‖K‖ * ‖residualPS‖ := by
        exact norm_comp_four_le _ _ _ _
      _ = ‖residualPS‖ * ‖K‖ * ‖J‖ * ‖T‖ := by
        rw [hTAdjNorm, hJAdjNorm]
        ring
      _ ≤ 2 * ‖K‖ := by
        exact hfour _ _ _ _ hresidualPS hJ hT
          (norm_nonneg K) (norm_nonneg J) (norm_nonneg T)
  have hsum (A B C D : SourceOp lambda) :
      ‖-A + B + C - D‖ ≤ ‖A‖ + ‖B‖ + ‖C‖ + ‖D‖ := by
    calc
      ‖-A + B + C - D‖ ≤ ‖-A + B + C‖ + ‖D‖ :=
        norm_sub_le (-A + B + C) D
      _ ≤ (‖-A + B‖ + ‖C‖) + ‖D‖ := by
        exact add_le_add (norm_add_le (-A + B) C) (le_refl _)
      _ ≤ ((‖A‖ + ‖B‖) + ‖C‖) + ‖D‖ := by
        have hAB : ‖-A + B‖ ≤ ‖A‖ + ‖B‖ := by
          calc
            ‖-A + B‖ ≤ ‖-A‖ + ‖B‖ := norm_add_le (-A) B
            _ = ‖A‖ + ‖B‖ := by
              exact congrArg (fun x : ℝ => x + ‖B‖) (norm_neg A)
        exact add_le_add (add_le_add hAB (le_refl _)) (le_refl _)
      _ = ‖A‖ + ‖B‖ + ‖C‖ + ‖D‖ := by ring
  change ‖-rowA + rowB + rowC - rowD‖ ≤ 8 * ‖K‖
  calc
    ‖-rowA + rowB + rowC - rowD‖ ≤
        ‖rowA‖ + ‖rowB‖ + ‖rowC‖ + ‖rowD‖ := hsum _ _ _ _
    _ ≤ (2 * ‖K‖) + (2 * ‖K‖) + (2 * ‖K‖) + (2 * ‖K‖) := by
      exact add_le_add (add_le_add (add_le_add hrowA hrowB) hrowC) hrowD
    _ = 8 * ‖K‖ := by ring

set_option maxHeartbeats 4000000 in
-- The named suffix specialization repeats the nested row normalization and
-- needs the same deterministic heartbeat budget as its generic owner.
theorem suffixActualBandNamedSchurCoframeResidualRow_norm_le_eight_mul_commutator
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime) :
    ‖suffixActualBandNamedSchurCoframeResidualRow owner lambda stepData p S‖ ≤
      8 * ‖cc20ThreeBranchCommutator (radialSupportProjection lambda)
        (sourceFourierSupportProjection lambda)
        (sourceProlateRemainder lambda) (detectorOperator owner)‖ := by
  rw [suffixActualBandNamedSchurCoframeResidualRow_eq_transportResidualRow
    owner lambda stepData p S]
  exact rawPhysicalTransportResidualRow_norm_le_eight_mul_commutator owner
    lambda p S
    (sourceActualBandForwardTransportResidual lambda stepData S)
    (sourceActualBandForwardTransportResidual lambda stepData (p :: S))
    (sourceActualBandForwardTransportResidual_norm_le_two lambda stepData S)
    (sourceActualBandForwardTransportResidual_norm_le_two lambda stepData
      (p :: S))

end CCM24FiniteSActualSchurPhysicalResidualUniformControl
end CCM25Concrete
end Source
end ConnesWeilRH
