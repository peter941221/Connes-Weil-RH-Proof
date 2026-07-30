/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeRangeFactorization
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeBoundedPieces
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOnePrimeMomentObstruction

/-!
# Scalar-normalized right inverse for the old-carrier coframe channel

The finite-S Schur--Markov transport has a non-unit scalar right inverse:

```text
T_p * V_p = rho_p * I.
```

This module inserts `rho_p⁻¹` before applying the generic range
factorization.  It also exposes the exact old/new frame readback, so a source
producer cannot silently replace a genuine annihilation premise by a
projection-compression identity.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeScalarRightInverse

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeDivideConquer
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeRangeFactorization
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeOrientationLedger
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeResidual
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierLeakageExpansion
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierReduction
open CCM24FiniteSCompletedJuliaRawPhysicalOnePrimeMomentObstruction
open CCM24FiniteSCausalMarkov
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSProjectionTrace
open CCM24FiniteSSchurMarkovPairing

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

local notation "SourceOp" lambda =>
  sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda

/-! ## The scalar-normalized right inverse -/

noncomputable def scalarNormalizedPrimeEulerInverse
    (p : CCM24VisiblePrime) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  (primeSchurMarkovScalar p : ℂ)⁻¹ • normalizedPrimeEulerInverse p

theorem normalizedPrimeEulerFrameTransport_comp_scalarNormalizedInverse
    (p : CCM24VisiblePrime) :
    normalizedPrimeEulerFrameTransport p ∘L
        scalarNormalizedPrimeEulerInverse p =
      ContinuousLinearMap.id ℂ finiteSCarrier := by
  have hscalar : (primeSchurMarkovScalar p : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (primeSchurMarkovScalar_pos p))
  calc
    normalizedPrimeEulerFrameTransport p ∘L
          scalarNormalizedPrimeEulerInverse p =
        (primeSchurMarkovScalar p : ℂ)⁻¹ •
          (normalizedPrimeEulerFrameTransport p ∘L
            normalizedPrimeEulerInverse p) := by
      apply ContinuousLinearMap.ext
      intro x
      simp only [scalarNormalizedPrimeEulerInverse,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
        map_smul]
    _ = (primeSchurMarkovScalar p : ℂ)⁻¹ •
          ((primeSchurMarkovScalar p : ℂ) •
            ContinuousLinearMap.id ℂ finiteSCarrier) := by
      rw [normalizedPrimeEulerFrameTransport_comp_inverse]
    _ = ContinuousLinearMap.id ℂ finiteSCarrier := by
      rw [smul_smul, inv_mul_cancel₀ hscalar, one_smul]

theorem scalarNormalizedPrimeEulerInverse_comp_normalizedPrimeEulerFrameTransport
    (p : CCM24VisiblePrime) :
    scalarNormalizedPrimeEulerInverse p ∘L
        normalizedPrimeEulerFrameTransport p =
      ContinuousLinearMap.id ℂ finiteSCarrier := by
  have hscalar : (primeSchurMarkovScalar p : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (primeSchurMarkovScalar_pos p))
  calc
    scalarNormalizedPrimeEulerInverse p ∘L
          normalizedPrimeEulerFrameTransport p =
        (primeSchurMarkovScalar p : ℂ)⁻¹ •
          (normalizedPrimeEulerInverse p ∘L
            normalizedPrimeEulerFrameTransport p) := by
      apply ContinuousLinearMap.ext
      intro x
      simp only [scalarNormalizedPrimeEulerInverse,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
        map_smul]
    _ = (primeSchurMarkovScalar p : ℂ)⁻¹ •
          ((primeSchurMarkovScalar p : ℂ) •
            ContinuousLinearMap.id ℂ finiteSCarrier) := by
      rw [normalizedPrimeEulerInverse_comp_frameTransport]
    _ = ContinuousLinearMap.id ℂ finiteSCarrier := by
      rw [smul_smul, inv_mul_cancel₀ hscalar, one_smul]

theorem scalarNormalizedPrimeEulerInverse_norm_le_eight
    (p : CCM24VisiblePrime) :
    ‖scalarNormalizedPrimeEulerInverse p‖ ≤ (8 : ℝ) := by
  rw [scalarNormalizedPrimeEulerInverse]
  calc
    ‖((primeSchurMarkovScalar p : ℂ)⁻¹) •
        normalizedPrimeEulerInverse p‖ ≤
        ‖((primeSchurMarkovScalar p : ℂ)⁻¹)‖ *
          ‖normalizedPrimeEulerInverse p‖ :=
      ContinuousLinearMap.opNorm_smul_le _ _
    _ ≤ (8 : ℝ) * 1 := by
      exact mul_le_mul
        (norm_primeSchurMarkovScalar_inv_le_eight p)
        (norm_normalizedPrimeEulerInverse_le_one p)
        (norm_nonneg _) (by norm_num)
    _ = 8 := by norm_num

/-! ## Exact old/new range alignment -/

theorem oldFrameAdjoint_comp_inverseAdjoint_comp_newFrame_eq_reverseAdjoint
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    (suffixEulerFrameSchurStep lambda p S).oldFrame† ∘L
        (normalizedPrimeEulerInverse p)† ∘L
          (suffixEulerFrameSchurStep lambda p S).newFrame =
      (suffixEulerFrameReverseTransition lambda p S)† := by
  have hadjoint := congrArg ContinuousLinearMap.adjoint
    (normalizedPrimeEulerInverse_comp_oldFrame lambda p S)
  have hadjoint' :
      (suffixEulerFrameSchurStep lambda p S).oldFrame† ∘L
          (normalizedPrimeEulerInverse p)† =
        (suffixEulerFrameReverseTransition lambda p S)† ∘L
          (suffixEulerFrameSchurStep lambda p S).newFrame† := by
    simpa only [suffixEulerFrameSchurStep,
      ContinuousLinearMap.adjoint_comp] using hadjoint
  have hframe := (suffixEulerFrameSchurStep lambda p S).newFrame_isometry
  apply ContinuousLinearMap.ext
  intro x
  have hadjointPoint := congrArg
    (fun operator : finiteSCarrier →L[ℂ] sourceSoninCarrier lambda =>
      operator ((suffixEulerFrameSchurStep lambda p S).newFrame x)) hadjoint'
  have hframePoint := congrArg
    (fun operator : sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda =>
      operator x) hframe
  simp only [ContinuousLinearMap.comp_apply] at hadjointPoint hframePoint ⊢
  rw [hframePoint] at hadjointPoint
  simpa only [ContinuousLinearMap.comp_apply] using hadjointPoint

theorem oldFrameAdjoint_comp_scalarNormalizedInverseAdjoint_comp_newFrame_eq
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    (suffixEulerFrameSchurStep lambda p S).oldFrame† ∘L
        (scalarNormalizedPrimeEulerInverse p)† ∘L
          (suffixEulerFrameSchurStep lambda p S).newFrame =
      (primeSchurMarkovScalar p : ℂ)⁻¹ •
        (suffixEulerFrameReverseTransition lambda p S)† := by
  have hstar : star ((primeSchurMarkovScalar p : ℂ)⁻¹) =
      (primeSchurMarkovScalar p : ℂ)⁻¹ := by
    simp only [star_inv₀, Complex.star_def, Complex.conj_ofReal]
  have hadjoint := ContinuousLinearMap.adjoint.map_smulₛₗ
    ((primeSchurMarkovScalar p : ℂ)⁻¹)
    (normalizedPrimeEulerInverse p)
  have hscalarAdjoint :
      (scalarNormalizedPrimeEulerInverse p)† =
        (primeSchurMarkovScalar p : ℂ)⁻¹ •
          (normalizedPrimeEulerInverse p)† := by
    simpa only [scalarNormalizedPrimeEulerInverse, hstar,
      starRingEnd_apply] using hadjoint
  apply ContinuousLinearMap.ext
  intro x
  have hbase :=
    oldFrameAdjoint_comp_inverseAdjoint_comp_newFrame_eq_reverseAdjoint
      lambda p S
  rw [hscalarAdjoint]
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, map_smul]
  have hbasePoint := DFunLike.congr_fun hbase x
  simp only [ContinuousLinearMap.comp_apply] at hbasePoint
  rw [hbasePoint]

theorem oldFrameRow_comp_scalarNormalizedInverseAdjoint_comp_newFrame_eq
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime)
    (middle : sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda) :
    (middle ∘L (suffixEulerFrameSchurStep lambda p S).oldFrame†) ∘L
        (scalarNormalizedPrimeEulerInverse p)† ∘L
          (suffixEulerFrameSchurStep lambda p S).newFrame =
      (primeSchurMarkovScalar p : ℂ)⁻¹ •
        (middle ∘L (suffixEulerFrameReverseTransition lambda p S)†) := by
  have hbase :=
    oldFrameAdjoint_comp_scalarNormalizedInverseAdjoint_comp_newFrame_eq
      lambda p S
  apply ContinuousLinearMap.ext
  intro x
  have hpoint := DFunLike.congr_fun hbase x
  simpa only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, map_smul] using congrArg middle hpoint

/-! ## The actual hard-row pullback -/

noncomputable def suffixActualBandRawPhysicalOldCarrierHardMiddle
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) : SourceOp lambda :=
  let detectorLeg : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier :=
    suffixActualBandRawCoframeBoundaryDetectorLeg owner lambda
  let metric := frameMetricCoframe lambda S
  let left : SourceOp lambda :=
    metric† ∘L detectorLeg ∘L frameTransitionAdjoint lambda p S
  let right : SourceOp lambda :=
    frameTransitionAdjoint lambda p S ∘L
      suffixEulerFrameTransition lambda p S ∘L metric† ∘L detectorLeg
  let residual : SourceOp lambda :=
    frameTransitionAdjoint lambda p S ∘L
      suffixActualBandMetricCoframeAdjointOrientationGap lambda p S ∘L
        detectorLeg
  left - right - residual

theorem suffixActualBandRawPhysicalOldCarrierHardRow_eq_hardMiddle_comp_oldFrameAdjoint
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandRawPhysicalOldCarrierHardRow owner lambda p S =
      suffixActualBandRawPhysicalOldCarrierHardMiddle owner lambda p S ∘L
        frameOldFrameAdjoint lambda p S := by
  rw [suffixActualBandRawPhysicalOldCarrierHardRow,
    suffixActualBandRawPhysicalOldCarrierMetricOrientationRow,
    suffixActualBandRawPhysicalOldCarrierMetricResidualRow,
    suffixActualBandRawPhysicalOldCarrierHardMiddle]
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.neg_apply, map_sub]
  abel

theorem suffixActualBandRawPhysicalOldCarrierHardRow_comp_scalarNormalizedInverseAdjoint_comp_newFrame_eq
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandRawPhysicalOldCarrierHardRow owner lambda p S ∘L
        (scalarNormalizedPrimeEulerInverse p)† ∘L
          (suffixEulerFrameSchurStep lambda p S).newFrame =
      (primeSchurMarkovScalar p : ℂ)⁻¹ •
        (suffixActualBandRawPhysicalOldCarrierHardMiddle owner lambda p S ∘L
          (suffixEulerFrameReverseTransition lambda p S)†) := by
  rw [suffixActualBandRawPhysicalOldCarrierHardRow_eq_hardMiddle_comp_oldFrameAdjoint]
  exact oldFrameRow_comp_scalarNormalizedInverseAdjoint_comp_newFrame_eq
    lambda p S (suffixActualBandRawPhysicalOldCarrierHardMiddle owner lambda p S)

/-!
The named boundary remainder has an exact scalar-normalized pullback.  This
is the range test which a source producer must annihilate before the generic
boundary factorization can be used; no zero conclusion is made here.
-/
theorem coframeHardBoundaryRow_comp_scalarNormalizedInverseAdjoint_comp_newFrame_eq
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    coframeHardBoundaryRow owner lambda p S ∘L
        (scalarNormalizedPrimeEulerInverse p)† ∘L
          (suffixEulerFrameSchurStep lambda p S).newFrame =
      -((primeSchurMarkovScalar p : ℂ)⁻¹) •
        (frameTransitionAdjoint lambda p S ∘L
          (frameMetricCoframe lambda (p :: S))† ∘L
            suffixActualBandRawCoframeBoundaryDetectorLeg owner lambda ∘L
              (suffixEulerFrameReverseTransition lambda p S)†) := by
  unfold coframeHardBoundaryRow
  have hrow :=
    oldFrameRow_comp_scalarNormalizedInverseAdjoint_comp_newFrame_eq
      lambda p S
      (frameTransitionAdjoint lambda p S ∘L
        (frameMetricCoframe lambda (p :: S))† ∘L
          suffixActualBandRawCoframeBoundaryDetectorLeg owner lambda)
  apply ContinuousLinearMap.ext
  intro x
  have hpoint := DFunLike.congr_fun hrow x
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply,
    frameOldFrameAdjoint] at hpoint ⊢
  have hneg := congrArg (fun z => -z) hpoint
  simpa only [neg_smul] using hneg

/-! ## Source-facing row adapter -/

noncomputable def rowReadoutData_of_scalarRangeAnnihilation
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime}
    (row : finiteSCarrier →L[ℂ] sourceSoninCarrier lambda)
    (rowBound inverseBound : ℝ)
    (hrow_nonneg : 0 ≤ rowBound)
    (hinverse_nonneg : 0 ≤ inverseBound)
    (hrow : ‖row‖ ≤ rowBound)
    (hinverse : ‖scalarNormalizedPrimeEulerInverse p‖ ≤ inverseBound)
    (hannihilate :
      row ∘L (scalarNormalizedPrimeEulerInverse p)† ∘L
          (suffixEulerFrameSchurStep lambda p S).newFrame = 0) :
    SuffixRawOldCarrierCoframeRowReadoutData owner lambda p S row
      (rowBound * inverseBound) := by
  let frame := (suffixEulerFrameSchurStep lambda p S).newFrame
  let inverse := scalarNormalizedPrimeEulerInverse p
  let factor := rangeFactor row inverse frame
  let readout := ambientDifferencePlusBoundaryReadout p 0 factor
  have hframe : ContinuousLinearMap.adjoint frame ∘L frame =
      ContinuousLinearMap.id ℂ (sourceSoninCarrier lambda) := by
    simpa only [frame] using
      (suffixEulerFrameSchurStep lambda p S).newFrame_isometry
  have htransport :
      (suffixEulerFrameSchurStep lambda p S).transport ∘L inverse =
        ContinuousLinearMap.id ℂ finiteSCarrier := by
    simpa only [inverse, suffixEulerFrameSchurStep] using
      normalizedPrimeEulerFrameTransport_comp_scalarNormalizedInverse p
  have hannihilate' : row ∘L ContinuousLinearMap.adjoint inverse ∘L frame = 0 := by
    simpa only [inverse, frame] using hannihilate
  have hfactor :
      factor ∘L
          (ContinuousLinearMap.id ℂ finiteSCarrier -
            frame ∘L ContinuousLinearMap.adjoint frame) ∘L
        ContinuousLinearMap.adjoint
          (suffixEulerFrameSchurStep lambda p S).transport = row := by
    exact rangeFactor_comp_complement_comp_transportAdjoint_eq
      row (suffixEulerFrameSchurStep lambda p S).transport inverse frame
      hframe htransport hannihilate'
  have hfactor_norm : ‖factor‖ ≤ rowBound * inverseBound := by
    exact rangeFactor_norm_le row inverse frame rowBound inverseBound
      hframe hrow hinverse hrow_nonneg hinverse_nonneg
  refine
    { bound_nonneg := mul_nonneg hrow_nonneg hinverse_nonneg
      readout := readout
      readout_norm_le := ?_
      factorization := ?_ }
  · dsimp [readout]
    calc
      ‖ambientDifferencePlusBoundaryReadout p 0 factor‖ ≤
          ‖(Real.sqrt (ccm24PrimeEulerCoefficient p) : ℂ)‖ *
              ‖(0 : finiteSCarrier →L[ℂ] sourceSoninCarrier lambda)‖ +
            ‖factor‖ :=
        ambientDifferencePlusBoundaryReadout_norm_le p 0 factor
      _ ≤ rowBound * inverseBound := by
        calc
          ‖(Real.sqrt (ccm24PrimeEulerCoefficient p) : ℂ)‖ *
                ‖(0 : finiteSCarrier →L[ℂ] sourceSoninCarrier lambda)‖ +
              ‖factor‖ = ‖factor‖ := by
            have hzero :
                ‖(0 : finiteSCarrier →L[ℂ] sourceSoninCarrier lambda)‖ = 0 :=
              ContinuousLinearMap.opNorm_zero
            rw [hzero, mul_zero, zero_add]
          _ ≤ rowBound * inverseBound := hfactor_norm
  · dsimp [readout]
    calc
      ambientDifferencePlusBoundaryReadout p 0 factor ∘L
          suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S =
        (0 : finiteSCarrier →L[ℂ] sourceSoninCarrier lambda) ∘L
              (normalizedPrimeEulerFrameTransport p)† - 0 +
          factor ∘L
            ((ContinuousLinearMap.id ℂ finiteSCarrier -
                (suffixEulerFrameSchurStep lambda p S).newFrame ∘L
                  ContinuousLinearMap.adjoint
                    (suffixEulerFrameSchurStep lambda p S).newFrame) ∘L
              ContinuousLinearMap.adjoint
                (suffixEulerFrameSchurStep lambda p S).transport) :=
        ambientDifferencePlusBoundaryReadout_comp_oldCarrierAnalysis_eq
          p S 0 factor
      _ = row := by
        apply ContinuousLinearMap.ext
        intro x
        have hzero :
            (0 : finiteSCarrier →L[ℂ] sourceSoninCarrier lambda) ∘L
                (normalizedPrimeEulerFrameTransport p)† - 0 = 0 := by
          apply ContinuousLinearMap.ext
          intro y
          simp
        rw [hzero, zero_add]
        have hpoint := congrArg
          (fun operator : finiteSCarrier →L[ℂ]
              sourceSoninCarrier lambda => operator x) hfactor
        simpa only [ContinuousLinearMap.comp_apply] using hpoint

end CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeScalarRightInverse
end CCM25Concrete
end Source
end ConnesWeilRH
