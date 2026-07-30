/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawCoDefectFactor
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierBlockReduction
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierSpectralGap

/-!
# Raw co-defect factors on the old carrier

The old-carrier reduction and the actual Julia co-defect are the same signed
energy ledger.  This file records the exact transfer in the direction used by
Bone 1:

```text
rawDefect = leftCoDefect * rightFactor
                 |
                 v
R0 = bounded readout * W
```

The proof uses the old-frame/complement orthogonal split.  It never estimates
the four raw summands separately and it does not introduce a spectral gap.
The source-specific factor `rightFactor` remains an explicit premise.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoDefectBridge

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCompletedJuliaAmbientDefectFactorization
open CCM24FiniteSCompletedJuliaMismatchFactorization
open CCM24FiniteSCompletedJuliaRawCoDefectFactor
open CCM24FiniteSCompletedJuliaRawPhysicalFactorization
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierBlockReduction
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierReduction
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierSpectralGap
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSJuliaBessel
open CCM24FiniteSJuliaCoDefect
open CCM24FiniteSProjectionTrace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! ## The source-side factor readback -/

set_option maxHeartbeats 4000000 in
-- The old-frame split and adjoint readback require a larger elaboration budget.
theorem SuffixRawCoDefectFactorData.toOldCarrierDomination
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {bound : ℝ}
    (data : SuffixRawCoDefectFactorData owner lambda p S bound) :
    SuffixRawOldCarrierDomination owner lambda p S bound := by
  have hbound : 0 ≤ bound :=
    le_trans (norm_nonneg data.rightFactor) data.rightFactor_norm_le
  let step := suffixEulerFrameSchurStep lambda p S
  let oldFrame := step.oldFrame
  let oldProjection : finiteSCarrier →L[ℂ] finiteSCarrier :=
    oldFrame ∘L ContinuousLinearMap.adjoint oldFrame
  let oldComplement : finiteSCarrier →L[ℂ] finiteSCarrier :=
    ContinuousLinearMap.id ℂ finiteSCarrier - oldProjection
  have hySplit : ∀ y : finiteSCarrier,
      y = oldProjection y + oldComplement y := by
    intro y
    dsimp [oldComplement]
    simp
  have hrowComplement : ∀ y : finiteSCarrier,
      suffixActualBandRawPhysicalReducedRow owner lambda p S
          (oldComplement y) = 0 := by
    intro y
    dsimp [oldComplement, oldProjection, step, oldFrame]
    simp only [suffixActualBandRawPhysicalReducedRow,
      ContinuousLinearMap.comp_apply, map_sub]
    have hframe :=
      (suffixEulerFrameSchurStep lambda p S).oldFrame_isometry
    have hframePoint := congrArg
      (fun T : sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda =>
        T (ContinuousLinearMap.adjoint
          (suffixEulerFrameSchurStep lambda p S).oldFrame y)) hframe
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] at hframePoint
    rw [hframePoint]
    simp
  have hrowProjection : ∀ y : finiteSCarrier,
      suffixActualBandRawPhysicalReducedRow owner lambda p S
          (oldProjection y) =
        suffixActualBandRawPhysicalFourTermRow owner lambda p S
          (ContinuousLinearMap.adjoint oldFrame y) := by
    intro y
    dsimp [oldProjection]
    have hrow :=
      congrArg
        (fun T : sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda =>
          T (ContinuousLinearMap.adjoint oldFrame y))
        (suffixActualBandRawPhysicalFourTermRow_eq_reducedRow_comp_oldFrame
          owner lambda p S)
    simpa only [oldFrame, step, ContinuousLinearMap.comp_apply] using hrow.symm
  have hrawFactorization :
      (suffixActualBandRawQuadraticIntertwiningDefect owner lambda p S)† =
        (ContinuousLinearMap.adjoint data.rightFactor) ∘L step.leftCoDefect := by
    have hadjoint := congrArg ContinuousLinearMap.adjoint data.factorization
    have hself : IsSelfAdjoint step.leftCoDefect := by
      simpa only [step, RectangularSchurCoDefectStepData.leftCoDefect] using
        (canonicalJuliaDefect_isSelfAdjoint
          (ContinuousLinearMap.adjoint step.transition)
          step.transitionAdjointContract)
    simpa only [step, ContinuousLinearMap.adjoint_comp, hself.adjoint_eq] using
      hadjoint
  have hrawPoint : ∀ y : finiteSCarrier,
      ‖suffixActualBandRawPhysicalReducedRow owner lambda p S y‖ ^ 2 ≤
        bound ^ 2 *
          ‖step.leftCoDefect (ContinuousLinearMap.adjoint oldFrame y)‖ ^ 2 := by
    intro y
    have hrow :
        suffixActualBandRawPhysicalReducedRow owner lambda p S y =
          suffixActualBandRawPhysicalFourTermRow owner lambda p S
            (ContinuousLinearMap.adjoint oldFrame y) := by
      calc
        suffixActualBandRawPhysicalReducedRow owner lambda p S y =
            suffixActualBandRawPhysicalReducedRow owner lambda p S
              (oldProjection y + oldComplement y) := by
          exact congrArg
            (fun z : finiteSCarrier =>
              suffixActualBandRawPhysicalReducedRow owner lambda p S z)
            (hySplit y)
        _ = suffixActualBandRawPhysicalReducedRow owner lambda p S
              (oldProjection y) +
            suffixActualBandRawPhysicalReducedRow owner lambda p S
              (oldComplement y) := by rw [map_add]
        _ = suffixActualBandRawPhysicalFourTermRow owner lambda p S
              (ContinuousLinearMap.adjoint oldFrame y) := by
          rw [hrowProjection y, hrowComplement y, add_zero]
    have hfactorPoint := congrArg
      (fun T : sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda =>
        T (ContinuousLinearMap.adjoint oldFrame y)) hrawFactorization
    have hnorm :
        ‖suffixActualBandRawPhysicalFourTermRow owner lambda p S
            (ContinuousLinearMap.adjoint oldFrame y)‖ ≤
          bound * ‖step.leftCoDefect
            (ContinuousLinearMap.adjoint oldFrame y)‖ := by
      rw [← suffixActualBandRawQuadraticIntertwiningDefect_adjoint_eq_fourTermRow
        owner lambda p S]
      rw [show
          ((suffixActualBandRawQuadraticIntertwiningDefect owner lambda p S)†)
              (ContinuousLinearMap.adjoint oldFrame y) =
            (ContinuousLinearMap.adjoint data.rightFactor)
              (step.leftCoDefect (ContinuousLinearMap.adjoint oldFrame y)) by
        simpa only [ContinuousLinearMap.comp_apply] using hfactorPoint]
      calc
        ‖(ContinuousLinearMap.adjoint data.rightFactor)
            (step.leftCoDefect (ContinuousLinearMap.adjoint oldFrame y))‖ ≤
            ‖ContinuousLinearMap.adjoint data.rightFactor‖ *
              ‖step.leftCoDefect (ContinuousLinearMap.adjoint oldFrame y)‖ :=
          (ContinuousLinearMap.adjoint data.rightFactor).le_opNorm _
        _ = ‖data.rightFactor‖ *
              ‖step.leftCoDefect (ContinuousLinearMap.adjoint oldFrame y)‖ := by
          exact congrArg
            (fun value : ℝ => value *
              ‖step.leftCoDefect (ContinuousLinearMap.adjoint oldFrame y)‖)
            (ContinuousLinearMap.adjoint.norm_map data.rightFactor)
        _ ≤ bound *
              ‖step.leftCoDefect (ContinuousLinearMap.adjoint oldFrame y)‖ :=
          mul_le_mul_of_nonneg_right data.rightFactor_norm_le
            (norm_nonneg _)
    rw [hrow]
    exact (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg hbound (norm_nonneg _))).mpr hnorm |>.trans_eq (by
        rw [mul_pow])
  refine ⟨hbound, ?_⟩
  intro y
  have henergy :=
    oldCarrierAnalysis_normSq_eq_oldFrame_part_add_complement_part
      lambda p S y
  have holdTerm :
      ‖suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S
          (oldFrame (ContinuousLinearMap.adjoint oldFrame y))‖ ^ 2 =
        ‖step.leftCoDefect (ContinuousLinearMap.adjoint oldFrame y)‖ ^ 2 := by
    have hanalysis :=
      congrArg
        (fun T : sourceSoninCarrier lambda →L[ℂ]
            suffixEulerFrameAmbientBoundaryCarrier =>
          T (ContinuousLinearMap.adjoint oldFrame y))
        (suffixEulerFrameAmbientBoundaryAnalysis_eq_oldCarrier_comp_oldFrame
          lambda p S)
    calc
      ‖suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S
          (oldFrame (ContinuousLinearMap.adjoint oldFrame y))‖ ^ 2 =
          ‖suffixEulerFrameAmbientBoundaryAnalysis lambda p S
              (ContinuousLinearMap.adjoint oldFrame y)‖ ^ 2 := by
        simpa only [ContinuousLinearMap.comp_apply] using
          congrArg (fun z : suffixEulerFrameAmbientBoundaryCarrier => ‖z‖ ^ 2)
            hanalysis.symm
      _ = ‖step.leftCoDefect
          (ContinuousLinearMap.adjoint oldFrame y)‖ ^ 2 := by
        exact suffixEulerFrameAmbientBoundaryAnalysis_normSq_eq_leftCoDefect
          lambda p S _
  have hdefect_le_analysis :
      ‖step.leftCoDefect (ContinuousLinearMap.adjoint oldFrame y)‖ ^ 2 ≤
        ‖suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S y‖ ^ 2 := by
    rw [← holdTerm]
    rw [henergy]
    exact le_add_of_nonneg_right (sq_nonneg _)
  calc
    ‖suffixActualBandRawPhysicalReducedRow owner lambda p S y‖ ^ 2 ≤
        bound ^ 2 *
          ‖step.leftCoDefect (ContinuousLinearMap.adjoint oldFrame y)‖ ^ 2 :=
      hrawPoint y
    _ ≤ bound ^ 2 *
          ‖suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S y‖ ^ 2 := by
      exact mul_le_mul_of_nonneg_left hdefect_le_analysis (sq_nonneg bound)

theorem SuffixRawCoDefectUniformFactorData.toOldCarrierUniformDomination
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {bound : ℝ}
    (data : SuffixRawCoDefectUniformFactorData owner lambda bound) :
    Nonempty (SuffixRawOldCarrierUniformDominationData owner lambda bound) := by
  refine ⟨{ bound_nonneg := data.bound_nonneg
            domination := fun p S =>
              SuffixRawCoDefectFactorData.toOldCarrierDomination
                (data.factor p S) }⟩

end CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoDefectBridge
end CCM25Concrete
end Source
end ConnesWeilRH
