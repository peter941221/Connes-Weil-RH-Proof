/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSActualSchurTelescoping

/-!
# Source-forward actual Schur transport

The actual Schur step has the source-forward orientation

```text
T_p * F_(p::S) = F_S * U_(p,S).
```

Its natural chronological product therefore appends the current factor on the
right, unlike the Julia survivor product used by the endpoint-facing adjoint
telescope.  This module owns that forward product and proves its exact frame
intertwining and contraction bound.  It does not identify the resulting dual
coframe with the physical endpoint.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSActualSchurForwardTransport

open scoped InnerProduct

open CC20Concrete
open _root_.ConnesWeilRH.CC20Concrete
open CCM24FiniteSActualJuliaInput
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSJuliaCausal
open CCM24FiniteSProjectionTrace
open CCM24FiniteSActualSchurTelescoping
open CCM24FiniteSFixedSourcePolar

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace
      (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! ## Source-forward products -/

/-- The ambient actual Schur product in source-forward order. -/
noncomputable def suffixActualSchurForwardAmbientProduct
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S) :
    List CCM24VisiblePrime → finiteSCarrier →L[ℂ] finiteSCarrier
  | [] => ContinuousLinearMap.id ℂ finiteSCarrier
  | p :: S =>
      suffixActualSchurForwardAmbientProduct lambda stepData S ∘L
        (suffixActualSchurFrameStep lambda stepData p S).transport

/-- The source transition product in the same source-forward order. -/
noncomputable def suffixActualSchurForwardTransitionProduct
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S) :
    List CCM24VisiblePrime →
      sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda
  | [] => ContinuousLinearMap.id ℂ (sourceSoninCarrier lambda)
  | p :: S =>
      suffixActualSchurForwardTransitionProduct lambda stepData S ∘L
        (suffixActualSchurFrameStep lambda stepData p S).transition

/-! ## Exact source-forward intertwining -/

theorem suffixActualSchurForwardAmbientProduct_comp_terminalPolarFrame
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (S : List CCM24VisiblePrime) :
    suffixActualSchurForwardAmbientProduct lambda stepData S ∘L
        newSuffixFrame lambda S =
      newSuffixFrame lambda [] ∘L
        suffixActualSchurForwardTransitionProduct lambda stepData S := by
  induction S with
  | nil =>
      apply ContinuousLinearMap.ext
      intro x
      rfl
  | cons p S ih =>
      let step := suffixActualSchurFrameStep lambda stepData p S
      have hstep : step.transport ∘L step.newFrame =
          step.oldFrame ∘L step.transition :=
        step.transport_intertwining
      apply ContinuousLinearMap.ext
      intro x
      have ihPoint := congrArg
        (fun operator : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier =>
          operator (step.transition x)) ih
      simp only [suffixActualSchurForwardAmbientProduct,
        suffixActualSchurForwardTransitionProduct,
        ContinuousLinearMap.comp_apply] at ⊢
      change (suffixActualSchurForwardAmbientProduct lambda stepData S)
          (step.transport (step.newFrame x)) =
        newSuffixFrame lambda []
          ((suffixActualSchurForwardTransitionProduct lambda stepData S)
            (step.transition x))
      rw [show step.transport (step.newFrame x) =
          step.oldFrame (step.transition x) by
        simpa only [ContinuousLinearMap.comp_apply] using
          congrArg
            (fun operator : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier =>
              operator x) hstep]
      have ihPoint' :
          (suffixActualSchurForwardAmbientProduct lambda stepData S)
              (step.oldFrame (step.transition x)) =
            newSuffixFrame lambda []
              ((suffixActualSchurForwardTransitionProduct lambda stepData S)
                (step.transition x)) := by
        simpa only [step, suffixActualSchurFrameStep, newSuffixFrame] using
          ihPoint
      exact ihPoint'

/-! ## Uniform contraction -/

theorem suffixActualSchurForwardAmbientProduct_norm_le_one
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (S : List CCM24VisiblePrime) :
    ‖suffixActualSchurForwardAmbientProduct lambda stepData S‖ ≤ 1 := by
  induction S with
  | nil =>
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro x
      simp only [suffixActualSchurForwardAmbientProduct,
        ContinuousLinearMap.id_apply, one_mul, le_refl]
  | cons p S ih =>
      have hstep :=
        (suffixActualSchurFrameStep lambda stepData p S).transport_norm_le_one
      calc
        ‖suffixActualSchurForwardAmbientProduct lambda stepData (p :: S)‖ ≤
            ‖suffixActualSchurForwardAmbientProduct lambda stepData S‖ *
              ‖(suffixActualSchurFrameStep lambda stepData p S).transport‖ := by
          simp only [suffixActualSchurForwardAmbientProduct]
          exact ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ 1 * 1 := by gcongr
        _ = 1 := by norm_num

/-- The dual of the source-forward transport, based at the empty polar frame.
Its norm is uniformly at most one for every finite suffix. -/
noncomputable def suffixActualSchurForwardDualCoframe
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (S : List CCM24VisiblePrime) :
    sourceSoninCarrier lambda →L[ℂ] finiteSCarrier :=
  (suffixActualSchurForwardAmbientProduct lambda stepData S)† ∘L
    newSuffixFrame lambda []

theorem suffixActualSchurForwardDualCoframe_norm_le_one
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (S : List CCM24VisiblePrime) :
    ‖suffixActualSchurForwardDualCoframe lambda stepData S‖ ≤ 1 := by
  have hambient :
      ‖suffixActualSchurForwardAmbientProduct lambda stepData S‖ ≤ 1 :=
    suffixActualSchurForwardAmbientProduct_norm_le_one lambda stepData S
  have hframe : ‖newSuffixFrame lambda []‖ ≤ 1 :=
    norm_le_one_of_isometric_inclusion (newSuffixFrame lambda []) (by
      intro x
      exact parameterizedSoninPolarFrame_isometry lambda 1 []
        (by norm_num) x)
  unfold suffixActualSchurForwardDualCoframe
  calc
    ‖(suffixActualSchurForwardAmbientProduct lambda stepData S)† ∘L
          newSuffixFrame lambda []‖ ≤
        ‖(suffixActualSchurForwardAmbientProduct lambda stepData S)†‖ *
          ‖newSuffixFrame lambda []‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ = ‖suffixActualSchurForwardAmbientProduct lambda stepData S‖ *
          ‖newSuffixFrame lambda []‖ := by
      rw [ContinuousLinearMap.adjoint.norm_map]
    _ ≤ 1 * 1 := by gcongr
    _ = 1 := by norm_num

end CCM24FiniteSActualSchurForwardTransport
end CCM25Concrete
end Source
end ConnesWeilRH
