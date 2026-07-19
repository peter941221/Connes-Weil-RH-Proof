/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.ConjSqrt
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.InnerProductSpace.StarOrder
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSActualJuliaInput
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSGramInverseCalculus

/-!
# Fixed-source polar frame for the actual finite-S Julia input

The chronological suffixes have different moving Sonin subtype carriers.  The
restricted Euler frame has the same source carrier at every suffix, but is only
boundedly invertible.  This module applies its positive polar correction

```text
V = A (A† A)^(-1/2)
```

and proves that `V` is an isometric frame with exactly the same range as `A`.
The resulting adapter turns the existing suffix-indexed Schur data into a
fixed-source `CurrentRangeJuliaStepData`.  No physical boundary identity is
inferred here; the readback theorem keeps that identity explicit.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSFixedSourcePolar

open CC20Concrete
open _root_.ConnesWeilRH.CC20Concrete
open CCM24FiniteSActualJuliaInput
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSGramInverseCalculus
open CCM24FiniteSJuliaBessel
open CCM24FiniteSJuliaCausal
open CCM24FiniteSParameterizedEulerEquiv
open CCM24FiniteSParameterizedSoninProjection
open CCM24FiniteSParameterizedSoninSubspace
open CCM24FiniteSProjectionTrace
open scoped InnerProduct

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

noncomputable local instance transportedSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    CompleteSpace
      ((transportedClosedSubmodule
        (parameterizedFiniteEulerEquiv alpha S halpha)
        (ccm24ArchimedeanSoninClosedSubspace lambda)).toSubmodule) :=
    (transportedClosedSubmodule
    (parameterizedFiniteEulerEquiv alpha S halpha)
    (ccm24ArchimedeanSoninClosedSubspace lambda)).isClosed.completeSpace_coe

noncomputable local instance sourceSoninOperatorComplexCFC
    (lambda : CCM24SoninScale) :
    ContinuousFunctionalCalculus ℂ
      ((sourceSoninCarrier lambda) →L[ℂ] (sourceSoninCarrier lambda))
      IsStarNormal := by
  letI : CompleteSpace (sourceSoninCarrier lambda) :=
    sourceSoninCarrierCompleteSpace lambda
  letI : CStarAlgebra
      ((sourceSoninCarrier lambda) →L[ℂ] (sourceSoninCarrier lambda)) :=
    inferInstance
  exact IsStarNormal.instContinuousFunctionalCalculus

noncomputable local instance sourceSoninOperatorNonUnitalComplexCFC
    (lambda : CCM24SoninScale) :
    NonUnitalClosedEmbeddingContinuousFunctionalCalculus ℂ
      ((sourceSoninCarrier lambda) →L[ℂ] (sourceSoninCarrier lambda))
      IsStarNormal := by
  letI : CompleteSpace (sourceSoninCarrier lambda) :=
    sourceSoninCarrierCompleteSpace lambda
  letI : CStarAlgebra
      ((sourceSoninCarrier lambda) →L[ℂ] (sourceSoninCarrier lambda)) :=
    inferInstance
  exact IsStarNormal.instNonUnitalContinuousFunctionalCalculus

noncomputable local instance sourceSoninOperatorRealCFC
    (lambda : CCM24SoninScale) :
    ContinuousFunctionalCalculus ℝ
      ((sourceSoninCarrier lambda) →L[ℂ] (sourceSoninCarrier lambda))
      IsSelfAdjoint := by
  letI : ContinuousFunctionalCalculus ℂ
      ((sourceSoninCarrier lambda) →L[ℂ] (sourceSoninCarrier lambda))
      IsStarNormal := sourceSoninOperatorComplexCFC lambda
  exact IsSelfAdjoint.instContinuousFunctionalCalculus

noncomputable local instance sourceSoninOperatorNonUnitalRealCFC
    (lambda : CCM24SoninScale) :
    NonUnitalContinuousFunctionalCalculus ℝ
      ((sourceSoninCarrier lambda) →L[ℂ] (sourceSoninCarrier lambda))
      IsSelfAdjoint := by
  letI : NonUnitalContinuousFunctionalCalculus ℂ
      ((sourceSoninCarrier lambda) →L[ℂ] (sourceSoninCarrier lambda))
      IsStarNormal :=
    (sourceSoninOperatorNonUnitalComplexCFC lambda).toNonUnitalContinuousFunctionalCalculus
  exact IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus

/-! The restricted Gram and its inverse are positive operators. -/

theorem parameterizedSoninGram_nonneg
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) :
    (0 : sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda) ≤
      parameterizedSoninGram lambda alpha S := by
  apply (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
  simpa only [parameterizedSoninGram] using
    (ContinuousLinearMap.isPositive_adjoint_comp_self
      (parameterizedSoninFrame lambda alpha S))

theorem parameterizedSoninGramInv_nonneg
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    (0 : sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda) ≤
      parameterizedSoninGramInv lambda alpha S halpha := by
  apply (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
  simpa only [parameterizedSoninGramInv, restrictedTransportGramInv] using
    (ContinuousLinearMap.isPositive_self_comp_adjoint
      (restrictedClosedTransportInverse
        (parameterizedFiniteEulerEquiv alpha S halpha)
        (ccm24ArchimedeanSoninClosedSubspace lambda)))

theorem parameterizedSoninGram_isUnit
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    IsUnit (parameterizedSoninGram lambda alpha S) := by
  refine isUnit_iff_exists.mpr
    ⟨parameterizedSoninGramInv lambda alpha S halpha, ?_, ?_⟩
  · exact parameterizedSoninGram_mul_gramInv lambda alpha S halpha
  · exact parameterizedSoninGramInv_mul_gram lambda alpha S halpha

theorem parameterizedSoninGramInv_isUnit
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    IsUnit (parameterizedSoninGramInv lambda alpha S halpha) := by
  refine isUnit_iff_exists.mpr
    ⟨parameterizedSoninGram lambda alpha S, ?_, ?_⟩
  · exact parameterizedSoninGramInv_mul_gram lambda alpha S halpha
  · exact parameterizedSoninGram_mul_gramInv lambda alpha S halpha

theorem parameterizedSoninGram_isStrictlyPositive
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    IsStrictlyPositive (parameterizedSoninGram lambda alpha S) := by
  letI : CompleteSpace (sourceSoninCarrier lambda) :=
    sourceSoninCarrierCompleteSpace lambda
  have hiff :
      IsStrictlyPositive (parameterizedSoninGram lambda alpha S) ↔
        (0 : sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda) ≤
            parameterizedSoninGram lambda alpha S ∧
          IsUnit (parameterizedSoninGram lambda alpha S) :=
    CStarAlgebra.isStrictlyPositive_TFAE.out 0 7
  exact hiff.mpr
    ⟨parameterizedSoninGram_nonneg lambda alpha S,
      parameterizedSoninGram_isUnit lambda alpha S halpha⟩

/-! The positive square root of the inverse Gram operator. -/

noncomputable def parameterizedSoninGramInvSqrt
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
  letI : CompleteSpace (sourceSoninCarrier lambda) :=
    sourceSoninCarrierCompleteSpace lambda
  CFC.sqrt (parameterizedSoninGramInv lambda alpha S halpha)

theorem parameterizedSoninGramInvSqrt_isSelfAdjoint
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    IsSelfAdjoint (parameterizedSoninGramInvSqrt lambda alpha S halpha) := by
  letI : CompleteSpace (sourceSoninCarrier lambda) :=
    sourceSoninCarrierCompleteSpace lambda
  have hnonneg :
      (0 : sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda) ≤
        parameterizedSoninGramInvSqrt lambda alpha S halpha := by
    exact CFC.sqrt_nonneg _
  exact (ContinuousLinearMap.nonneg_iff_isPositive _).mp hnonneg |>.isSelfAdjoint

theorem parameterizedSoninGramInvSqrt_isUnit
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    IsUnit (parameterizedSoninGramInvSqrt lambda alpha S halpha) := by
  letI : CompleteSpace (sourceSoninCarrier lambda) :=
    sourceSoninCarrierCompleteSpace lambda
  exact (CFC.isUnit_sqrt_iff _
    (parameterizedSoninGramInv_nonneg lambda alpha S halpha)).mpr
    (parameterizedSoninGramInv_isUnit lambda alpha S halpha)

theorem parameterizedSoninGramInvSqrt_mul_self
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    parameterizedSoninGramInvSqrt lambda alpha S halpha ∘L
        parameterizedSoninGramInvSqrt lambda alpha S halpha =
      parameterizedSoninGramInv lambda alpha S halpha := by
  letI : CompleteSpace (sourceSoninCarrier lambda) :=
    sourceSoninCarrierCompleteSpace lambda
  rw [← ContinuousLinearMap.mul_def]
  exact CFC.sqrt_mul_sqrt_self _
    (parameterizedSoninGramInv_nonneg lambda alpha S halpha)

theorem parameterizedSoninGramInvSqrt_gram_mul
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    parameterizedSoninGramInvSqrt lambda alpha S halpha ∘L
        parameterizedSoninGram lambda alpha S ∘L
        parameterizedSoninGramInvSqrt lambda alpha S halpha =
      ContinuousLinearMap.id ℂ (sourceSoninCarrier lambda) := by
  letI : CompleteSpace (sourceSoninCarrier lambda) :=
    sourceSoninCarrierCompleteSpace lambda
  have h := CFC.conjSqrt_ringInverse_self
    (parameterizedSoninGram lambda alpha S)
    (parameterizedSoninGram_isStrictlyPositive lambda alpha S halpha)
  rw [CFC.conjSqrt_apply] at h
  rw [ringInverse_parameterizedSoninGram lambda alpha S halpha] at h
  simpa only [parameterizedSoninGramInvSqrt,
    ContinuousLinearMap.mul_def,
    ContinuousLinearMap.one_def] using h

/-! The actual polar frame and its range. -/

noncomputable def parameterizedSoninPolarFrame
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    sourceSoninCarrier lambda →L[ℂ] finiteSCarrier :=
  parameterizedSoninFrame lambda alpha S ∘L
    parameterizedSoninGramInvSqrt lambda alpha S halpha

theorem parameterizedSoninPolarFrame_adjoint_comp_self
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    (parameterizedSoninPolarFrame lambda alpha S halpha)† ∘L
        parameterizedSoninPolarFrame lambda alpha S halpha =
      ContinuousLinearMap.id ℂ (sourceSoninCarrier lambda) := by
  have hsqrt := parameterizedSoninGramInvSqrt_gram_mul
    lambda alpha S halpha
  have hself := parameterizedSoninGramInvSqrt_isSelfAdjoint
    lambda alpha S halpha
  simpa only [parameterizedSoninPolarFrame, parameterizedSoninGram,
    ContinuousLinearMap.adjoint_comp, hself.adjoint_eq,
    ContinuousLinearMap.comp_assoc] using hsqrt

theorem parameterizedSoninPolarFrame_isometry
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    ∀ x : sourceSoninCarrier lambda,
      ‖parameterizedSoninPolarFrame lambda alpha S halpha x‖ = ‖x‖ :=
  (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).mpr
    (parameterizedSoninPolarFrame_adjoint_comp_self lambda alpha S halpha)

theorem parameterizedSoninFrame_range
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    (parameterizedSoninFrame lambda alpha S).range =
      (parameterizedSoninClosedSubspace lambda alpha S halpha).toSubmodule := by
  rw [parameterizedSoninFrame_eq_restrictedClosedTransport
    lambda alpha S halpha]
  calc
    (restrictedClosedTransport
        (parameterizedFiniteEulerEquiv alpha S halpha)
        (ccm24ArchimedeanSoninClosedSubspace lambda)).range =
        (transportedClosedSubmodule
          (parameterizedFiniteEulerEquiv alpha S halpha)
          (ccm24ArchimedeanSoninClosedSubspace lambda)).toSubmodule :=
      restrictedClosedTransport_range
        (parameterizedFiniteEulerEquiv alpha S halpha)
        (ccm24ArchimedeanSoninClosedSubspace lambda)
    _ = (parameterizedSoninClosedSubspace lambda alpha S halpha).toSubmodule := by
      change
        (ClosedSubmodule.mapEquiv
          (parameterizedFiniteEulerEquiv alpha S halpha)
          (ccm24ArchimedeanSoninClosedSubspace lambda)).toSubmodule =
          (parameterizedSoninClosedSubspace lambda alpha S halpha).toSubmodule
      exact congrArg
        (fun P : ClosedSubmodule ℂ finiteSCarrier => P.toSubmodule)
        (parameterizedFiniteEulerEquiv_maps_sonin lambda alpha S halpha)

theorem parameterizedSoninPolarFrame_range
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    (parameterizedSoninPolarFrame lambda alpha S halpha).range =
      (parameterizedSoninClosedSubspace lambda alpha S halpha).toSubmodule := by
  have hunit := parameterizedSoninGramInvSqrt_isUnit lambda alpha S halpha
  obtain ⟨BInv, hleft, _⟩ := isUnit_iff_exists.mp hunit
  have hsurj : Function.Surjective
      (parameterizedSoninGramInvSqrt lambda alpha S halpha) := by
    intro x
    refine ⟨BInv x, ?_⟩
    have hx := congrArg
      (fun T : sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda => T x)
      hleft
    simpa only [ContinuousLinearMap.mul_def, ContinuousLinearMap.one_def,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using hx
  let A := parameterizedSoninFrame lambda alpha S
  let B := parameterizedSoninGramInvSqrt lambda alpha S halpha
  have hcomp : (A ∘L B).range = A.range := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      exact ⟨B x, rfl⟩
    · rintro _ ⟨x, rfl⟩
      obtain ⟨y, hy⟩ := hsurj x
      refine ⟨y, ?_⟩
      change A (B y) = A x
      rw [hy]
  calc
    (parameterizedSoninPolarFrame lambda alpha S halpha).range =
        (parameterizedSoninFrame lambda alpha S).range := by
      simpa only [parameterizedSoninPolarFrame, A, B] using hcomp
    _ = (parameterizedSoninClosedSubspace lambda alpha S halpha).toSubmodule :=
      parameterizedSoninFrame_range lambda alpha S halpha

/-!
The suffix Schur data now has a fixed-source realization.  Its current range
is still the actual moving Sonin subspace; only the coordinate carrier is
fixed.
-/

noncomputable def SuffixPrimeEulerProjectedJuliaSchurFrameStepData.toFixedSourceCurrentRangeStepData
    {lambda : CCM24SoninScale} {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {p : CCM24VisiblePrime} {S : List CCM24VisiblePrime}
    (data : SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S) :
    CurrentRangeJuliaStepData
      (sourceSoninCarrier lambda) finiteSCarrier G := by
  let range := parameterizedSoninClosedSubspace lambda 1 S (by norm_num)
  let input := parameterizedPrimeEulerProjectedJuliaInput lambda 1 S
    (by norm_num) p
  let frame := parameterizedSoninPolarFrame lambda 1 S (by norm_num)
  have hframe : ∀ x : sourceSoninCarrier lambda, ‖frame x‖ = ‖x‖ := by
    intro x
    exact parameterizedSoninPolarFrame_isometry lambda 1 S (by norm_num) x
  have hframe_range : frame.range = range.toSubmodule := by
    simpa only [frame, range] using
      parameterizedSoninPolarFrame_range lambda 1 S (by norm_num)
  have hnorm : ‖input.normalizedSchurFrame‖ ≤ 1 :=
    CCM24FiniteSJuliaCausal.norm_le_one_of_adjoint_comp_self_le_id
      input.normalizedSchurFrame
      data.transfer_contract
  refine
    { currentRange := range
      frame := frame
      frame_isometry := hframe
      frame_range := by
        intro y
        change y ∈ range.toSubmodule ↔ ∃ x, frame x = y
        rw [← hframe_range]
        rfl
      ambientTransfer := input.normalizedSchurFrame
      ambientTransfer_norm_le_one := hnorm
      ambientRangeSine := data.rangeSine
      weight := primeJuliaWeight p
      weight_nonneg := primeJuliaWeight_nonneg p
      rangeSine_weighted_le := ?_ }
  intro x
  have hdata := data.rangeSine_weighted_le (frame x)
  have hdef := canonicalJuliaDefect_comp_frame_normSq_le
    frame input.normalizedSchurFrame hframe hnorm x
  simpa only [input, frame, range] using hdata.trans hdef

theorem SuffixPrimeEulerProjectedJuliaSchurFrameStepData.fixedSource_rangeSine_readback
    {lambda : CCM24SoninScale} {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {p : CCM24VisiblePrime} {S : List CCM24VisiblePrime}
    (data : SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S) :
    data.rangeSine ∘L
        parameterizedSoninPolarFrame lambda 1 S (by norm_num) =
      data.readout ∘L
        (parameterizedPrimeEulerProjectedJuliaInput lambda 1 S
          (by norm_num) p).toColligation.graphSine
        (parameterizedPrimeEulerProjectedJuliaInput lambda 1 S
            (by norm_num) p).toColligation.graphCosine ∘L
        parameterizedSoninPolarFrame lambda 1 S (by norm_num) := by
  simpa only [ContinuousLinearMap.comp_assoc] using congrArg
    (fun A : finiteSCarrier →L[ℂ] G =>
      A ∘L parameterizedSoninPolarFrame lambda 1 S (by norm_num))
    data.rangeSine_readback

/-! Recursive fixed-source step schedules preserve the visible-prime length. -/

noncomputable def fixedSourceCurrentRangeJuliaSteps
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S) :
    List CCM24VisiblePrime → List (CurrentRangeJuliaStepData
      (sourceSoninCarrier lambda) finiteSCarrier G)
  | [] => []
  | p :: S =>
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData.toFixedSourceCurrentRangeStepData
          (stepData p S) ::
        fixedSourceCurrentRangeJuliaSteps lambda stepData S

@[simp]
theorem fixedSourceCurrentRangeJuliaSteps_nil
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S) :
    fixedSourceCurrentRangeJuliaSteps lambda stepData [] = [] :=
  rfl

@[simp]
theorem fixedSourceCurrentRangeJuliaSteps_cons
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime) :
    fixedSourceCurrentRangeJuliaSteps lambda stepData (p :: S) =
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData.toFixedSourceCurrentRangeStepData
          (stepData p S) ::
        fixedSourceCurrentRangeJuliaSteps lambda stepData S :=
  rfl

theorem fixedSourceCurrentRangeJuliaSteps_length
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (S : List CCM24VisiblePrime) :
    (fixedSourceCurrentRangeJuliaSteps lambda stepData S).length = S.length := by
  induction S with
  | nil => rfl
  | cons p S ih => simp [ih]

theorem fixedSourceCurrentRangeJuliaDefectSteps_length
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (S : List CCM24VisiblePrime) :
    (currentRangeJuliaSteps
      (fixedSourceCurrentRangeJuliaSteps lambda stepData S)).length = S.length := by
  simpa only [currentRangeJuliaSteps, List.length_map] using
    fixedSourceCurrentRangeJuliaSteps_length lambda stepData S

noncomputable def fixedSourceCurrentRangeJuliaReadouts
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S) :
    List CCM24VisiblePrime → List (G →L[ℂ] G)
  | [] => []
  | p :: S =>
      (stepData p S).fixedSourceReadout ::
        fixedSourceCurrentRangeJuliaReadouts lambda stepData S

theorem fixedSourceCurrentRangeJuliaReadouts_length
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (S : List CCM24VisiblePrime) :
    (fixedSourceCurrentRangeJuliaReadouts lambda stepData S).length = S.length := by
  induction S with
  | nil => rfl
  | cons p S ih =>
      simp only [fixedSourceCurrentRangeJuliaReadouts, List.length_cons]
      exact congrArg Nat.succ ih

noncomputable def fixedSourceCurrentRangeJuliaReadout
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (S : List CCM24VisiblePrime)
    (i : Fin (currentRangeJuliaSteps
      (fixedSourceCurrentRangeJuliaSteps lambda stepData S)).length) :
    G →L[ℂ] G :=
  (fixedSourceCurrentRangeJuliaReadouts lambda stepData S).get
    (Fin.cast (by
      exact (fixedSourceCurrentRangeJuliaDefectSteps_length lambda stepData S).trans
        (fixedSourceCurrentRangeJuliaReadouts_length lambda stepData S).symm) i)

end CCM24FiniteSFixedSourcePolar
end CCM25Concrete
end Source
end ConnesWeilRH
