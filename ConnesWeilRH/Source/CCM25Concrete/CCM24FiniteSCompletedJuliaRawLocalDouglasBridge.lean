/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaNonpolarGapDouglas
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaPolarSlotBound
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawDouglasReadout
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawLocalCofactor

/-!
# Raw physical Douglas to the complete signed local gap

The local raw defect is not the same operator as the four-term physical row.
The two are related by the two-sided Schur--Markov cofactor identities.  This
module makes the direction needed by the Douglas estimate explicit:

```text
localRawDefect = -rawIntertwiningDefect * reverseTransition
localRawDefect^dagger = -reverseTransition^dagger * rawPhysicalRow
```

The reverse transition is contractive.  Therefore an already available raw
physical Douglas estimate transfers to the complete local raw defect, and the
closed polar Julia slot can then be subtracted to obtain the complete signed
non-polar gap estimate.  The raw physical estimate remains an explicit source
premise; this file does not manufacture it.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedJuliaRawLocalDouglasBridge

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCompletedJuliaAmbientDefectFactorization
open CCM24FiniteSCompletedJuliaNonpolarGapDouglas
open CCM24FiniteSCompletedJuliaMismatchFactorization
open CCM24FiniteSCompletedJuliaPolarSlotBound
open CCM24FiniteSCompletedJuliaRawDouglasReadout
open CCM24FiniteSCompletedJuliaRawLocalCofactor
open CCM24FiniteSCompletedJuliaRawPhysicalFactorization
open CCM24FiniteSCompletedJuliaSignedLocalization
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSJuliaCoDefect
open CCM24FiniteSJuliaBessel
open CCM24FiniteSProjectionTrace
open CCM24FiniteSRawCompletedSchurCocycle
open CCM24FiniteSSchurMarkovPairing

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace
      (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

local notation "SourceOp" lambda =>
  sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda

/-! ## Exact local cofactor readback -/

theorem suffixActualBandLocalRawDefect_eq_neg_rawIntertwiningDefect_comp_reverse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandLocalRawDefect owner lambda p S =
      (-suffixActualBandRawQuadraticIntertwiningDefect owner lambda p S) ∘L
        suffixEulerFrameReverseTransition lambda p S := by
  have hpair := suffixEulerFrameTransition_comp_reverse lambda p S
  apply ContinuousLinearMap.ext
  intro x
  have hpairx := congrArg
    (fun operator : SourceOp lambda => operator x) hpair
  simp only [suffixActualBandLocalRawDefect,
    suffixActualBandRawQuadraticIntertwiningDefect,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.id_apply] at hpairx ⊢
  rw [hpairx, map_smul]
  abel

theorem suffixActualBandLocalRawDefect_adjoint_eq_neg_reverse_adjoint_comp_rawPhysicalRow
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    (suffixActualBandLocalRawDefect owner lambda p S)† =
      -((suffixEulerFrameReverseTransition lambda p S)† ∘L
        suffixActualBandRawPhysicalFourTermRow owner lambda p S) := by
  have hneg (operator : SourceOp lambda) :
      (-operator)† = -(operator†) := by
    apply ContinuousLinearMap.ext
    intro y
    apply ext_inner_right ℂ
    intro z
    simp only [ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearMap.neg_apply, inner_neg_left, inner_neg_right]
  have hrow :
      (suffixActualBandRawQuadraticIntertwiningDefect owner lambda p S)† =
        suffixActualBandRawPhysicalFourTermRow owner lambda p S := by
    rw [← suffixActualBandRawPhysicalFourTermRow_adjoint_eq_rawIntertwiningDefect,
      ContinuousLinearMap.adjoint_adjoint]
  calc
    (suffixActualBandLocalRawDefect owner lambda p S)† =
        ((-suffixActualBandRawQuadraticIntertwiningDefect owner lambda p S) ∘L
          suffixEulerFrameReverseTransition lambda p S)† := by
      rw [suffixActualBandLocalRawDefect_eq_neg_rawIntertwiningDefect_comp_reverse]
    _ = (suffixEulerFrameReverseTransition lambda p S)† ∘L
          (-suffixActualBandRawQuadraticIntertwiningDefect owner lambda p S)† := by
      rw [ContinuousLinearMap.adjoint_comp]
    _ = (suffixEulerFrameReverseTransition lambda p S)† ∘L
          (-(suffixActualBandRawQuadraticIntertwiningDefect
            owner lambda p S)†) := by
      rw [hneg]
    _ = (suffixEulerFrameReverseTransition lambda p S)† ∘L
          (-suffixActualBandRawPhysicalFourTermRow owner lambda p S) := by
      rw [hrow]
    _ = -((suffixEulerFrameReverseTransition lambda p S)† ∘L
          suffixActualBandRawPhysicalFourTermRow owner lambda p S) := by
      apply ContinuousLinearMap.ext
      intro x
      simp only [ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.neg_apply, map_neg]

/-! ## Transfer of the signed Douglas estimate -/

set_option maxHeartbeats 4000000 in
-- The packed raw row and co-defect energy normalization need a larger budget.
theorem suffixActualBandLocalRawDefect_adjoint_normSq_le_of_rawDomination
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {bound : ℝ}
    (hdom : SuffixRawAmbientBoundaryDomination owner lambda p S bound)
    (x : sourceSoninCarrier lambda) :
    ‖((suffixActualBandLocalRawDefect owner lambda p S)†) x‖ ^ 2 ≤
      bound ^ 2 *
        ‖(suffixEulerFrameSchurStep lambda p S).leftCoDefect x‖ ^ 2 := by
  have hrow :
      (suffixActualBandRawQuadraticIntertwiningDefect owner lambda p S)† =
        suffixActualBandRawPhysicalFourTermRow owner lambda p S := by
    rw [← suffixActualBandRawPhysicalFourTermRow_adjoint_eq_rawIntertwiningDefect,
      ContinuousLinearMap.adjoint_adjoint]
  have hraw := hdom.2 x
  rw [hrow] at hraw
  have hreverse :
      ‖(suffixEulerFrameReverseTransition lambda p S)†‖ ≤ (1 : ℝ) := by
    calc
      ‖(suffixEulerFrameReverseTransition lambda p S)†‖ =
          ‖suffixEulerFrameReverseTransition lambda p S‖ :=
        ContinuousLinearMap.adjoint.norm_map _
      _ ≤ 1 := suffixEulerFrameReverseTransition_norm_le_one lambda p S
  have hpoint :
      ‖((suffixEulerFrameReverseTransition lambda p S)†)
          (suffixActualBandRawPhysicalFourTermRow owner lambda p S x)‖ ≤
        ‖suffixActualBandRawPhysicalFourTermRow owner lambda p S x‖ := by
    calc
      ‖((suffixEulerFrameReverseTransition lambda p S)†)
          (suffixActualBandRawPhysicalFourTermRow owner lambda p S x)‖ ≤
          ‖(suffixEulerFrameReverseTransition lambda p S)†‖ *
            ‖suffixActualBandRawPhysicalFourTermRow owner lambda p S x‖ :=
        (suffixEulerFrameReverseTransition lambda p S)†.le_opNorm _
      _ ≤ 1 * ‖suffixActualBandRawPhysicalFourTermRow owner lambda p S x‖ :=
        mul_le_mul_of_nonneg_right hreverse (norm_nonneg _)
      _ = ‖suffixActualBandRawPhysicalFourTermRow owner lambda p S x‖ :=
        one_mul _
  have hlocal :
      ‖((suffixActualBandLocalRawDefect owner lambda p S)†) x‖ ^ 2 ≤
        ‖suffixActualBandRawPhysicalFourTermRow owner lambda p S x‖ ^ 2 := by
    rw [suffixActualBandLocalRawDefect_adjoint_eq_neg_reverse_adjoint_comp_rawPhysicalRow]
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.neg_apply, norm_neg] using
      (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hpoint
  calc
    ‖((suffixActualBandLocalRawDefect owner lambda p S)†) x‖ ^ 2 ≤
        ‖suffixActualBandRawPhysicalFourTermRow owner lambda p S x‖ ^ 2 := hlocal
    _ ≤ bound ^ 2 *
        (‖suffixEulerFrameAmbientLossColumn lambda p S x‖ ^ 2 +
          ‖(ContinuousLinearMap.adjoint
            (suffixEulerFrameSchurStep lambda p S).boundary) x‖ ^ 2) := hraw
    _ = bound ^ 2 *
        ‖(suffixEulerFrameSchurStep lambda p S).leftCoDefect x‖ ^ 2 := by
      rw [suffixEulerFrameLeftCoDefect_normSq_eq_ambient_add_boundary]

/-! ## The complete signed non-polar gap -/

set_option maxHeartbeats 4000000 in
-- The signed raw/polar subtraction keeps the two Douglas readbacks on one carrier.
theorem suffixActualBandLocalNonpolarLocalizationGap_douglas_of_rawDomination
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {bound : ℝ}
    (hdom : SuffixRawAmbientBoundaryDomination owner lambda p S bound) :
    SuffixLocalNonpolarGapDouglasDomination owner lambda p S
      (‖detectorOperator owner‖ + bound) := by
  have hlocal (x : sourceSoninCarrier lambda) :=
    suffixActualBandLocalRawDefect_adjoint_normSq_le_of_rawDomination hdom x
  have hpolarFactor :=
    suffixActualBandLocalPolarJuliaContribution_eq_leftCoDefect
      owner lambda p S
  have hself : IsSelfAdjoint
      (suffixEulerFrameSchurStep lambda p S).leftCoDefect := by
    simpa only [RectangularSchurCoDefectStepData.leftCoDefect] using
      (canonicalJuliaDefect_isSelfAdjoint
        (ContinuousLinearMap.adjoint
          (suffixEulerFrameSchurStep lambda p S).transition)
        (suffixEulerFrameSchurStep lambda p S).transitionAdjointContract)
  have hpolarAdjoint :
      (suffixActualBandLocalPolarJuliaContribution owner lambda p S)† =
        (suffixActualBandLocalPolarJuliaRightFactor owner lambda p S)† ∘L
          (suffixEulerFrameSchurStep lambda p S).leftCoDefect := by
    have h := congrArg ContinuousLinearMap.adjoint hpolarFactor
    simpa only [ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint, hself.adjoint_eq] using h
  have hpolarNorm (x : sourceSoninCarrier lambda) :
      ‖((suffixActualBandLocalPolarJuliaContribution owner lambda p S)†) x‖ ≤
        ‖detectorOperator owner‖ *
          ‖(suffixEulerFrameSchurStep lambda p S).leftCoDefect x‖ := by
    rw [hpolarAdjoint, ContinuousLinearMap.comp_apply]
    calc
      ‖((suffixActualBandLocalPolarJuliaRightFactor owner lambda p S)†)
          ((suffixEulerFrameSchurStep lambda p S).leftCoDefect x)‖ ≤
          ‖(suffixActualBandLocalPolarJuliaRightFactor owner lambda p S)†‖ *
            ‖(suffixEulerFrameSchurStep lambda p S).leftCoDefect x‖ :=
        (suffixActualBandLocalPolarJuliaRightFactor owner lambda p S)†.le_opNorm _
      _ = ‖suffixActualBandLocalPolarJuliaRightFactor owner lambda p S‖ *
            ‖(suffixEulerFrameSchurStep lambda p S).leftCoDefect x‖ := by
        exact congrArg
          (fun value : ℝ => value *
            ‖(suffixEulerFrameSchurStep lambda p S).leftCoDefect x‖)
          (ContinuousLinearMap.adjoint.norm_map
            (suffixActualBandLocalPolarJuliaRightFactor owner lambda p S))
      _ ≤ ‖detectorOperator owner‖ *
            ‖(suffixEulerFrameSchurStep lambda p S).leftCoDefect x‖ := by
        exact mul_le_mul_of_nonneg_right
          (suffixActualBandLocalPolarJuliaRightFactor_norm_le_detector
            owner lambda p S) (norm_nonneg _)
  have hsplit := suffixActualBandLocalRawDefect_eq_polarJulia_add_nonpolarGap
    owner lambda p S
  have hadd (A B : SourceOp lambda) :
      (A + B)† = A† + B† := by
    exact ContinuousLinearMap.adjoint.map_add _ _
  have hgapAdj :
      (suffixActualBandLocalNonpolarLocalizationGap owner lambda p S)† =
        (suffixActualBandLocalRawDefect owner lambda p S)† -
          (suffixActualBandLocalPolarJuliaContribution owner lambda p S)† := by
    have hsum := congrArg ContinuousLinearMap.adjoint hsplit
    rw [hadd] at hsum
    apply ContinuousLinearMap.ext
    intro x
    have hsumPoint := congrArg
      (fun operator : SourceOp lambda => operator x) hsum
    have hsumPoint' :
        ((suffixActualBandLocalRawDefect owner lambda p S)†) x =
          ((suffixActualBandLocalPolarJuliaContribution owner lambda p S)†) x +
            ((suffixActualBandLocalNonpolarLocalizationGap owner lambda p S)†) x := by
      simpa only [ContinuousLinearMap.add_apply] using hsumPoint
    calc
      ((suffixActualBandLocalNonpolarLocalizationGap owner lambda p S)†) x =
          (((suffixActualBandLocalPolarJuliaContribution owner lambda p S)†) x +
            ((suffixActualBandLocalNonpolarLocalizationGap owner lambda p S)†) x) -
            ((suffixActualBandLocalPolarJuliaContribution owner lambda p S)†) x := by
        abel
      _ = ((suffixActualBandLocalRawDefect owner lambda p S)†) x -
          ((suffixActualBandLocalPolarJuliaContribution owner lambda p S)†) x := by
        rw [← hsumPoint']
  refine ⟨add_nonneg (norm_nonneg (detectorOperator owner)) hdom.1, ?_⟩
  intro x
  have hlocalNorm :
      ‖((suffixActualBandLocalRawDefect owner lambda p S)†) x‖ ≤
        bound * ‖(suffixEulerFrameSchurStep lambda p S).leftCoDefect x‖ :=
    (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg hdom.1 (norm_nonneg _))).mp (by
        simpa only [mul_pow] using hlocal x)
  have hgapNorm :
      ‖((suffixActualBandLocalNonpolarLocalizationGap owner lambda p S)†) x‖ ≤
        (‖detectorOperator owner‖ + bound) *
          ‖(suffixEulerFrameSchurStep lambda p S).leftCoDefect x‖ := by
    rw [hgapAdj, ContinuousLinearMap.sub_apply]
    calc
      ‖((suffixActualBandLocalRawDefect owner lambda p S)†) x -
          ((suffixActualBandLocalPolarJuliaContribution owner lambda p S)†) x‖ ≤
          ‖((suffixActualBandLocalRawDefect owner lambda p S)†) x‖ +
            ‖((suffixActualBandLocalPolarJuliaContribution owner lambda p S)†) x‖ :=
        norm_sub_le _ _
      _ ≤ bound * ‖(suffixEulerFrameSchurStep lambda p S).leftCoDefect x‖ +
          ‖detectorOperator owner‖ *
            ‖(suffixEulerFrameSchurStep lambda p S).leftCoDefect x‖ :=
        add_le_add hlocalNorm (hpolarNorm x)
      _ = (‖detectorOperator owner‖ + bound) *
          ‖(suffixEulerFrameSchurStep lambda p S).leftCoDefect x‖ := by
        ring
  simpa only [mul_pow] using
    (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg (add_nonneg (norm_nonneg (detectorOperator owner)) hdom.1)
        (norm_nonneg _))).mpr hgapNorm

/-! ## Uniform handoff -/

noncomputable def
    SuffixRawAmbientBoundaryUniformDominationData.toNonpolarGapDouglas
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {bound : ℝ}
    (data : SuffixRawAmbientBoundaryUniformDominationData owner lambda bound) :
    SuffixLocalNonpolarGapUniformDouglasData owner lambda
      (‖detectorOperator owner‖ + bound) :=
  { bound_nonneg := add_nonneg (norm_nonneg (detectorOperator owner))
      data.bound_nonneg
    domination := fun p S =>
      suffixActualBandLocalNonpolarLocalizationGap_douglas_of_rawDomination
        (data.domination p S) }

end CCM24FiniteSCompletedJuliaRawLocalDouglasBridge
end CCM25Concrete
end Source
end ConnesWeilRH
