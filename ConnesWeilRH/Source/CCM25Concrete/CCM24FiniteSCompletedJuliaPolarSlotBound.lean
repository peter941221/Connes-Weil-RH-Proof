/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaSignedLocalization
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaPolarRawReadout

/-!
# Quantitative polar Julia slot in the local completed raw defect

Proof 501 localized the polar contribution of the local raw defect in the
actual adjacent Julia co-defect.  This module records the missing quantitative
part of that closed slot: its right factor has norm at most the selected
detector norm, uniformly in the visible prime and suffix.

Consequently the remaining local co-defect producer is exactly the non-polar
localization gap, up to the fixed detector-norm cost.  This is still not the
Gate 3U estimate: it isolates the source-specific non-polar gap that must be
bounded next.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedJuliaPolarSlotBound

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCompletedJuliaPolarRawReadout
open CCM24FiniteSCompletedJuliaSignedLocalization
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSJuliaCoDefect
open CCM24FiniteSProjectionTrace
open CCM24FiniteSRawCompletedSchurCocycle
open CCM24FiniteSSchurMarkovPairing

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) :
      CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

local notation "SourceOp" lambda =>
  sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda

/-! ## Quantitative polar slot -/

/-- The polar Julia right factor is uniformly bounded by the selected
detector norm.  The proof uses only the contraction of the boundary co-defect
factor, the normalized suffix frame, and the reverse Schur--Markov transition.
-/
theorem suffixActualBandLocalPolarJuliaRightFactor_norm_le_detector
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    ‖suffixActualBandLocalPolarJuliaRightFactor owner lambda p S‖ ≤
      ‖detectorOperator owner‖ := by
  let factor :=
    ((suffixEulerFrameSchurStep lambda p S).boundaryCoDefectFactor).factor
  let detector := detectorOperator owner
  let frame := newSuffixFrame lambda S
  let reverse := suffixEulerFrameReverseTransition lambda p S
  have hfactor : ‖ContinuousLinearMap.adjoint factor‖ ≤ (1 : ℝ) := by
    exact
      ((suffixEulerFrameSchurStep lambda p S).boundaryCoDefectFactor)
        |>.factor_adjoint_norm_le_one
  have hframe : ‖frame‖ ≤ (1 : ℝ) := by
    exact newSuffixFrame_norm_le_one lambda S
  have hreverse : ‖reverse‖ ≤ (1 : ℝ) := by
    exact suffixEulerFrameReverseTransition_norm_le_one lambda p S
  have hcomp1 :
      ‖((ContinuousLinearMap.adjoint factor ∘L detector) ∘L frame) ∘L
          reverse‖ ≤
        ‖(ContinuousLinearMap.adjoint factor ∘L detector) ∘L frame‖ *
          ‖reverse‖ :=
    ContinuousLinearMap.opNorm_comp_le _ _
  have hcomp2 :
      ‖(ContinuousLinearMap.adjoint factor ∘L detector) ∘L frame‖ ≤
        ‖ContinuousLinearMap.adjoint factor ∘L detector‖ * ‖frame‖ :=
    ContinuousLinearMap.opNorm_comp_le _ _
  have hcomp3 :
      ‖ContinuousLinearMap.adjoint factor ∘L detector‖ ≤
        ‖ContinuousLinearMap.adjoint factor‖ * ‖detector‖ :=
    ContinuousLinearMap.opNorm_comp_le _ _
  have htarget :
      ‖((ContinuousLinearMap.adjoint factor ∘L detector) ∘L frame) ∘L
          reverse‖ ≤ ‖detector‖ := by
    have hnonFactor : 0 ≤ ‖ContinuousLinearMap.adjoint factor‖ := by
      exact norm_nonneg (ContinuousLinearMap.adjoint factor)
    have hnonDetector : 0 ≤ ‖detector‖ := by
      exact norm_nonneg detector
    have hnonFrame : 0 ≤ ‖frame‖ := by
      exact norm_nonneg frame
    have hnonReverse : 0 ≤ ‖reverse‖ := by
      exact norm_nonneg reverse
    have hnonComp1 :
        0 ≤ ‖ContinuousLinearMap.adjoint factor ∘L detector‖ := by
      exact norm_nonneg (ContinuousLinearMap.adjoint factor ∘L detector)
    have hnonComp2 :
        0 ≤ ‖(ContinuousLinearMap.adjoint factor ∘L detector) ∘L frame‖ :=
      by
        exact norm_nonneg
          ((ContinuousLinearMap.adjoint factor ∘L detector) ∘L frame)
    nlinarith
  simpa only [suffixActualBandLocalPolarJuliaRightFactor, factor, detector,
    frame, reverse, ContinuousLinearMap.comp_assoc] using htarget

/-! ## Local raw and non-polar co-defect factor data -/

/-- A right factor through the actual adjacent Julia left co-defect for the
full local raw defect. -/
structure SuffixLocalRawCoDefectFactorData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (bound : ℝ) where
  bound_nonneg : 0 ≤ bound
  rightFactor : SourceOp lambda
  rightFactor_norm_le : ‖rightFactor‖ ≤ bound
  factorization :
    suffixActualBandLocalRawDefect owner lambda p S =
      (suffixEulerFrameSchurStep lambda p S).leftCoDefect ∘L rightFactor

/-- The source-specific remaining factor: the non-polar localization gap
through the same adjacent Julia left co-defect. -/
structure SuffixLocalNonpolarGapCoDefectFactorData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (bound : ℝ) where
  bound_nonneg : 0 ≤ bound
  completion : SourceOp lambda
  completion_norm_le : ‖completion‖ ≤ bound
  factorization :
    suffixActualBandLocalNonpolarLocalizationGap owner lambda p S =
      (suffixEulerFrameSchurStep lambda p S).leftCoDefect ∘L completion

/-- A non-polar gap factor completes the full local raw factor.  The only
extra cost is the already closed polar Julia slot, bounded by the detector
norm. -/
noncomputable def
    SuffixLocalNonpolarGapCoDefectFactorData.toLocalRawFactor
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {bound : ℝ}
    (data : SuffixLocalNonpolarGapCoDefectFactorData
      owner lambda p S bound) :
    SuffixLocalRawCoDefectFactorData owner lambda p S
      (‖detectorOperator owner‖ + bound) := by
  let polar := suffixActualBandLocalPolarJuliaRightFactor owner lambda p S
  let rightFactor := polar + data.completion
  have hfactor :
      suffixActualBandLocalRawDefect owner lambda p S =
        (suffixEulerFrameSchurStep lambda p S).leftCoDefect ∘L
          rightFactor := by
    exact
      (suffixActualBandLocalRawDefect_eq_leftCoDefect_iff_nonpolarGap
        owner lambda p S data.completion).mpr data.factorization
  have hnorm : ‖rightFactor‖ ≤ ‖detectorOperator owner‖ + bound := by
    calc
      ‖rightFactor‖ = ‖polar + data.completion‖ := rfl
      _ ≤ ‖polar‖ + ‖data.completion‖ :=
        ContinuousLinearMap.opNorm_add_le _ _
      _ ≤ ‖detectorOperator owner‖ + bound := by
        exact add_le_add
          (suffixActualBandLocalPolarJuliaRightFactor_norm_le_detector
            owner lambda p S)
          data.completion_norm_le
  exact
    { bound_nonneg := add_nonneg (norm_nonneg (detectorOperator owner))
        data.bound_nonneg
      rightFactor := rightFactor
      rightFactor_norm_le := hnorm
      factorization := hfactor }

/-- Conversely, any full local raw factor leaves a non-polar gap factor after
subtracting the closed polar Julia right factor. -/
noncomputable def
    SuffixLocalRawCoDefectFactorData.toNonpolarGapFactor
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {bound : ℝ}
    (data : SuffixLocalRawCoDefectFactorData owner lambda p S bound) :
    SuffixLocalNonpolarGapCoDefectFactorData owner lambda p S
      (‖detectorOperator owner‖ + bound) := by
  let polar := suffixActualBandLocalPolarJuliaRightFactor owner lambda p S
  let completion := data.rightFactor - polar
  have hright : polar + completion = data.rightFactor := by
    apply ContinuousLinearMap.ext
    intro x
    simp only [polar, completion, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.sub_apply]
    abel
  have hfull :
      suffixActualBandLocalRawDefect owner lambda p S =
        (suffixEulerFrameSchurStep lambda p S).leftCoDefect ∘L
          (polar + completion) := by
    rw [hright]
    exact data.factorization
  have hfactor :
      suffixActualBandLocalNonpolarLocalizationGap owner lambda p S =
        (suffixEulerFrameSchurStep lambda p S).leftCoDefect ∘L
          completion := by
    exact
      (suffixActualBandLocalRawDefect_eq_leftCoDefect_iff_nonpolarGap
        owner lambda p S completion).mp hfull
  have hnorm : ‖completion‖ ≤ ‖detectorOperator owner‖ + bound := by
    calc
      ‖completion‖ = ‖data.rightFactor + -polar‖ := by
        change ‖data.rightFactor - polar‖ = ‖data.rightFactor + -polar‖
        rw [sub_eq_add_neg]
      _ ≤ ‖data.rightFactor‖ + ‖-polar‖ :=
        ContinuousLinearMap.opNorm_add_le _ _
      _ = ‖data.rightFactor‖ + ‖polar‖ := by
        rw [ContinuousLinearMap.opNorm_neg]
      _ ≤ bound + ‖detectorOperator owner‖ := by
        exact add_le_add data.rightFactor_norm_le
          (suffixActualBandLocalPolarJuliaRightFactor_norm_le_detector
            owner lambda p S)
      _ = ‖detectorOperator owner‖ + bound := by ring
  exact
    { bound_nonneg := add_nonneg (norm_nonneg (detectorOperator owner))
        data.bound_nonneg
      completion := completion
      completion_norm_le := hnorm
      factorization := hfactor }

/-! ## Uniform-family reduction -/

/-- A uniform family of local raw co-defect factors. -/
structure SuffixLocalRawCoDefectUniformFactorData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (bound : ℝ) where
  bound_nonneg : 0 ≤ bound
  factor : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
    SuffixLocalRawCoDefectFactorData owner lambda p S bound

/-- A uniform family of non-polar gap co-defect factors. -/
structure SuffixLocalNonpolarGapCoDefectUniformFactorData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (bound : ℝ) where
  bound_nonneg : 0 ≤ bound
  factor : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
    SuffixLocalNonpolarGapCoDefectFactorData owner lambda p S bound

/-- A uniform non-polar gap factor family gives a uniform local raw factor
family, paying only the detector norm. -/
noncomputable def
    SuffixLocalNonpolarGapCoDefectUniformFactorData.toLocalRawUniform
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {bound : ℝ}
    (data : SuffixLocalNonpolarGapCoDefectUniformFactorData
      owner lambda bound) :
    SuffixLocalRawCoDefectUniformFactorData owner lambda
      (‖detectorOperator owner‖ + bound) :=
  { bound_nonneg := add_nonneg (norm_nonneg (detectorOperator owner))
      data.bound_nonneg
    factor := fun p S =>
      (data.factor p S).toLocalRawFactor }

/-- A uniform local raw factor family gives a uniform non-polar gap factor
family, again paying only the detector norm. -/
noncomputable def
    SuffixLocalRawCoDefectUniformFactorData.toNonpolarGapUniform
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {bound : ℝ}
    (data : SuffixLocalRawCoDefectUniformFactorData owner lambda bound) :
    SuffixLocalNonpolarGapCoDefectUniformFactorData owner lambda
      (‖detectorOperator owner‖ + bound) :=
  { bound_nonneg := add_nonneg (norm_nonneg (detectorOperator owner))
      data.bound_nonneg
    factor := fun p S =>
      (data.factor p S).toNonpolarGapFactor }

/-- Existence of a finite uniform local raw factor family is equivalent to
existence of a finite uniform non-polar gap factor family.  The equivalence is
not isometric: converting either way adds the fixed detector norm. -/
theorem exists_uniformLocalRawFactor_iff_exists_uniformNonpolarGapFactor
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    (∃ bound : ℝ,
      Nonempty
        (SuffixLocalRawCoDefectUniformFactorData owner lambda bound)) ↔
      (∃ bound : ℝ,
        Nonempty
          (SuffixLocalNonpolarGapCoDefectUniformFactorData
            owner lambda bound)) := by
  constructor
  · rintro ⟨bound, ⟨data⟩⟩
    exact ⟨‖detectorOperator owner‖ + bound,
      ⟨data.toNonpolarGapUniform⟩⟩
  · rintro ⟨bound, ⟨data⟩⟩
    exact ⟨‖detectorOperator owner‖ + bound,
      ⟨data.toLocalRawUniform⟩⟩

end CCM24FiniteSCompletedJuliaPolarSlotBound
end CCM25Concrete
end Source
end ConnesWeilRH
