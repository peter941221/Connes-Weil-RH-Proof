/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaPolarSlotBound
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawLocalDouglasBridge
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoDefectBridge
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaNonpolarGapFactorBridge

/-!
# Recovery of the Bone 1 raw factor

The local raw co-defect is related to the one-sided raw intertwinement by the
exact Schur--Markov cofactor identity.  The reverse transition is contractive,
but its scalar-normalized forward recovery has norm at most `8`.  Therefore a
local raw factor through the adjacent Julia left co-defect gives the desired
Bone 1 raw factor with the explicit cost `8`.

The polar slot then gives the following source-facing handoff:

```text
nonpolar gap factor (bound B)
        -> local raw factor (bound ||detector|| + B)
        -> raw factor (bound 8 * (||detector|| + B))
        -> old-carrier domination
```

This file proves only the algebraic recovery and its norm bookkeeping.  It
does not construct the nonpolar gap factor itself.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierFactorRecovery

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCompletedJuliaJointProducer
open CCM24FiniteSCompletedJuliaMismatchFactorization
open CCM24FiniteSCompletedJuliaNonpolarGapFactorBridge
open CCM24FiniteSCompletedJuliaPolarSlotBound
open CCM24FiniteSCompletedJuliaRawCoDefectFactor
open CCM24FiniteSCompletedJuliaRawDouglasReadout
open CCM24FiniteSCompletedJuliaRawLocalDouglasBridge
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoDefectBridge
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierReduction
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierSpectralGap
open CCM24FiniteSCompletedJuliaUniformCoDefectFactor
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSProjectionTrace
open CCM24FiniteSRawCompletedSchurCocycle
open CCM24FiniteSSchurMarkovPairing

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

local notation "SourceOp" lambda =>
  sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda

/-! ## Local raw factor -> raw factor -/

set_option maxHeartbeats 4000000 in
-- The two-step cofactor recovery expands several nested source-carrier maps.
set_option maxRecDepth 10000 in
noncomputable def
    SuffixLocalRawCoDefectFactorData.toRawCoDefectFactor
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {bound : ℝ}
    (data : SuffixLocalRawCoDefectFactorData owner lambda p S bound) :
    SuffixRawCoDefectFactorData owner lambda p S (8 * bound) := by
  let scaled := suffixMismatchScaledForwardTransition lambda p S
  let localDefect := suffixActualBandLocalRawDefect owner lambda p S
  let rawDefect := suffixActualBandRawQuadraticIntertwiningDefect
    owner lambda p S
  let leftCoDefect := (suffixEulerFrameSchurStep lambda p S).leftCoDefect
  let rightFactor : SourceOp lambda := -(data.rightFactor ∘L scaled)
  have hlocal : localDefect = leftCoDefect ∘L data.rightFactor := by
    simpa only [localDefect, leftCoDefect] using data.factorization
  have hrecover : localDefect ∘L scaled = -rawDefect := by
    calc
      localDefect ∘L scaled =
          ((-rawDefect) ∘L
            suffixEulerFrameReverseTransition lambda p S) ∘L scaled := by
        rw [show localDefect =
            (-rawDefect) ∘L suffixEulerFrameReverseTransition lambda p S by
          simpa only [localDefect, rawDefect] using
            suffixActualBandLocalRawDefect_eq_neg_rawIntertwiningDefect_comp_reverse
              owner lambda p S]
      _ = (-rawDefect) ∘L
          (suffixEulerFrameReverseTransition lambda p S ∘L scaled) := by
        simp only [ContinuousLinearMap.comp_assoc]
      _ = (-rawDefect) ∘L
          (ContinuousLinearMap.id ℂ (sourceSoninCarrier lambda)) := by
        dsimp [scaled, suffixMismatchScaledForwardTransition]
        rw [suffixEulerFrameReverse_comp_scaledTransition]
      _ = -rawDefect := by simp
  have hfactor : rawDefect = leftCoDefect ∘L rightFactor := by
    calc
      rawDefect = -(localDefect ∘L scaled) := by
        rw [hrecover]
        simp
      _ = -((leftCoDefect ∘L data.rightFactor) ∘L scaled) := by
        rw [hlocal]
      _ = leftCoDefect ∘L rightFactor := by
        apply ContinuousLinearMap.ext
        intro x
        simp only [rightFactor, ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.neg_apply, map_neg]
  have hnorm : ‖rightFactor‖ ≤ 8 * bound := by
    change ‖-(data.rightFactor ∘L
      suffixMismatchScaledForwardTransition lambda p S)‖ ≤ 8 * bound
    rw [ContinuousLinearMap.opNorm_neg]
    calc
      ‖data.rightFactor ∘L suffixMismatchScaledForwardTransition lambda p S‖ ≤
          ‖data.rightFactor‖ *
            ‖suffixMismatchScaledForwardTransition lambda p S‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ bound * 8 := by
        exact mul_le_mul data.rightFactor_norm_le
          (suffixMismatchScaledForwardTransition_norm_le_eight lambda p S)
          (norm_nonneg _) data.bound_nonneg
      _ = 8 * bound := by ring
  exact
    { rightFactor := rightFactor
      rightFactor_norm_le := hnorm
      factorization := hfactor }

/-! ## The local reverse direction -/

noncomputable def
    SuffixRawCoDefectFactorData.toLocalRawCoDefectFactor
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {bound : ℝ}
    (data : SuffixRawCoDefectFactorData owner lambda p S bound) :
    SuffixLocalRawCoDefectFactorData owner lambda p S bound := by
  let reverse := suffixEulerFrameReverseTransition lambda p S
  let localDefect := suffixActualBandLocalRawDefect owner lambda p S
  let rawDefect := suffixActualBandRawQuadraticIntertwiningDefect
    owner lambda p S
  let leftCoDefect := (suffixEulerFrameSchurStep lambda p S).leftCoDefect
  let rightFactor : SourceOp lambda := -(data.rightFactor ∘L reverse)
  have hbound : 0 ≤ bound :=
    le_trans (norm_nonneg data.rightFactor) data.rightFactor_norm_le
  have hfactor : localDefect = leftCoDefect ∘L rightFactor := by
    calc
      localDefect = (-rawDefect) ∘L reverse := by
        simpa only [localDefect, rawDefect, reverse] using
          suffixActualBandLocalRawDefect_eq_neg_rawIntertwiningDefect_comp_reverse
            owner lambda p S
      _ = (-(leftCoDefect ∘L data.rightFactor)) ∘L reverse := by
        rw [show rawDefect = leftCoDefect ∘L data.rightFactor by
          simpa only [rawDefect, leftCoDefect] using data.factorization]
      _ = leftCoDefect ∘L rightFactor := by
        apply ContinuousLinearMap.ext
        intro x
        simp only [rightFactor, ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.neg_apply, map_neg]
  have hnorm : ‖rightFactor‖ ≤ bound := by
    change ‖-(data.rightFactor ∘L
      suffixEulerFrameReverseTransition lambda p S)‖ ≤ bound
    rw [ContinuousLinearMap.opNorm_neg]
    calc
      ‖data.rightFactor ∘L suffixEulerFrameReverseTransition lambda p S‖ ≤
          ‖data.rightFactor‖ *
            ‖suffixEulerFrameReverseTransition lambda p S‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ bound * 1 := by
        exact mul_le_mul data.rightFactor_norm_le
          (suffixEulerFrameReverseTransition_norm_le_one lambda p S)
          (norm_nonneg _) hbound
      _ = bound := by ring
  exact
    { bound_nonneg := hbound
      rightFactor := rightFactor
      rightFactor_norm_le := hnorm
      factorization := hfactor }

/-! ## Uniform-family conversions -/

noncomputable def
    SuffixLocalRawCoDefectUniformFactorData.toRawCoDefectUniform
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {bound : ℝ}
    (data : SuffixLocalRawCoDefectUniformFactorData owner lambda bound) :
    SuffixRawCoDefectUniformFactorData owner lambda (8 * bound) :=
  { bound_nonneg := mul_nonneg (by norm_num) data.bound_nonneg
    factor := fun p S =>
      SuffixLocalRawCoDefectFactorData.toRawCoDefectFactor
        (data.factor p S) }

noncomputable def
    SuffixRawCoDefectUniformFactorData.toLocalRawCoDefectUniform
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {bound : ℝ}
    (data : SuffixRawCoDefectUniformFactorData owner lambda bound) :
    SuffixLocalRawCoDefectUniformFactorData owner lambda bound :=
  { bound_nonneg := data.bound_nonneg
    factor := fun p S =>
      SuffixRawCoDefectFactorData.toLocalRawCoDefectFactor
        (data.factor p S) }

noncomputable def
    SuffixLocalNonpolarGapCoDefectUniformFactorData.toRawCoDefectUniform
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {bound : ℝ}
    (data : SuffixLocalNonpolarGapCoDefectUniformFactorData owner lambda bound) :
    SuffixRawCoDefectUniformFactorData owner lambda
      (8 * (‖detectorOperator owner‖ + bound)) :=
  SuffixLocalRawCoDefectUniformFactorData.toRawCoDefectUniform
    (SuffixLocalNonpolarGapCoDefectUniformFactorData.toLocalRawUniform data)

noncomputable def
    SuffixRawCoDefectUniformFactorData.toNonpolarGapUniform
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {bound : ℝ}
    (data : SuffixRawCoDefectUniformFactorData owner lambda bound) :
    SuffixLocalNonpolarGapCoDefectUniformFactorData owner lambda
      (‖detectorOperator owner‖ + bound) :=
  SuffixLocalRawCoDefectUniformFactorData.toNonpolarGapUniform
    (SuffixRawCoDefectUniformFactorData.toLocalRawCoDefectUniform data)

theorem exists_uniformRawCoDefectFactor_iff_exists_uniformNonpolarGapFactor
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    (∃ bound : ℝ,
      Nonempty (SuffixRawCoDefectUniformFactorData owner lambda bound)) ↔
      (∃ bound : ℝ,
        Nonempty (SuffixLocalNonpolarGapCoDefectUniformFactorData
          owner lambda bound)) := by
  constructor
  · rintro ⟨bound, ⟨data⟩⟩
    exact ⟨‖detectorOperator owner‖ + bound,
      ⟨SuffixRawCoDefectUniformFactorData.toNonpolarGapUniform data⟩⟩
  · rintro ⟨bound, ⟨data⟩⟩
    exact ⟨8 * (‖detectorOperator owner‖ + bound),
      ⟨SuffixLocalNonpolarGapCoDefectUniformFactorData.toRawCoDefectUniform
        data⟩⟩

/-! ## Direct Bone 1 handoff -/

noncomputable def
    SuffixMismatchAmbientBoundaryUniformCoDefectFactorData.toRawCoDefectUniform
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {bound : ℝ}
    (data : SuffixMismatchAmbientBoundaryUniformCoDefectFactorData
      owner lambda bound) :
    SuffixRawCoDefectUniformFactorData owner lambda
      (8 * (‖detectorOperator owner‖ + bound)) :=
  SuffixLocalNonpolarGapCoDefectUniformFactorData.toRawCoDefectUniform
    (mismatchUniformFactorData_toLocalNonpolarGapUniform data)

theorem
    SuffixMismatchAmbientBoundaryUniformCoDefectFactorData.toOldCarrierUniformDomination
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {bound : ℝ}
    (data : SuffixMismatchAmbientBoundaryUniformCoDefectFactorData
      owner lambda bound) :
    Nonempty (SuffixRawOldCarrierUniformDominationData owner lambda
      (8 * (‖detectorOperator owner‖ + bound))) :=
  SuffixRawCoDefectUniformFactorData.toOldCarrierUniformDomination
    (SuffixMismatchAmbientBoundaryUniformCoDefectFactorData.toRawCoDefectUniform
      data)

theorem exists_uniformOldCarrierDomination_iff_exists_uniformNonpolarGapFactor
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    (∃ bound : ℝ,
      Nonempty (SuffixRawOldCarrierUniformDominationData owner lambda bound)) ↔
      (∃ bound : ℝ,
        Nonempty (SuffixLocalNonpolarGapCoDefectUniformFactorData
          owner lambda bound)) := by
  constructor
  · rintro ⟨bound, ⟨data⟩⟩
    let rawDom : SuffixRawAmbientBoundaryUniformDominationData owner lambda
        bound :=
      { bound_nonneg := data.bound_nonneg
        domination := fun p S =>
          suffixRawOldCarrierDomination_implies_rawDomination owner lambda
            p S bound (data.domination p S) }
    have hfactor :
        Nonempty (SuffixRawCoDefectUniformFactorData owner lambda bound) :=
      (uniformRawDomination_iff_nonempty_uniformCoDefectFactor
        owner lambda bound).mp ⟨rawDom⟩
    obtain ⟨factor⟩ := hfactor
    exact ⟨‖detectorOperator owner‖ + bound,
      ⟨SuffixRawCoDefectUniformFactorData.toNonpolarGapUniform factor⟩⟩
  · rintro ⟨bound, ⟨data⟩⟩
    exact ⟨8 * (‖detectorOperator owner‖ + bound),
      SuffixRawCoDefectUniformFactorData.toOldCarrierUniformDomination
        (SuffixLocalNonpolarGapCoDefectUniformFactorData.toRawCoDefectUniform
          data)⟩

end CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierFactorRecovery
end CCM25Concrete
end Source
end ConnesWeilRH
