/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaUniformRawReadout

/-!
# Raw physical readout equivalence

The unconditional polar readout is already available. Therefore the missing
physical Douglas producer can be stated either for the complete mismatch or
for the recombined raw four-term intertwinement. This module records both
directions explicitly, with the detector norm as the only additive cost.

This is an interface reduction, not a domination theorem. No readout is
constructed for the raw four-term row without a source-specific premise.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedJuliaRawPhysicalReadout

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCompletedJuliaAmbientDefectFactorization
open CCM24FiniteSCompletedJuliaMismatchFactorization
open CCM24FiniteSCompletedJuliaPhysicalDouglasReadout
open CCM24FiniteSCompletedJuliaPolarRawReadout
open CCM24FiniteSCompletedJuliaUniformRawReadout
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSProjectionTrace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

local notation "SourceOp" lambda =>
  sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda

/-! ## The raw four-term readout contract -/

/-- A bounded readout for the already recombined raw four-term row. -/
structure SuffixRawAmbientBoundaryReadoutData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (bound : ℝ) where
  bound_nonneg : 0 ≤ bound
  readout : suffixEulerFrameAmbientBoundaryCarrier →L[ℂ]
    sourceSoninCarrier lambda
  readout_norm_le : ‖readout‖ ≤ bound
  factorization :
    readout ∘L suffixEulerFrameAmbientBoundaryAnalysis lambda p S =
      (suffixActualBandRawQuadraticIntertwiningDefect owner lambda p S)†

/-- The raw readout gives a mismatch readout after subtracting it from the
unconditional polar readout. -/
noncomputable def SuffixRawAmbientBoundaryReadoutData.toMismatch
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {bound : ℝ}
    (data : SuffixRawAmbientBoundaryReadoutData owner lambda p S bound) :
    SuffixMismatchAmbientBoundaryReadoutData owner lambda p S
      (‖detectorOperator owner‖ + bound) := by
  refine
    { readout := suffixActualBandPolarPhysicalReadout owner lambda S -
        data.readout
      readout_norm_le := ?_
      factorization := ?_ }
  · calc
      ‖suffixActualBandPolarPhysicalReadout owner lambda S - data.readout‖ =
          ‖suffixActualBandPolarPhysicalReadout owner lambda S +
            -data.readout‖ := by rw [sub_eq_add_neg]
      _ ≤ ‖suffixActualBandPolarPhysicalReadout owner lambda S‖ +
          ‖-data.readout‖ := ContinuousLinearMap.opNorm_add_le _ _
      _ = ‖suffixActualBandPolarPhysicalReadout owner lambda S‖ +
          ‖data.readout‖ := by rw [ContinuousLinearMap.opNorm_neg]
      _ ≤ ‖detectorOperator owner‖ + bound := add_le_add
        (suffixActualBandPolarPhysicalReadout_norm_le owner lambda S)
        data.readout_norm_le
  · have hpolar := suffixActualBandPolarPhysicalReadout_comp_analysis
      owner lambda p S
    have hraw := data.factorization
    have hsplit :=
      suffixActualBandRoutePolarRawMismatchIntertwiningDefect_eq_polar_sub_raw
        owner lambda p S
    have hadjoint_sub (A B : SourceOp lambda) :
        (A - B)† = A† - B† := by
      apply ContinuousLinearMap.ext
      intro y
      exact ext_inner_right ℂ fun z => by
        simp only [ContinuousLinearMap.adjoint_inner_left,
          ContinuousLinearMap.sub_apply, inner_sub_left, inner_sub_right]
    have hsplitAdjoint := congrArg ContinuousLinearMap.adjoint hsplit
    rw [hadjoint_sub] at hsplitAdjoint
    apply ContinuousLinearMap.ext
    intro x
    change (suffixActualBandPolarPhysicalReadout owner lambda S - data.readout)
        (suffixEulerFrameAmbientBoundaryAnalysis lambda p S x) = _
    have hsub :
        (suffixActualBandPolarPhysicalReadout owner lambda S - data.readout)
            (suffixEulerFrameAmbientBoundaryAnalysis lambda p S x) =
          suffixActualBandPolarPhysicalReadout owner lambda S
              (suffixEulerFrameAmbientBoundaryAnalysis lambda p S x) -
            data.readout (suffixEulerFrameAmbientBoundaryAnalysis lambda p S x) :=
      rfl
    rw [hsub]
    rw [show suffixActualBandPolarPhysicalReadout owner lambda S
          (suffixEulerFrameAmbientBoundaryAnalysis lambda p S x) =
        ((suffixActualBandPolarIntertwiningDefect owner lambda p S)†) x by
      exact congrArg (fun operator : SourceOp lambda => operator x) hpolar]
    rw [show data.readout
          (suffixEulerFrameAmbientBoundaryAnalysis lambda p S x) =
        ((suffixActualBandRawQuadraticIntertwiningDefect owner lambda p S)†) x by
      exact congrArg (fun operator : SourceOp lambda => operator x) hraw]
    have hsplitPoint := congrArg
      (fun operator : SourceOp lambda => operator x) hsplitAdjoint
    have hsplitPoint' :
        ((suffixActualBandRoutePolarRawMismatchIntertwiningDefect
          owner lambda p S)†) x =
          ((suffixActualBandPolarIntertwiningDefect owner lambda p S)†) x -
            ((suffixActualBandRawQuadraticIntertwiningDefect owner lambda p S)†) x := by
      simpa only [suffixActualBandPolarIntertwiningDefect,
        ContinuousLinearMap.sub_apply] using hsplitPoint
    exact hsplitPoint'.symm

/-! ## The reverse single-suffix conversion -/

/-- An existing mismatch readout supplies a raw readout by the polar
correction. -/
noncomputable def SuffixMismatchAmbientBoundaryReadoutData.toRaw
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {bound : ℝ}
    (data : SuffixMismatchAmbientBoundaryReadoutData owner lambda p S bound) :
    SuffixRawAmbientBoundaryReadoutData owner lambda p S
      (‖detectorOperator owner‖ + bound) := by
  have hbound : 0 ≤ bound := by
    exact le_trans (norm_nonneg data.readout) data.readout_norm_le
  exact
    { bound_nonneg := add_nonneg (norm_nonneg (detectorOperator owner)) hbound
      readout := rawCorrectionReadout data
      readout_norm_le := rawCorrection_norm_le data
      factorization := rawCorrection_factorization data }

/-! ## Uniform families -/

/-- One common raw-readout bound for every visible-prime/suffix pair. -/
structure SuffixRawAmbientBoundaryUniformReadoutData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (bound : ℝ) where
  bound_nonneg : 0 ≤ bound
  readout : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
    SuffixRawAmbientBoundaryReadoutData owner lambda p S bound

/-- A uniform raw readout family gives the uniform mismatch family with the
detector norm added once. -/
noncomputable def SuffixRawAmbientBoundaryUniformReadoutData.toMismatch
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {bound : ℝ}
    (data : SuffixRawAmbientBoundaryUniformReadoutData owner lambda bound) :
    SuffixMismatchAmbientBoundaryUniformReadoutData owner lambda
      (‖detectorOperator owner‖ + bound) :=
  { bound_nonneg := add_nonneg (norm_nonneg (detectorOperator owner))
      data.bound_nonneg
    readout := fun p S =>
      CCM24FiniteSCompletedJuliaRawPhysicalReadout.SuffixRawAmbientBoundaryReadoutData.toMismatch
        (data.readout p S) }

/-- A uniform mismatch readout family gives the uniform raw family with the
same detector cost. -/
noncomputable def SuffixMismatchAmbientBoundaryUniformReadoutData.toRaw
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {bound : ℝ}
    (data : SuffixMismatchAmbientBoundaryUniformReadoutData owner lambda bound) :
    SuffixRawAmbientBoundaryUniformReadoutData owner lambda
      (‖detectorOperator owner‖ + bound) :=
  { bound_nonneg := by
      have hbound : 0 ≤ bound := data.bound_nonneg
      exact add_nonneg (norm_nonneg (detectorOperator owner)) hbound
    readout := fun p S =>
      CCM24FiniteSCompletedJuliaRawPhysicalReadout.SuffixMismatchAmbientBoundaryReadoutData.toRaw
        (data.readout p S) }

/-! ## Exact existence-level reduction -/

/-- Existence of some finite uniform raw-readout bound is equivalent to
existence of some finite uniform mismatch-readout bound. The two numerical
bounds differ only by the fixed detector norm. -/
theorem exists_uniformRawReadout_iff_exists_uniformMismatchReadout
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    (∃ bound : ℝ,
      Nonempty (SuffixRawAmbientBoundaryUniformReadoutData owner lambda bound)) ↔
      (∃ bound : ℝ,
        Nonempty (SuffixMismatchAmbientBoundaryUniformReadoutData
          owner lambda bound)) := by
  constructor
  · rintro ⟨bound, ⟨data⟩⟩
    exact ⟨‖detectorOperator owner‖ + bound,
      ⟨data.toMismatch⟩⟩
  · rintro ⟨bound, ⟨data⟩⟩
    exact ⟨‖detectorOperator owner‖ + bound,
      ⟨SuffixMismatchAmbientBoundaryUniformReadoutData.toRaw data⟩⟩

/-- The raw four-term source obligation is also equivalent, at existence
level, to the family-uniform physical Douglas producer. -/
theorem exists_uniformRawReadout_iff_exists_uniformPhysicalDomination
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    (∃ bound : ℝ,
      Nonempty (SuffixRawAmbientBoundaryUniformReadoutData owner lambda bound)) ↔
      (∃ bound : ℝ,
        Nonempty (SuffixMismatchAmbientBoundaryUniformDominationData
          owner lambda bound)) := by
  rw [exists_uniformRawReadout_iff_exists_uniformMismatchReadout]
  constructor
  · rintro ⟨bound, hreadout⟩
    exact ⟨bound,
      (uniformDomination_iff_nonempty_uniformReadout owner lambda bound).mpr
        hreadout⟩
  · rintro ⟨bound, hdom⟩
    exact ⟨bound,
      (uniformDomination_iff_nonempty_uniformReadout owner lambda bound).mp
        hdom⟩

end CCM24FiniteSCompletedJuliaRawPhysicalReadout
end CCM25Concrete
end Source
end ConnesWeilRH
