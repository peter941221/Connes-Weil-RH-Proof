/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawDouglasReadout

/-!
# Raw co-defect factorization for the completed Julia row

Proof 538 rewrites the remaining raw four-term obligation as a direct
Douglas domination against the packed physical analysis column. The packed
column has exactly the same pointwise energy as the adjacent Julia
left co-defect.

This module converts that all-vector inequality into the actual right-factor
form

    rawDefect = leftCoDefect ∘ rightFactor.

No source-specific estimate is asserted here. The file only records the
operator-theoretic consequence of a successful raw Douglas producer.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedJuliaRawCoDefectFactor

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSDouglasFactor
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCompletedJuliaAmbientDefectFactorization
open CCM24FiniteSCompletedJuliaMismatchFactorization
open CCM24FiniteSCompletedJuliaRawDouglasReadout
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSJuliaBessel
open CCM24FiniteSJuliaCoDefect
open CCM24FiniteSProjectionTrace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) :
      CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

local notation "SourceOp" lambda =>
  sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda

/-! ## Single-suffix factor data -/

/-- A right factor through the actual adjacent Julia left co-defect for the
recombined raw four-term defect. -/
structure SuffixRawCoDefectFactorData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (bound : ℝ) where
  rightFactor : SourceOp lambda
  rightFactor_norm_le : ‖rightFactor‖ ≤ bound
  factorization :
    suffixActualBandRawQuadraticIntertwiningDefect owner lambda p S =
      (suffixEulerFrameSchurStep lambda p S).leftCoDefect ∘L rightFactor

/-- Raw Douglas domination factors the recombined raw defect through the
actual adjacent left co-defect, not merely through the packed product carrier. -/
noncomputable def suffixRawCoDefectFactorDataOfDomination
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (bound : ℝ)
    (hdom : SuffixRawAmbientBoundaryDomination owner lambda p S bound) :
    SuffixRawCoDefectFactorData owner lambda p S bound := by
  let rawDefect :=
    suffixActualBandRawQuadraticIntertwiningDefect owner lambda p S
  let leftCoDefect := (suffixEulerFrameSchurStep lambda p S).leftCoDefect
  have hraw : ∀ x : sourceSoninCarrier lambda,
      ‖(rawDefect†) x‖ ^ 2 ≤ bound ^ 2 * ‖leftCoDefect x‖ ^ 2 := by
    intro x
    have hpoint := hdom.2 x
    simpa only [rawDefect, leftCoDefect,
      suffixEulerFrameLeftCoDefect_normSq_eq_ambient_add_boundary]
      using hpoint
  let factorWitness := exists_factor_of_norm_sq_le (rawDefect†) leftCoDefect
    bound hdom.1 hraw
  let factorAdjoint := Classical.choose factorWitness
  have factorSpec := Classical.choose_spec factorWitness
  let rightFactor := factorAdjoint†
  have hrightNorm : ‖rightFactor‖ ≤ bound := by
    change ‖factorAdjoint†‖ ≤ bound
    calc
      ‖factorAdjoint†‖ = ‖factorAdjoint‖ :=
        ContinuousLinearMap.adjoint.norm_map factorAdjoint
      _ ≤ bound := by
        simpa only [factorAdjoint] using factorSpec.1
  have hfactor : rawDefect = leftCoDefect ∘L rightFactor := by
    have hadjoint := congrArg ContinuousLinearMap.adjoint factorSpec.2
    have hself : IsSelfAdjoint leftCoDefect := by
      simpa only [leftCoDefect,
        RectangularSchurCoDefectStepData.leftCoDefect] using
        (canonicalJuliaDefect_isSelfAdjoint
          (ContinuousLinearMap.adjoint
            (suffixEulerFrameSchurStep lambda p S).transition)
          (suffixEulerFrameSchurStep lambda p S).transitionAdjointContract)
    have hadjoint' : leftCoDefect ∘L rightFactor = rawDefect := by
      simpa only [rightFactor, factorAdjoint,
        ContinuousLinearMap.adjoint_comp,
        ContinuousLinearMap.adjoint_adjoint, hself.adjoint_eq] using hadjoint
    exact hadjoint'.symm
  exact
    { rightFactor := rightFactor
      rightFactor_norm_le := hrightNorm
      factorization := hfactor }

/-- A raw co-defect factor is already the direct raw Douglas domination.
Thus the factor structure stores no extra analytic estimate beyond the
all-vector inequality. -/
theorem SuffixRawCoDefectFactorData.domination
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {bound : ℝ}
    (data : SuffixRawCoDefectFactorData owner lambda p S bound) :
    SuffixRawAmbientBoundaryDomination owner lambda p S bound := by
  have hbound : 0 ≤ bound :=
    le_trans (norm_nonneg data.rightFactor) data.rightFactor_norm_le
  refine ⟨hbound, ?_⟩
  intro x
  have hadjoint := congrArg ContinuousLinearMap.adjoint data.factorization
  have hself : IsSelfAdjoint
      (suffixEulerFrameSchurStep lambda p S).leftCoDefect := by
    simpa only [RectangularSchurCoDefectStepData.leftCoDefect] using
      (canonicalJuliaDefect_isSelfAdjoint
        (ContinuousLinearMap.adjoint
          (suffixEulerFrameSchurStep lambda p S).transition)
        (suffixEulerFrameSchurStep lambda p S).transitionAdjointContract)
  have hmap :
      (suffixActualBandRawQuadraticIntertwiningDefect owner lambda p S)† =
        (data.rightFactor)† ∘L
          (suffixEulerFrameSchurStep lambda p S).leftCoDefect := by
    simpa only [ContinuousLinearMap.adjoint_comp, hself.adjoint_eq] using
      hadjoint
  have hnorm :
      ‖((suffixActualBandRawQuadraticIntertwiningDefect
          owner lambda p S)†) x‖ ≤
        bound * ‖(suffixEulerFrameSchurStep lambda p S).leftCoDefect x‖ := by
    rw [hmap]
    calc
      ‖((data.rightFactor)†)
          ((suffixEulerFrameSchurStep lambda p S).leftCoDefect x)‖ ≤
          ‖(data.rightFactor)†‖ *
            ‖(suffixEulerFrameSchurStep lambda p S).leftCoDefect x‖ :=
        (data.rightFactor)†.le_opNorm _
      _ = ‖data.rightFactor‖ *
            ‖(suffixEulerFrameSchurStep lambda p S).leftCoDefect x‖ := by
        exact congrArg
          (fun value : ℝ => value *
            ‖(suffixEulerFrameSchurStep lambda p S).leftCoDefect x‖)
          (ContinuousLinearMap.adjoint.norm_map data.rightFactor)
      _ ≤ bound *
            ‖(suffixEulerFrameSchurStep lambda p S).leftCoDefect x‖ := by
        exact mul_le_mul_of_nonneg_right data.rightFactor_norm_le
          (norm_nonneg _)
  calc
    ‖((suffixActualBandRawQuadraticIntertwiningDefect
        owner lambda p S)†) x‖ ^ 2 ≤
        (bound *
          ‖(suffixEulerFrameSchurStep lambda p S).leftCoDefect x‖) ^ 2 := by
      exact (sq_le_sq₀ (norm_nonneg _)
        (mul_nonneg hbound (norm_nonneg _))).mpr hnorm
    _ = bound ^ 2 *
        ‖(suffixEulerFrameSchurStep lambda p S).leftCoDefect x‖ ^ 2 := by
      rw [mul_pow]
    _ = bound ^ 2 *
        (‖suffixEulerFrameAmbientLossColumn lambda p S x‖ ^ 2 +
          ‖(ContinuousLinearMap.adjoint
            (suffixEulerFrameSchurStep lambda p S).boundary) x‖ ^ 2) := by
      rw [suffixEulerFrameLeftCoDefect_normSq_eq_ambient_add_boundary]

/-- The single-suffix raw Douglas inequality is equivalent to the raw
right-factor contract through the actual left co-defect. -/
theorem suffixRawAmbientBoundaryDomination_iff_nonempty_coDefectFactorData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (bound : ℝ) :
    SuffixRawAmbientBoundaryDomination owner lambda p S bound ↔
      Nonempty (SuffixRawCoDefectFactorData owner lambda p S bound) := by
  constructor
  · intro hdom
    exact ⟨suffixRawCoDefectFactorDataOfDomination
      owner lambda p S bound hdom⟩
  · rintro ⟨data⟩
    exact data.domination

/-- Every successful raw co-defect factor passes the exact kernel guard:
a vector killed by the left co-defect is killed by the raw four-term adjoint. -/
theorem SuffixRawCoDefectFactorData.rawAdjoint_eq_zero_of_leftCoDefect_eq_zero
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {bound : ℝ}
    (data : SuffixRawCoDefectFactorData owner lambda p S bound)
    {x : sourceSoninCarrier lambda}
    (hx : (suffixEulerFrameSchurStep lambda p S).leftCoDefect x = 0) :
    ((suffixActualBandRawQuadraticIntertwiningDefect
      owner lambda p S)†) x = 0 := by
  have hadjoint := congrArg ContinuousLinearMap.adjoint data.factorization
  have hself : IsSelfAdjoint
      (suffixEulerFrameSchurStep lambda p S).leftCoDefect := by
    simpa only [RectangularSchurCoDefectStepData.leftCoDefect] using
      (canonicalJuliaDefect_isSelfAdjoint
        (ContinuousLinearMap.adjoint
          (suffixEulerFrameSchurStep lambda p S).transition)
        (suffixEulerFrameSchurStep lambda p S).transitionAdjointContract)
  have hmap :
      (suffixActualBandRawQuadraticIntertwiningDefect owner lambda p S)† =
        (data.rightFactor)† ∘L
          (suffixEulerFrameSchurStep lambda p S).leftCoDefect := by
    simpa only [ContinuousLinearMap.adjoint_comp, hself.adjoint_eq] using
      hadjoint
  rw [hmap]
  simp only [ContinuousLinearMap.comp_apply, hx, map_zero]

/-! ## Uniform-family factor data -/

/-- One raw co-defect right factor for every visible-prime/suffix pair, with
one shared numerical bound. -/
structure SuffixRawCoDefectUniformFactorData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (bound : ℝ) where
  bound_nonneg : 0 ≤ bound
  factor : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
    SuffixRawCoDefectFactorData owner lambda p S bound

/-- A uniform raw Douglas producer gives uniform raw co-defect factors. -/
noncomputable def
    suffixRawCoDefectUniformFactorDataOfDominationData
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {bound : ℝ}
    (data : SuffixRawAmbientBoundaryUniformDominationData
      owner lambda bound) :
    SuffixRawCoDefectUniformFactorData owner lambda bound :=
  { bound_nonneg := data.bound_nonneg
    factor := fun p S =>
      suffixRawCoDefectFactorDataOfDomination owner lambda p S bound
        (data.domination p S) }

/-- Conversely, a uniform raw co-defect factor family is already a uniform
raw Douglas producer. -/
noncomputable def
    SuffixRawCoDefectUniformFactorData.toDomination
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {bound : ℝ}
    (data : SuffixRawCoDefectUniformFactorData owner lambda bound) :
    SuffixRawAmbientBoundaryUniformDominationData owner lambda bound :=
  { bound_nonneg := data.bound_nonneg
    domination := fun p S => (data.factor p S).domination }

/-- Uniform raw Douglas domination is equivalent to uniform raw co-defect
right-factor data, with the same numerical bound. -/
theorem uniformRawDomination_iff_nonempty_uniformCoDefectFactor
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (bound : ℝ) :
    Nonempty (SuffixRawAmbientBoundaryUniformDominationData
      owner lambda bound) ↔
      Nonempty (SuffixRawCoDefectUniformFactorData owner lambda bound) := by
  constructor
  · rintro ⟨data⟩
    exact ⟨suffixRawCoDefectUniformFactorDataOfDominationData data⟩
  · rintro ⟨data⟩
    exact ⟨data.toDomination⟩

/-- Existence of some finite uniform raw Douglas bound is exactly existence
of some finite uniform raw co-defect factor bound. -/
theorem exists_uniformRawDomination_iff_exists_uniformCoDefectFactor
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    (∃ bound : ℝ,
      Nonempty
        (SuffixRawAmbientBoundaryUniformDominationData
          owner lambda bound)) ↔
      (∃ bound : ℝ,
        Nonempty
          (SuffixRawCoDefectUniformFactorData owner lambda bound)) := by
  constructor
  · rintro ⟨bound, hdata⟩
    exact ⟨bound,
      (uniformRawDomination_iff_nonempty_uniformCoDefectFactor
        owner lambda bound).mp hdata⟩
  · rintro ⟨bound, hdata⟩
    exact ⟨bound,
      (uniformRawDomination_iff_nonempty_uniformCoDefectFactor
        owner lambda bound).mpr hdata⟩

end CCM24FiniteSCompletedJuliaRawCoDefectFactor
end CCM25Concrete
end Source
end ConnesWeilRH
