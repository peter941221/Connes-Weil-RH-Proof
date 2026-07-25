/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaNonpolarGapKernel
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSDouglasFactor

/-!
# Direct Douglas gate for the non-polar gap

Proof 542 reduced Gate 3U to a uniform non-polar gap factor. This module
states and consumes the exact all-vector Douglas inequality which would
produce that factor:

    ||gap^dagger x||^2 <= C^2 ||leftCoDefect x||^2.

The file proves the operator-theoretic handoff from that inequality to the
factor family and then to the physical domination owner. It does not prove
the source-specific inequality itself.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedJuliaNonpolarGapDouglas

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSDouglasFactor
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCompletedJuliaNonpolarGapFactorBridge
open CCM24FiniteSCompletedJuliaNonpolarGapKernel
open CCM24FiniteSCompletedJuliaPolarSlotBound
open CCM24FiniteSCompletedJuliaSignedLocalization
open CCM24FiniteSCompletedJuliaUniformRawReadout
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSJuliaBessel
open CCM24FiniteSJuliaCoDefect

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) :
      CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

local notation "SourceOp" lambda =>
  sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda

/-! ## Single-suffix Douglas contract -/

/-- Direct Douglas domination for the exact non-polar localization gap.
The gap is the recombined first-jet plus route/polar ordering residual from
Proof 502; it is not split before the estimate. -/
def SuffixLocalNonpolarGapDouglasDomination
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (bound : ℝ) : Prop :=
  0 ≤ bound ∧
    ∀ x : sourceSoninCarrier lambda,
      ‖((suffixActualBandLocalNonpolarLocalizationGap
          owner lambda p S)†) x‖ ^ 2 ≤
        bound ^ 2 *
          ‖(suffixEulerFrameSchurStep lambda p S).leftCoDefect x‖ ^ 2

/-- The direct Douglas inequality produces the correctly oriented right
factor through the adjacent Julia left co-defect. -/
noncomputable def suffixLocalNonpolarGapCoDefectFactorDataOfDomination
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (bound : ℝ)
    (hdom : SuffixLocalNonpolarGapDouglasDomination
      owner lambda p S bound) :
    SuffixLocalNonpolarGapCoDefectFactorData owner lambda p S bound := by
  let gap := suffixActualBandLocalNonpolarLocalizationGap owner lambda p S
  let leftCoDefect := (suffixEulerFrameSchurStep lambda p S).leftCoDefect
  let factorWitness := exists_factor_of_norm_sq_le (gap†) leftCoDefect
    bound hdom.1 (by
      intro x
      simpa only [gap, leftCoDefect] using hdom.2 x)
  let factorAdjoint := Classical.choose factorWitness
  have factorSpec := Classical.choose_spec factorWitness
  let completion := factorAdjoint†
  have hcompletionNorm : ‖completion‖ ≤ bound := by
    change ‖factorAdjoint†‖ ≤ bound
    calc
      ‖factorAdjoint†‖ = ‖factorAdjoint‖ :=
        ContinuousLinearMap.adjoint.norm_map factorAdjoint
      _ ≤ bound := by
        simpa only [factorAdjoint] using factorSpec.1
  have hfactor : gap = leftCoDefect ∘L completion := by
    have hadjoint := congrArg ContinuousLinearMap.adjoint factorSpec.2
    have hself : IsSelfAdjoint leftCoDefect := by
      simpa only [leftCoDefect,
        RectangularSchurCoDefectStepData.leftCoDefect] using
        (canonicalJuliaDefect_isSelfAdjoint
          (ContinuousLinearMap.adjoint
            (suffixEulerFrameSchurStep lambda p S).transition)
          (suffixEulerFrameSchurStep lambda p S).transitionAdjointContract)
    have hadjoint' : leftCoDefect ∘L completion = gap := by
      simpa only [completion, factorAdjoint,
        ContinuousLinearMap.adjoint_comp,
        ContinuousLinearMap.adjoint_adjoint, hself.adjoint_eq] using hadjoint
    exact hadjoint'.symm
  exact
    { bound_nonneg := hdom.1
      completion := completion
      completion_norm_le := hcompletionNorm
      factorization := by
        simpa only [gap, leftCoDefect] using hfactor }

/-- Conversely, a non-polar gap factor is exactly the same Douglas
domination, with the same bound. -/
theorem SuffixLocalNonpolarGapCoDefectFactorData.domination
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {bound : ℝ}
    (data : SuffixLocalNonpolarGapCoDefectFactorData
      owner lambda p S bound) :
    SuffixLocalNonpolarGapDouglasDomination owner lambda p S bound := by
  refine ⟨data.bound_nonneg, ?_⟩
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
      (suffixActualBandLocalNonpolarLocalizationGap owner lambda p S)† =
        (data.completion)† ∘L
          (suffixEulerFrameSchurStep lambda p S).leftCoDefect := by
    simpa only [ContinuousLinearMap.adjoint_comp, hself.adjoint_eq] using
      hadjoint
  have hnorm :
      ‖((suffixActualBandLocalNonpolarLocalizationGap
          owner lambda p S)†) x‖ ≤
        bound * ‖(suffixEulerFrameSchurStep lambda p S).leftCoDefect x‖ := by
    rw [hmap]
    calc
      ‖(ContinuousLinearMap.adjoint data.completion)
          ((suffixEulerFrameSchurStep lambda p S).leftCoDefect x)‖ ≤
          ‖ContinuousLinearMap.adjoint data.completion‖ *
            ‖(suffixEulerFrameSchurStep lambda p S).leftCoDefect x‖ :=
        (ContinuousLinearMap.adjoint data.completion).le_opNorm _
      _ = ‖data.completion‖ *
            ‖(suffixEulerFrameSchurStep lambda p S).leftCoDefect x‖ := by
        exact congrArg
          (fun value : ℝ => value *
            ‖(suffixEulerFrameSchurStep lambda p S).leftCoDefect x‖)
          (ContinuousLinearMap.adjoint.norm_map data.completion)
      _ ≤ bound *
            ‖(suffixEulerFrameSchurStep lambda p S).leftCoDefect x‖ := by
        exact mul_le_mul_of_nonneg_right data.completion_norm_le
          (norm_nonneg _)
  calc
    ‖((suffixActualBandLocalNonpolarLocalizationGap
        owner lambda p S)†) x‖ ^ 2 ≤
        (bound *
          ‖(suffixEulerFrameSchurStep lambda p S).leftCoDefect x‖) ^ 2 := by
      exact (sq_le_sq₀ (norm_nonneg _)
        (mul_nonneg data.bound_nonneg (norm_nonneg _))).mpr hnorm
    _ = bound ^ 2 *
        ‖(suffixEulerFrameSchurStep lambda p S).leftCoDefect x‖ ^ 2 := by
      rw [mul_pow]

/-- The direct non-polar gap Douglas inequality is equivalent to the
non-polar gap co-defect factor data. -/
theorem suffixLocalNonpolarGapDouglasDomination_iff_nonempty_factorData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (bound : ℝ) :
    SuffixLocalNonpolarGapDouglasDomination owner lambda p S bound ↔
      Nonempty (SuffixLocalNonpolarGapCoDefectFactorData
        owner lambda p S bound) := by
  constructor
  · intro hdom
    exact ⟨suffixLocalNonpolarGapCoDefectFactorDataOfDomination
      owner lambda p S bound hdom⟩
  · rintro ⟨data⟩
    exact SuffixLocalNonpolarGapCoDefectFactorData.domination data

/-! ## Uniform-family handoff -/

/-- One direct Douglas bound for the non-polar gap at every visible
prime/suffix pair. -/
structure SuffixLocalNonpolarGapUniformDouglasData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (bound : ℝ) where
  bound_nonneg : 0 ≤ bound
  domination : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
    SuffixLocalNonpolarGapDouglasDomination owner lambda p S bound

/-- A uniform direct Douglas producer gives the uniform non-polar gap factor
family consumed by Proof 542. -/
noncomputable def SuffixLocalNonpolarGapUniformDouglasData.toFactorData
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {bound : ℝ}
    (data : SuffixLocalNonpolarGapUniformDouglasData owner lambda bound) :
    SuffixLocalNonpolarGapCoDefectUniformFactorData owner lambda bound :=
  { bound_nonneg := data.bound_nonneg
    factor := fun p S =>
      suffixLocalNonpolarGapCoDefectFactorDataOfDomination
        owner lambda p S bound (data.domination p S) }

/-- Conversely, a uniform non-polar gap factor family is already the same
direct Douglas estimate. -/
noncomputable def SuffixLocalNonpolarGapCoDefectUniformFactorData.toDouglas
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {bound : ℝ}
    (data : SuffixLocalNonpolarGapCoDefectUniformFactorData owner lambda bound) :
    SuffixLocalNonpolarGapUniformDouglasData owner lambda bound :=
  { bound_nonneg := data.bound_nonneg
    domination := fun p S =>
      SuffixLocalNonpolarGapCoDefectFactorData.domination (data.factor p S) }

/-- Uniform direct Douglas domination is equivalent to the uniform factor
family at the same numerical bound. -/
theorem uniformNonpolarGapDouglas_iff_nonempty_uniformFactor
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (bound : ℝ) :
    Nonempty (SuffixLocalNonpolarGapUniformDouglasData owner lambda bound) ↔
      Nonempty (SuffixLocalNonpolarGapCoDefectUniformFactorData
        owner lambda bound) := by
  constructor
  · rintro ⟨data⟩
    exact ⟨data.toFactorData⟩
  · rintro ⟨data⟩
    exact ⟨SuffixLocalNonpolarGapCoDefectUniformFactorData.toDouglas data⟩

/-- Existence of a finite direct Douglas bound for the non-polar gap is
equivalent to the Proof 542 non-polar factor producer. -/
theorem exists_uniformNonpolarGapDouglas_iff_exists_uniformFactor
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    (∃ bound : ℝ,
      Nonempty (SuffixLocalNonpolarGapUniformDouglasData
        owner lambda bound)) ↔
      (∃ bound : ℝ,
        Nonempty (SuffixLocalNonpolarGapCoDefectUniformFactorData
          owner lambda bound)) := by
  constructor
  · rintro ⟨bound, hdata⟩
    exact ⟨bound,
      (uniformNonpolarGapDouglas_iff_nonempty_uniformFactor
        owner lambda bound).mp hdata⟩
  · rintro ⟨bound, hdata⟩
    exact ⟨bound,
      (uniformNonpolarGapDouglas_iff_nonempty_uniformFactor
        owner lambda bound).mpr hdata⟩

/-- This is the final formal handoff: the direct non-polar gap Douglas
estimate is exactly as strong as the existing family-uniform physical
domination producer. The missing source work is the estimate itself. -/
theorem exists_uniformNonpolarGapDouglas_iff_exists_uniformPhysicalDomination
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    (∃ bound : ℝ,
      Nonempty (SuffixLocalNonpolarGapUniformDouglasData
        owner lambda bound)) ↔
      (∃ bound : ℝ,
        Nonempty (SuffixMismatchAmbientBoundaryUniformDominationData
          owner lambda bound)) :=
  (exists_uniformNonpolarGapDouglas_iff_exists_uniformFactor owner lambda).trans
    (exists_uniformNonpolarGapFactor_iff_exists_uniformPhysicalDomination
      owner lambda)

end CCM24FiniteSCompletedJuliaNonpolarGapDouglas
end CCM25Concrete
end Source
end ConnesWeilRH
