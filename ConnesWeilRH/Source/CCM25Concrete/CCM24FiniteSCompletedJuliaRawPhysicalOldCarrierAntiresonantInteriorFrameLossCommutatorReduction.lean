/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorAmbientFrameLossStability
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorBalancedProjectionRawLedger

/-!
# Relative commutator reduction of ambient frame-loss stability

Proof 670 isolates the sufficient frame-loss estimate

```text
‖A_p P_S u‖ ≤ K ‖A_p u‖,
```

where `A_p` is the actual adjoint ambient loss and
`P_S = F_S F_S†` is the new suffix-frame range projection.  This module
identifies both objects exactly:

```text
A_p = s_p (I + U_(log p)),
P_S = starProjection_(semilocal Sonin S).
```

Since `P_S` is contractive, frame-loss stability exists exactly when the
translation/Sonin commutator is relatively bounded in the antiresonant graph
norm:

```text
‖[U_(log p), P_S] u‖ ≤ L ‖(I + U_(log p)) u‖.
```

The two directions change a supplied constant only by adding one.  An
ordinary operator-norm commutator estimate is not this statement because
`I + U_(log p)` has no bounded inverse.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace AntiresonantFrameLossCommutator

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSActualMovingProjection
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCompletedJuliaAmbientDefectFactorization
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorAdjacentProjectionGap
open AmbientFrameLossStability
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorBalancedProjectionRawLedger
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorPairedCorrelationCoboundary
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorRouteValidFactorization
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorSingleChannelColumnEquivalence
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorTwoStepCoboundaryFactorization
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantRadialBlockRecurrence
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSGramProjectionCalculus
open CCM24FiniteSProjectionTrace
open CCM24FiniteSParameterizedSoninSubspace
open CCM24UnitScaleProlateAlignment
open TwoStepFactorCollapse

/-! ## Removing the harmless positive loss scale -/

/-- A common positive real scalar cancels from a same-vector norm
domination. -/
theorem norm_real_smul_le_iff_of_pos
    {H : Type*} [NormedAddCommGroup H] [NormedSpace Complex H]
    (scale bound : Real) (hscale : 0 < scale) (x y : H) :
    ‖(scale : Complex) • x‖ ≤
        bound * ‖(scale : Complex) • y‖ ↔
      ‖x‖ ≤ bound * ‖y‖ := by
  simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hscale]
  rw [show bound * (scale * ‖y‖) = scale * (bound * ‖y‖) by ring]
  exact mul_le_mul_iff_of_pos_left hscale

/-- Frame-loss stability after the positive Euler scale is removed. -/
def SuffixCompleteCoupledRouteUniformAntiresonantCoreProjectionDomination
    (bound : Real) : Prop :=
  0 ≤ bound ∧
    ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixRouteValidStep p S → ∀ u : finiteSCarrier,
        ‖primeEulerAntiresonantCore p
            (newSuffixRangeProjection unitSoninScale S u)‖ ≤
          bound * ‖primeEulerAntiresonantCore p u‖

/-- For one point, the scaled ambient-loss domination and the unscaled
antiresonant-core domination are equivalent with the same constant. -/
theorem ambientLossProjection_domination_iff_core
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
    (bound : Real) (u : finiteSCarrier) :
    ‖((primeEulerAmbientLossFactor p)†)
        (newSuffixRangeProjection unitSoninScale S u)‖ ≤
        bound * ‖((primeEulerAmbientLossFactor p)†) u‖ ↔
      ‖primeEulerAntiresonantCore p
          (newSuffixRangeProjection unitSoninScale S u)‖ ≤
        bound * ‖primeEulerAntiresonantCore p u‖ := by
  have hscale : 0 < primeEulerAmbientLossScale p :=
    primeEulerAmbientLossScale_pos p
  rw [primeEulerAmbientLossFactor_adjoint_eq]
  change
    ‖(primeEulerAmbientLossScale p : Complex) •
        primeEulerAntiresonantCore p
          (newSuffixRangeProjection unitSoninScale S u)‖ ≤
        bound * ‖(primeEulerAmbientLossScale p : Complex) •
          primeEulerAntiresonantCore p u‖ ↔ _
  exact norm_real_smul_le_iff_of_pos
    (primeEulerAmbientLossScale p) bound hscale _ _

/-- Proof 670's frame-loss predicate is exactly the unscaled core/projection
predicate with the same bound. -/
theorem routeUniformAmbientFrameLossStability_iff_coreProjectionDomination
    (bound : Real) :
    SuffixCompleteCoupledRouteUniformAmbientFrameLossStability bound ↔
      SuffixCompleteCoupledRouteUniformAntiresonantCoreProjectionDomination
        bound := by
  constructor
  · rintro ⟨hbound, hstability⟩
    refine ⟨hbound, ?_⟩
    intro p S hvalid u
    apply (ambientLossProjection_domination_iff_core p S bound u).mp
    simpa only [newSuffixRangeProjection,
      ContinuousLinearMap.comp_apply] using hstability p S hvalid u
  · rintro ⟨hbound, hcore⟩
    refine ⟨hbound, ?_⟩
    intro p S hvalid u
    have hloss :=
      (ambientLossProjection_domination_iff_core p S bound u).mpr
        (hcore p S hvalid u)
    simpa only [newSuffixRangeProjection,
      ContinuousLinearMap.comp_apply] using hloss

/-! ## The actual Sonin projection and its translation commutator -/

/-- The frame projection in Proof 670 is literally the canonical semilocal
Sonin orthogonal projection. -/
theorem newSuffixRangeProjection_eq_semilocalSoninStarProjection
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    newSuffixRangeProjection lambda S =
      (ccm24SemilocalSoninClosedSubspace lambda S).toSubmodule.starProjection := by
  rw [newSuffixRangeProjection_eq_parameterizedCanonicalGramProjection,
    parameterizedCanonicalGramProjection_one]

/-- Hence the actual suffix-frame range projection is contractive on every
ambient vector. -/
theorem norm_newSuffixRangeProjection_apply_le
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime)
    (u : finiteSCarrier) :
    ‖newSuffixRangeProjection lambda S u‖ ≤ ‖u‖ := by
  rw [newSuffixRangeProjection_eq_semilocalSoninStarProjection]
  exact Submodule.norm_starProjection_apply_le _ _

/-- The genuine positive prime-log translation as a named operator. -/
noncomputable def primePositiveLogTranslationOperator
    (p : CCM24VisiblePrime) :
    finiteSCarrier →L[Complex] finiteSCarrier :=
  (cc20GlobalLogTranslation (Real.log p)).toContinuousLinearMap

/-- The exact source object left after removing the contractive projected
copy of the antiresonant loss. -/
noncomputable def suffixPrimeTranslationProjectionCommutator
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime) :
    finiteSCarrier →L[Complex] finiteSCarrier :=
  cc20Commutator (primePositiveLogTranslationOperator p)
    (newSuffixRangeProjection unitSoninScale S)

/-- The route-uniform relative commutator estimate.  Its denominator is the
actual antiresonant core, not the ambient norm of `u`. -/
def SuffixCompleteCoupledRouteUniformPrimeTranslationProjectionCommutatorDomination
    (bound : Real) : Prop :=
  0 ≤ bound ∧
    ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixRouteValidStep p S → ∀ u : finiteSCarrier,
        ‖suffixPrimeTranslationProjectionCommutator p S u‖ ≤
          bound * ‖primeEulerAntiresonantCore p u‖

/-- Adding the identity to the translation does not change its commutator
with the Sonin projection. -/
theorem antiresonantCore_projection_commutator_eq_translation
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime) :
    cc20Commutator (primeEulerAntiresonantCore p)
        (newSuffixRangeProjection unitSoninScale S) =
      suffixPrimeTranslationProjectionCommutator p S := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [cc20Commutator, primeEulerAntiresonantCore,
    suffixPrimeTranslationProjectionCommutator,
    primePositiveLogTranslationOperator,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.id_apply, map_add]
  abel

/-- Exact pointwise split of the projected core into its contractive part
and the relative translation commutator. -/
theorem antiresonantCore_projection_eq_commutator_add
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
    (u : finiteSCarrier) :
    primeEulerAntiresonantCore p
        (newSuffixRangeProjection unitSoninScale S u) =
      suffixPrimeTranslationProjectionCommutator p S u +
        newSuffixRangeProjection unitSoninScale S
          (primeEulerAntiresonantCore p u) := by
  have hoperator :=
    antiresonantCore_projection_commutator_eq_translation p S
  have hpoint := DFunLike.congr_fun hoperator u
  simp only [cc20Commutator, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply] at hpoint
  rw [← hpoint]
  abel

/-- Reverse pointwise form used to recover the commutator from a frame-loss
bound. -/
theorem translationProjectionCommutator_eq_core_sub_projection
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
    (u : finiteSCarrier) :
    suffixPrimeTranslationProjectionCommutator p S u =
      primeEulerAntiresonantCore p
          (newSuffixRangeProjection unitSoninScale S u) -
        newSuffixRangeProjection unitSoninScale S
          (primeEulerAntiresonantCore p u) := by
  rw [antiresonantCore_projection_eq_commutator_add]
  abel

/-! ## Equivalence up to the unavoidable contractive copy -/

/-- A relative commutator bound `L` gives frame-loss stability `L + 1`. -/
theorem coreProjectionDomination_of_relativeCommutatorDomination
    {bound : Real}
    (hcommutator :
      SuffixCompleteCoupledRouteUniformPrimeTranslationProjectionCommutatorDomination
        bound) :
    SuffixCompleteCoupledRouteUniformAntiresonantCoreProjectionDomination
      (bound + 1) := by
  refine ⟨add_nonneg hcommutator.1 zero_le_one, ?_⟩
  intro p S hvalid u
  rw [antiresonantCore_projection_eq_commutator_add]
  calc
    ‖suffixPrimeTranslationProjectionCommutator p S u +
        newSuffixRangeProjection unitSoninScale S
          (primeEulerAntiresonantCore p u)‖ ≤
        ‖suffixPrimeTranslationProjectionCommutator p S u‖ +
          ‖newSuffixRangeProjection unitSoninScale S
            (primeEulerAntiresonantCore p u)‖ := norm_add_le _ _
    _ ≤ bound * ‖primeEulerAntiresonantCore p u‖ +
          ‖primeEulerAntiresonantCore p u‖ :=
      add_le_add (hcommutator.2 p S hvalid u)
        (norm_newSuffixRangeProjection_apply_le unitSoninScale S _)
    _ = (bound + 1) * ‖primeEulerAntiresonantCore p u‖ := by ring

/-- Conversely, frame-loss stability `K` bounds the relative commutator by
`K + 1`. -/
theorem relativeCommutatorDomination_of_coreProjectionDomination
    {bound : Real}
    (hprojection :
      SuffixCompleteCoupledRouteUniformAntiresonantCoreProjectionDomination
        bound) :
    SuffixCompleteCoupledRouteUniformPrimeTranslationProjectionCommutatorDomination
      (bound + 1) := by
  refine ⟨add_nonneg hprojection.1 zero_le_one, ?_⟩
  intro p S hvalid u
  rw [translationProjectionCommutator_eq_core_sub_projection]
  calc
    ‖primeEulerAntiresonantCore p
          (newSuffixRangeProjection unitSoninScale S u) -
        newSuffixRangeProjection unitSoninScale S
          (primeEulerAntiresonantCore p u)‖ ≤
        ‖primeEulerAntiresonantCore p
          (newSuffixRangeProjection unitSoninScale S u)‖ +
          ‖newSuffixRangeProjection unitSoninScale S
            (primeEulerAntiresonantCore p u)‖ := norm_sub_le _ _
    _ ≤ bound * ‖primeEulerAntiresonantCore p u‖ +
          ‖primeEulerAntiresonantCore p u‖ :=
      add_le_add (hprojection.2 p S hvalid u)
        (norm_newSuffixRangeProjection_apply_le unitSoninScale S _)
    _ = (bound + 1) * ‖primeEulerAntiresonantCore p u‖ := by ring

/-- Existence of a route-uniform frame-loss constant is exactly existence of
a route-uniform relative translation/Sonin commutator constant. -/
theorem exists_routeUniformAmbientFrameLossStability_iff_relativeCommutatorDomination :
    (∃ bound : Real,
      SuffixCompleteCoupledRouteUniformAmbientFrameLossStability bound) ↔
      ∃ bound : Real,
        SuffixCompleteCoupledRouteUniformPrimeTranslationProjectionCommutatorDomination
          bound := by
  constructor
  · rintro ⟨bound, hstability⟩
    have hcore :=
      (routeUniformAmbientFrameLossStability_iff_coreProjectionDomination
        bound).mp hstability
    exact ⟨bound + 1,
      relativeCommutatorDomination_of_coreProjectionDomination hcore⟩
  · rintro ⟨bound, hcommutator⟩
    have hcore :=
      coreProjectionDomination_of_relativeCommutatorDomination hcommutator
    exact ⟨bound + 1,
      (routeUniformAmbientFrameLossStability_iff_coreProjectionDomination
        (bound + 1)).mpr hcore⟩

/-! ## Direct handoff to the existing factor consumers -/

/-- Restricted raw Bone 1 plus the relative commutator estimate constructs
the full ambient quotient with bound `B * (L + 1)`. -/
noncomputable def routeUniformAmbientLossFactorOfRawAmbientDominationAndRelativeCommutator
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {rawBound commutatorBound : Real}
    (hraw :
      SuffixRawOldCarrierAntiresonantInteriorRouteUniformRawAmbientDomination
        owner unitSoninScale rawBound)
    (hcommutator :
      SuffixCompleteCoupledRouteUniformPrimeTranslationProjectionCommutatorDomination
        commutatorBound) :
    SuffixCompleteCoupledRouteUniformAmbientLossFactor owner
      (rawBound * (commutatorBound + 1)) := by
  have hcore :=
    coreProjectionDomination_of_relativeCommutatorDomination hcommutator
  have hstability :=
    (routeUniformAmbientFrameLossStability_iff_coreProjectionDomination
      (commutatorBound + 1)).mpr hcore
  exact
    routeUniformAmbientLossFactorOfRawAmbientDominationAndFrameLossStability
      hraw hstability

/-- The same two inputs reach Proof 669's two-step factor with no additional
constant. -/
theorem routeUniformTwoStepFactorOfRawAmbientDominationAndRelativeCommutator
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {rawBound commutatorBound : Real}
    (hraw :
      SuffixRawOldCarrierAntiresonantInteriorRouteUniformRawAmbientDomination
        owner unitSoninScale rawBound)
    (hcommutator :
      SuffixCompleteCoupledRouteUniformPrimeTranslationProjectionCommutatorDomination
        commutatorBound) :
    SuffixCompleteCoupledRouteUniformScaledTwoStepCoboundaryFactor owner
      (rawBound * (commutatorBound + 1)) :=
  (routeUniformTwoStepFactor_iff_ambientLossFactor owner
    (rawBound * (commutatorBound + 1))).mpr
      (routeUniformAmbientLossFactorOfRawAmbientDominationAndRelativeCommutator
        hraw hcommutator)

/-- The relative commutator route reaches the paired finite-horizon
envelope. -/
theorem pairedAdjointCoboundaryEnvelopeBoundOfRawAmbientDominationAndRelativeCommutator
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {rawBound commutatorBound : Real}
    (hraw :
      SuffixRawOldCarrierAntiresonantInteriorRouteUniformRawAmbientDomination
        owner unitSoninScale rawBound)
    (hcommutator :
      SuffixCompleteCoupledRouteUniformPrimeTranslationProjectionCommutatorDomination
        commutatorBound) :
    SuffixCompleteCoupledRoutePairedAdjointCoboundaryEnvelopeBound owner :=
  pairedAdjointCoboundaryEnvelopeBound_of_twoStepFactor
    (routeUniformTwoStepFactorOfRawAmbientDominationAndRelativeCommutator
      hraw hcommutator)

end AntiresonantFrameLossCommutator
end CCM25Concrete
end Source
end ConnesWeilRH
