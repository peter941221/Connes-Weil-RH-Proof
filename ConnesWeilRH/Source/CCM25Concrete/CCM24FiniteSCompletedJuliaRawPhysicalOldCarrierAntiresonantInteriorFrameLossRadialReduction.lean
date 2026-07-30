/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFrameLossCommutatorReduction
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantRadialBlockRecurrence

/-!
# Radial reduction of the frame-loss relative commutator

Proof 671 reduces ambient frame-loss stability to

```text
||[U_(log p), P_S]u|| <= L ||(I + U_(log p))u||,
```

where `P_S` is the actual semilocal Sonin orthogonal projection.  This module
uses the genuine upper radial-support projection `E`.  Since `P_S <= E` and
positive translation preserves the lower radial complement, the commutator
depends only on `E u`, while the radial component of the denominator is
exactly `E (I + U) E u`.

Consequently the source-specific compressed estimate

```text
||[U_(log p), P_S] E u|| <= L ||E (I + U_(log p)) E u||
```

implies the full relative commutator estimate with the same constant.  The
remaining reverse direction is the exterior-cancellation problem: the lower
radial component of `(I + U)u` can cancel the boundary emitted by `E u`.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace AntiresonantFrameLossRadialReduction

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorAdjacentProjectionGap
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantRadialBlockRecurrence
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantRadialSplit
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorRouteValidFactorization
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorSingleChannelColumnEquivalence
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorTwoStepCoboundaryFactorization
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorPairedCorrelationCoboundary
open CCM24FiniteSProjectionTrace
open CCM24UnitScaleProlateAlignment
open AntiresonantFrameLossCommutator
open TwoStepFactorCollapse

/-! ## The Sonin projection is contained in the radial half-line -/

/-- The actual suffix Sonin projection lands in the common upper radial
support. -/
theorem radialSupportProjection_comp_newSuffixRangeProjection
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    radialSupportProjection lambda ∘L
        newSuffixRangeProjection lambda S =
      newSuffixRangeProjection lambda S := by
  rw [newSuffixRangeProjection, ← ContinuousLinearMap.comp_assoc,
    radialSupportProjection_comp_newSuffixFrame]

/-- The same range containment in the reverse compression order. -/
theorem newSuffixRangeProjection_comp_radialSupportProjection
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    newSuffixRangeProjection lambda S ∘L
        radialSupportProjection lambda =
      newSuffixRangeProjection lambda S := by
  have h := congrArg ContinuousLinearMap.adjoint
    (radialSupportProjection_comp_newSuffixRangeProjection lambda S)
  have hradial :
      (radialSupportProjection lambda)† =
        radialSupportProjection lambda :=
    (radialSupportProjection_isStarProjection lambda).isSelfAdjoint.adjoint_eq
  have hsuffix :
      (newSuffixRangeProjection lambda S)† =
        newSuffixRangeProjection lambda S := by
    rw [newSuffixRangeProjection_eq_semilocalSoninStarProjection]
    exact isSelfAdjoint_starProjection _
  simpa only [ContinuousLinearMap.adjoint_comp, hradial, hsuffix] using h

/-- The radial complement annihilates the actual suffix Sonin projection. -/
theorem radialComplement_comp_newSuffixRangeProjection_eq_zero
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    radialComplement lambda ∘L
        newSuffixRangeProjection lambda S = 0 := by
  apply ContinuousLinearMap.ext
  intro u
  have h := DFunLike.congr_fun
    (radialSupportProjection_comp_newSuffixRangeProjection lambda S) u
  simp only [radialComplement, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.zero_apply] at h ⊢
  rw [h]
  exact sub_self _

/-- The actual suffix Sonin projection annihilates the radial complement. -/
theorem newSuffixRangeProjection_comp_radialComplement_eq_zero
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    newSuffixRangeProjection lambda S ∘L
        radialComplement lambda = 0 := by
  apply ContinuousLinearMap.ext
  intro u
  have h := DFunLike.congr_fun
    (newSuffixRangeProjection_comp_radialSupportProjection lambda S) u
  simp only [radialComplement, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, map_sub,
    ContinuousLinearMap.zero_apply] at h ⊢
  rw [h]
  exact sub_self _

/-! ## One-sided triangularity of positive translation -/

/-- Negative translation preserves the upper radial half-line. -/
theorem radialComplement_comp_negativeTranslation_comp_radialSupport_eq_zero
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) :
    radialComplement lambda ∘L
        (cc20GlobalLogTranslation
          (-Real.log p)).toContinuousLinearMap ∘L
        radialSupportProjection lambda = 0 := by
  apply ContinuousLinearMap.ext
  intro u
  have hsource :
      radialSupportProjection lambda u ∈
        ccm24LogRadialSupportClosedSubspace lambda :=
    Submodule.starProjection_apply_mem _ _
  have hpLog : 0 ≤ Real.log (p : Real) :=
    Real.log_nonneg (by exact_mod_cast p.property.le)
  have htranslated :=
    cc20GlobalLogTranslation_mem_ccm24LogRadialSupport lambda
      (-Real.log p) (neg_nonpos.mpr hpLog) hsource
  have hfixed :=
    (ccm24LogRadialSupportProjection_eq_self_iff lambda _).2 htranslated
  have hfixed' :
      radialSupportProjection lambda
          ((cc20GlobalLogTranslation (-Real.log p)).toContinuousLinearMap
            (radialSupportProjection lambda u)) =
        (cc20GlobalLogTranslation (-Real.log p)).toContinuousLinearMap
          (radialSupportProjection lambda u) := by
    simpa only [radialSupportProjection,
      ccm24LogRadialSupportProjection] using hfixed
  simp only [radialComplement, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.zero_apply]
  rw [hfixed']
  exact sub_self _

/-- After adjointing, positive translation cannot carry a lower radial vector
back into the upper half-line. -/
theorem radialSupport_comp_positiveTranslation_comp_radialComplement_eq_zero
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) :
    radialSupportProjection lambda ∘L
        (cc20GlobalLogTranslation
          (Real.log p)).toContinuousLinearMap ∘L
        radialComplement lambda = 0 := by
  have h := congrArg ContinuousLinearMap.adjoint
    (radialComplement_comp_negativeTranslation_comp_radialSupport_eq_zero
      lambda p)
  have hradial :
      (radialSupportProjection lambda)† =
        radialSupportProjection lambda :=
    (radialSupportProjection_isStarProjection lambda).isSelfAdjoint.adjoint_eq
  have hcomplement :
      (radialComplement lambda)† = radialComplement lambda :=
    (radialSupportProjection_isStarProjection lambda).one_sub
      |>.isSelfAdjoint.adjoint_eq
  have htranslation :
      ((cc20GlobalLogTranslation
        (-Real.log p)).toContinuousLinearMap)† =
        (cc20GlobalLogTranslation
          (Real.log p)).toContinuousLinearMap :=
    SelectedCrossingOperatorBridge.cc20GlobalLogTranslation_neg_adjoint _
  simpa only [ContinuousLinearMap.adjoint_comp, hradial, hcomplement,
    htranslation, map_zero] using h

/-- The Sonin projection therefore kills every positive-translation input
coming from the lower radial complement. -/
theorem newSuffixRangeProjection_comp_positiveTranslation_comp_radialComplement_eq_zero
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    newSuffixRangeProjection lambda S ∘L
        (cc20GlobalLogTranslation
          (Real.log p)).toContinuousLinearMap ∘L
        radialComplement lambda = 0 := by
  calc
    newSuffixRangeProjection lambda S ∘L
          (cc20GlobalLogTranslation
            (Real.log p)).toContinuousLinearMap ∘L
          radialComplement lambda =
        (newSuffixRangeProjection lambda S ∘L
            radialSupportProjection lambda) ∘L
          (cc20GlobalLogTranslation
            (Real.log p)).toContinuousLinearMap ∘L
          radialComplement lambda := by
            rw [newSuffixRangeProjection_comp_radialSupportProjection]
    _ = newSuffixRangeProjection lambda S ∘L
          (radialSupportProjection lambda ∘L
            (cc20GlobalLogTranslation
              (Real.log p)).toContinuousLinearMap ∘L
            radialComplement lambda) := by
          simp only [ContinuousLinearMap.comp_assoc]
    _ = 0 := by
      rw [radialSupport_comp_positiveTranslation_comp_radialComplement_eq_zero]
      simp

/-! ## Exact radial absorption -/

/-- The translation/Sonin commutator depends only on the upper radial part of
its input. -/
theorem suffixPrimeTranslationProjectionCommutator_comp_radialSupport_eq_self
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime) :
    suffixPrimeTranslationProjectionCommutator p S ∘L
        radialSupportProjection unitSoninScale =
      suffixPrimeTranslationProjectionCommutator p S := by
  apply ContinuousLinearMap.ext
  intro u
  have hPE := DFunLike.congr_fun
    (newSuffixRangeProjection_comp_radialSupportProjection
      unitSoninScale S) u
  have hPUF := DFunLike.congr_fun
    (newSuffixRangeProjection_comp_positiveTranslation_comp_radialComplement_eq_zero
      unitSoninScale p S) u
  simp only [suffixPrimeTranslationProjectionCommutator,
    primePositiveLogTranslationOperator, cc20Commutator,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.zero_apply, radialComplement,
    ContinuousLinearMap.id_apply, map_sub] at hPE hPUF ⊢
  have hPU :
      newSuffixRangeProjection unitSoninScale S
          ((cc20GlobalLogTranslation (Real.log p)).toContinuousLinearMap u) =
        newSuffixRangeProjection unitSoninScale S
          ((cc20GlobalLogTranslation (Real.log p)).toContinuousLinearMap
            (radialSupportProjection unitSoninScale u)) := by
    exact sub_eq_zero.mp hPUF
  rw [hPE, hPU]

/-- The upper radial component of the antiresonant denominator also depends
only on the upper radial input. -/
theorem radialSupport_comp_antiresonantCore_comp_radialSupport_eq_left
    (p : CCM24VisiblePrime) :
    radialSupportProjection unitSoninScale ∘L
        primeEulerAntiresonantCore p ∘L
        radialSupportProjection unitSoninScale =
      radialSupportProjection unitSoninScale ∘L
        primeEulerAntiresonantCore p := by
  apply ContinuousLinearMap.ext
  intro u
  have hEUF := DFunLike.congr_fun
    (radialSupport_comp_positiveTranslation_comp_radialComplement_eq_zero
      unitSoninScale p) u
  have hEfixed :
      radialSupportProjection unitSoninScale
          (radialSupportProjection unitSoninScale u) =
        radialSupportProjection unitSoninScale u :=
    (ccm24LogRadialSupportProjection_eq_self_iff unitSoninScale _).2
      (Submodule.starProjection_apply_mem _ _)
  simp only [primeEulerAntiresonantCore,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.id_apply, map_add, radialComplement,
    ContinuousLinearMap.sub_apply, map_sub,
    ContinuousLinearMap.zero_apply] at hEUF ⊢
  rw [hEfixed]
  have htranslation :
      radialSupportProjection unitSoninScale
          ((cc20GlobalLogTranslation (Real.log p)).toContinuousLinearMap u) =
        radialSupportProjection unitSoninScale
          ((cc20GlobalLogTranslation (Real.log p)).toContinuousLinearMap
            (radialSupportProjection unitSoninScale u)) := by
    exact sub_eq_zero.mp hEUF
  rw [htranslation]

/-! ## Route-uniform radial graph estimate -/

/-- The route-uniform estimate after both the input and denominator are
compressed to the actual upper radial half-line. -/
def SuffixCompleteCoupledRouteUniformRadialPrimeTranslationProjectionCommutatorDomination
    (bound : Real) : Prop :=
  0 ≤ bound ∧
    ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixRouteValidStep p S → ∀ u : finiteSCarrier,
        ‖suffixPrimeTranslationProjectionCommutator p S
            (radialSupportProjection unitSoninScale u)‖ ≤
          bound *
            ‖radialSupportProjection unitSoninScale
              (primeEulerAntiresonantCore p
                (radialSupportProjection unitSoninScale u))‖

/-- The radial compressed estimate implies Proof 671's full relative
commutator estimate with no loss in the constant. -/
theorem relativeCommutatorDomination_of_radialDomination
    {bound : Real}
    (hradial :
      SuffixCompleteCoupledRouteUniformRadialPrimeTranslationProjectionCommutatorDomination
        bound) :
    SuffixCompleteCoupledRouteUniformPrimeTranslationProjectionCommutatorDomination
      bound := by
  refine ⟨hradial.1, ?_⟩
  intro p S hvalid u
  have hcommutator := DFunLike.congr_fun
    (suffixPrimeTranslationProjectionCommutator_comp_radialSupport_eq_self
      p S) u
  have hdenominator := DFunLike.congr_fun
    (radialSupport_comp_antiresonantCore_comp_radialSupport_eq_left p) u
  simp only [ContinuousLinearMap.comp_apply] at hcommutator hdenominator
  rw [← hcommutator]
  calc
    ‖suffixPrimeTranslationProjectionCommutator p S
        (radialSupportProjection unitSoninScale u)‖ ≤
        bound *
          ‖radialSupportProjection unitSoninScale
            (primeEulerAntiresonantCore p
              (radialSupportProjection unitSoninScale u))‖ :=
      hradial.2 p S hvalid u
    _ = bound *
          ‖radialSupportProjection unitSoninScale
            (primeEulerAntiresonantCore p u)‖ := by rw [hdenominator]
    _ ≤ bound * ‖primeEulerAntiresonantCore p u‖ := by
      exact mul_le_mul_of_nonneg_left
        (Submodule.norm_starProjection_apply_le _ _) hradial.1

/-! ## Direct handoff to Proof 671's consumers -/

/-- Restricted raw Bone 1 plus the radial graph estimate constructs the full
ambient quotient with bound `B * (L + 1)`. -/
noncomputable def routeUniformAmbientLossFactorOfRawAmbientDominationAndRadialCommutator
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {rawBound radialBound : Real}
    (hraw :
      SuffixRawOldCarrierAntiresonantInteriorRouteUniformRawAmbientDomination
        owner unitSoninScale rawBound)
    (hradial :
      SuffixCompleteCoupledRouteUniformRadialPrimeTranslationProjectionCommutatorDomination
        radialBound) :
    SuffixCompleteCoupledRouteUniformAmbientLossFactor owner
      (rawBound * (radialBound + 1)) :=
  routeUniformAmbientLossFactorOfRawAmbientDominationAndRelativeCommutator
    hraw (relativeCommutatorDomination_of_radialDomination hradial)

/-- The same radial estimate reaches Proof 669's two-step factor. -/
theorem routeUniformTwoStepFactorOfRawAmbientDominationAndRadialCommutator
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {rawBound radialBound : Real}
    (hraw :
      SuffixRawOldCarrierAntiresonantInteriorRouteUniformRawAmbientDomination
        owner unitSoninScale rawBound)
    (hradial :
      SuffixCompleteCoupledRouteUniformRadialPrimeTranslationProjectionCommutatorDomination
        radialBound) :
    SuffixCompleteCoupledRouteUniformScaledTwoStepCoboundaryFactor owner
      (rawBound * (radialBound + 1)) :=
  routeUniformTwoStepFactorOfRawAmbientDominationAndRelativeCommutator
    hraw (relativeCommutatorDomination_of_radialDomination hradial)

/-- The radial estimate reaches the paired finite-horizon envelope. -/
theorem pairedAdjointCoboundaryEnvelopeBoundOfRawAmbientDominationAndRadialCommutator
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {rawBound radialBound : Real}
    (hraw :
      SuffixRawOldCarrierAntiresonantInteriorRouteUniformRawAmbientDomination
        owner unitSoninScale rawBound)
    (hradial :
      SuffixCompleteCoupledRouteUniformRadialPrimeTranslationProjectionCommutatorDomination
        radialBound) :
    SuffixCompleteCoupledRoutePairedAdjointCoboundaryEnvelopeBound owner :=
  pairedAdjointCoboundaryEnvelopeBoundOfRawAmbientDominationAndRelativeCommutator
    hraw (relativeCommutatorDomination_of_radialDomination hradial)

end AntiresonantFrameLossRadialReduction
end CCM25Concrete
end Source
end ConnesWeilRH
