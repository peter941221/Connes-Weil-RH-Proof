/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSActualSchurRightCoDefect
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorSingleChannelColumnEquivalence

/-!
# The raw antiresonant column is the actual right Schur defect

The normalized one-prime ambient transport is normal because its two
orientations are polynomials in commuting opposite translations.  Therefore
the Gram operator of the raw antiresonant column is

```text
(L_p^dagger newFrame_S)^dagger (L_p^dagger newFrame_S)
  = I - Transition_(p,S)^dagger Transition_(p,S).
```

The right-boundary leakage from the generic rectangular identity is exactly
zero here because the actual Schur owner stores
`transport * newFrame = oldFrame * transition`.  Combining this result with
Proof 634 rewrites Bone 1 as a uniform estimate against the genuine right
transition co-defect.  It does not estimate the signed numerator.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorSingleChannelRightCoDefect

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSActualSchurRightCoDefect
open CCM24FiniteSCompletedJuliaAmbientDefectFactorization
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorGap
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorRouteValidFactorization
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorSingleChannelColumnEquivalence
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorSingleChannelFactorization
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantRadialSplit
open CCM24FiniteSForwardRenewal
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSJuliaCoDefect
open CCM24FiniteSProjectionTrace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! ## Normality of the concrete ambient transport -/

/-- The normalized ambient Euler transport commutes with its adjoint. -/
theorem normalizedPrimeEulerFrameTransport_adjoint_comp_self_eq_comp_adjoint
    (p : CCM24VisiblePrime) :
    (normalizedPrimeEulerFrameTransport p)† ∘L
        normalizedPrimeEulerFrameTransport p =
      normalizedPrimeEulerFrameTransport p ∘L
        (normalizedPrimeEulerFrameTransport p)† := by
  have hfactor :
      (ccm24PrimeEulerTransportEquiv p).toContinuousLinearMap =
        ContinuousLinearMap.id ℂ finiteSCarrier -
          (ccm24PrimeEulerCoefficient p : ℂ) •
            (cc20GlobalLogTranslation
              (-Real.log p)).toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro x
    exact ccm24PrimeEulerTransportEquiv_apply p x
  apply ContinuousLinearMap.ext
  intro x
  rw [normalizedPrimeEulerFrameTransport_adjoint_eq,
    normalizedPrimeEulerFrameTransport, hfactor]
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply, map_smul, map_sub]
  have hcommMaps :
      (cc20GlobalLogTranslation
          (Real.log p)).toContinuousLinearMap ∘L
          (cc20GlobalLogTranslation
            (-Real.log p)).toContinuousLinearMap =
        (cc20GlobalLogTranslation
          (-Real.log p)).toContinuousLinearMap ∘L
          (cc20GlobalLogTranslation
            (Real.log p)).toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro y
    exact cc20GlobalLogTranslation_commute
      (Real.log p) (-Real.log p) y
  have hcomm := DFunLike.congr_fun hcommMaps x
  simp only [ContinuousLinearMap.comp_apply] at hcomm
  rw [hcomm]
  module

/-- The known ambient co-defect factorization also has the right-defect
orientation because the concrete transport is normal. -/
theorem primeEulerAmbientLossFactor_comp_adjoint_eq_rightAmbientDefect
    (p : CCM24VisiblePrime) :
    primeEulerAmbientLossFactor p ∘L
        (primeEulerAmbientLossFactor p)† =
      ContinuousLinearMap.id ℂ finiteSCarrier -
        (normalizedPrimeEulerFrameTransport p)† ∘L
          normalizedPrimeEulerFrameTransport p := by
  rw [← normalizedPrimeEulerFrameTransport_ambientCoDefect_eq_factor]
  unfold rectangularAmbientCoDefect
  rw [←
    normalizedPrimeEulerFrameTransport_adjoint_comp_self_eq_comp_adjoint]

/-! ## Actual source-step Gram identity -/

/-- The raw antiresonant column has exactly the Gram operator of the actual
transition right co-defect. -/
theorem newFrameAntiresonantColumn_adjoint_comp_self_eq_rightCoDefect
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    (newFrameAntiresonantColumn lambda p S)† ∘L
        newFrameAntiresonantColumn lambda p S =
      rectangularTransitionRightCoDefect
        (suffixEulerFrameTransition lambda p S) := by
  let data := suffixEulerFrameSchurStep lambda p S
  have hright := rectangularTransitionRightCoDefect_eq_ambient_add_boundary
    data
  have hboundary :=
    rectangularRightBoundaryCompression_eq_zero_of_intertwining data
  rw [hboundary] at hright
  simp only [ContinuousLinearMap.comp_zero, add_zero] at hright
  have hnew : data.newFrame = newSuffixFrame lambda S := rfl
  have htransport : data.transport =
      normalizedPrimeEulerFrameTransport p := rfl
  have htransition : data.transition =
      suffixEulerFrameTransition lambda p S := rfl
  rw [hnew, htransport, htransition] at hright
  calc
    (newFrameAntiresonantColumn lambda p S)† ∘L
          newFrameAntiresonantColumn lambda p S =
        (newSuffixFrame lambda S)† ∘L
          (primeEulerAmbientLossFactor p ∘L
            (primeEulerAmbientLossFactor p)†) ∘L
              newSuffixFrame lambda S := by
      simp only [newFrameAntiresonantColumn,
        ContinuousLinearMap.adjoint_comp,
        ContinuousLinearMap.adjoint_adjoint,
        ContinuousLinearMap.comp_assoc]
    _ = (newSuffixFrame lambda S)† ∘L
          (ContinuousLinearMap.id ℂ finiteSCarrier -
            (normalizedPrimeEulerFrameTransport p)† ∘L
              normalizedPrimeEulerFrameTransport p) ∘L
            newSuffixFrame lambda S := by
      rw [primeEulerAmbientLossFactor_comp_adjoint_eq_rightAmbientDefect]
    _ = rectangularTransitionRightCoDefect
          (suffixEulerFrameTransition lambda p S) := hright.symm

/-- Pointwise Julia readout of the same right defect. -/
theorem norm_sq_newFrameAntiresonantColumn_eq_rightCoDefect_inner
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (x : sourceSoninCarrier lambda) :
    ‖newFrameAntiresonantColumn lambda p S x‖ ^ 2 =
      RCLike.re
        ⟪(rectangularTransitionRightCoDefect
          (suffixEulerFrameTransition lambda p S)) x, x⟫_ℂ := by
  calc
    ‖newFrameAntiresonantColumn lambda p S x‖ ^ 2 =
        RCLike.re ⟪((newFrameAntiresonantColumn lambda p S)† ∘L
          newFrameAntiresonantColumn lambda p S) x, x⟫_ℂ := by
      rw [ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_left]
    _ = RCLike.re
        ⟪(rectangularTransitionRightCoDefect
          (suffixEulerFrameTransition lambda p S)) x, x⟫_ℂ := by
      rw [newFrameAntiresonantColumn_adjoint_comp_self_eq_rightCoDefect]

/-! ## Exact Bone 1 restatement -/

/-- Bone 1 written against the positive quadratic form of the actual right
transition co-defect. -/
def SuffixRawOldCarrierAntiresonantInteriorRouteUniformRightCoDefectDomination
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (bound : ℝ) : Prop :=
  0 ≤ bound ∧
    ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixRouteValidStep p S →
        ∀ x : sourceSoninCarrier lambda,
          ‖signedCompressedInteriorOwner owner lambda p S x‖ ^ 2 ≤
            bound ^ 2 * RCLike.re
              ⟪(rectangularTransitionRightCoDefect
                (suffixEulerFrameTransition lambda p S)) x, x⟫_ℂ

/-- The raw-column and right-co-defect formulations are definitionally the
same estimate after the Gram identity is inserted. -/
theorem routeUniformRawAmbientDomination_iff_rightCoDefectDomination
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (bound : ℝ) :
    SuffixRawOldCarrierAntiresonantInteriorRouteUniformRawAmbientDomination
        owner lambda bound ↔
      SuffixRawOldCarrierAntiresonantInteriorRouteUniformRightCoDefectDomination
        owner lambda bound := by
  constructor
  · rintro ⟨hbound, hdom⟩
    refine ⟨hbound, ?_⟩
    intro p S hvalid x
    simpa only [
      norm_sq_newFrameAntiresonantColumn_eq_rightCoDefect_inner] using
      hdom p S hvalid x
  · rintro ⟨hbound, hdom⟩
    refine ⟨hbound, ?_⟩
    intro p S hvalid x
    simpa only [
      norm_sq_newFrameAntiresonantColumn_eq_rightCoDefect_inner] using
      hdom p S hvalid x

/-- Existence of the route-uniform Bone 1 constant is exactly existence of a
uniform right-co-defect bound. -/
theorem exists_routeUniformRenewedAmbientDomination_iff_exists_rightCoDefect
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    (∃ bound : ℝ,
      SuffixRawOldCarrierAntiresonantInteriorRouteUniformRenewedAmbientDomination
        owner lambda bound) ↔
      ∃ bound : ℝ,
        SuffixRawOldCarrierAntiresonantInteriorRouteUniformRightCoDefectDomination
          owner lambda bound := by
  rw [exists_routeUniformRenewedAmbientDomination_iff_exists_raw]
  constructor
  · rintro ⟨bound, hbound⟩
    exact ⟨bound,
      (routeUniformRawAmbientDomination_iff_rightCoDefectDomination
        owner lambda bound).1 hbound⟩
  · rintro ⟨bound, hbound⟩
    exact ⟨bound,
      (routeUniformRawAmbientDomination_iff_rightCoDefectDomination
        owner lambda bound).2 hbound⟩

end CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorSingleChannelRightCoDefect
end CCM25Concrete
end Source
end ConnesWeilRH
