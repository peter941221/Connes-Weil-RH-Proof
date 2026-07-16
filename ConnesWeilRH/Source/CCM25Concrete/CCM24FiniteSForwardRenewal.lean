/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSTwoSidedRenewal

/-!
# Finite signed expansion of the normalized forward Euler adjoint

The forward factor has only two choices at each visible prime.  This module
keeps the alternating sign, proves the exact adjoint translation formula, and
flattens the complete finite product into one Boolean multi-index sum.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSForwardRenewal

open scoped InnerProduct

open CC20Concrete
open CCM24FiniteSProjectionTrace
open CCM24FiniteSGramResponse
open CCM24FiniteSCausalSupport
open CCM24FiniteSCausalMarkov
open CCM24FiniteSTwoSidedRenewal
open SelectedCrossingOperatorBridge

/-- The signed normalized coefficient of one forward Euler choice. -/
noncomputable def primeForwardSignedWeight
    (p : CCM24VisiblePrime) (choice : Bool) : ℝ :=
  (1 - ccm24PrimeEulerCoefficient p) *
    if choice then -ccm24PrimeEulerCoefficient p else 1

/-- The displacement contributed by one forward Euler choice. -/
noncomputable def primeForwardDisplacement
    (p : CCM24VisiblePrime) (choice : Bool) : ℝ :=
  (forwardEulerExponent choice : ℝ) * Real.log p

/-- One Boolean choice for every occurrence in the visible-prime list. -/
abbrev FiniteEulerForwardIndex : List CCM24VisiblePrime → Type
  | [] => PUnit
  | _ :: S => Bool × FiniteEulerForwardIndex S

noncomputable instance finiteEulerForwardIndexFintype :
    (S : List CCM24VisiblePrime) → Fintype (FiniteEulerForwardIndex S)
  | [] => inferInstance
  | _ :: S => by
      letI := finiteEulerForwardIndexFintype S
      exact inferInstance

noncomputable def finiteEulerForwardSignedWeight :
    (S : List CCM24VisiblePrime) → FiniteEulerForwardIndex S → ℝ
  | [], _ => 1
  | p :: S, index =>
      primeForwardSignedWeight p index.1 *
        finiteEulerForwardSignedWeight S index.2

noncomputable def finiteEulerForwardDisplacement :
    (S : List CCM24VisiblePrime) → FiniteEulerForwardIndex S → ℝ
  | [], _ => 0
  | p :: S, index =>
      primeForwardDisplacement p index.1 +
        finiteEulerForwardDisplacement S index.2

noncomputable def finiteEulerForwardOperatorTerm
    (S : List CCM24VisiblePrime) (index : FiniteEulerForwardIndex S) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  (finiteEulerForwardSignedWeight S index : ℂ) •
    (cc20GlobalLogTranslation
      (finiteEulerForwardDisplacement S index)).toContinuousLinearMap

/-- One normalized adjoint Euler factor. -/
noncomputable def normalizedPrimeEulerTransportAdjoint
    (p : CCM24VisiblePrime) : finiteSCarrier →L[ℂ] finiteSCarrier :=
  ((1 - ccm24PrimeEulerCoefficient p : ℝ) : ℂ) •
    (ccm24PrimeEulerTransportEquiv p).toContinuousLinearMap†

/-- The adjoint of `I-aU_(-log p)` is `I-aU_(log p)`. -/
theorem primeEulerTransportAdjoint_eq
    (p : CCM24VisiblePrime) :
    (ccm24PrimeEulerTransportEquiv p).toContinuousLinearMap† =
      ContinuousLinearMap.id ℂ finiteSCarrier -
        (ccm24PrimeEulerCoefficient p : ℂ) •
          (cc20GlobalLogTranslation
            (Real.log p)).toContinuousLinearMap := by
  have hfactor :
      (ccm24PrimeEulerTransportEquiv p).toContinuousLinearMap =
        ContinuousLinearMap.id ℂ finiteSCarrier -
          (ccm24PrimeEulerCoefficient p : ℂ) •
            (cc20GlobalLogTranslation
              (-Real.log p)).toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro u
    exact ccm24PrimeEulerTransportEquiv_apply p u
  rw [hfactor]
  simp only [map_sub, ContinuousLinearMap.adjoint_id, map_smulₛₗ,
    starRingEnd_apply]
  have hstar : star (ccm24PrimeEulerCoefficient p : ℂ) =
      (ccm24PrimeEulerCoefficient p : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal]
  rw [hstar, cc20GlobalLogTranslation_neg_adjoint]

/-- Exact two-choice expansion of one normalized forward adjoint factor. -/
theorem normalizedPrimeEulerTransportAdjoint_eq_sum
    (p : CCM24VisiblePrime) :
    normalizedPrimeEulerTransportAdjoint p =
      ∑ choice : Bool,
        (primeForwardSignedWeight p choice : ℂ) •
          (cc20GlobalLogTranslation
            (primeForwardDisplacement p choice)).toContinuousLinearMap := by
  have hzero :
      (cc20GlobalLogTranslation 0).toContinuousLinearMap =
        ContinuousLinearMap.id ℂ finiteSCarrier := by
    apply ContinuousLinearMap.ext
    intro u
    exact cc20GlobalLogTranslation_zero_apply u
  rw [normalizedPrimeEulerTransportAdjoint,
    primeEulerTransportAdjoint_eq, Fintype.univ_bool]
  simp [primeForwardSignedWeight, primeForwardDisplacement,
    forwardEulerExponent, hzero]
  module

/-- Recursive product of the normalized one-prime forward adjoints. -/
noncomputable def finiteEulerForwardAverage :
    List CCM24VisiblePrime → finiteSCarrier →L[ℂ] finiteSCarrier
  | [] => ContinuousLinearMap.id ℂ finiteSCarrier
  | p :: S => finiteEulerForwardAverage S ∘L
      normalizedPrimeEulerTransportAdjoint p

/-- The recursive forward average is the actual normalized complete transport
adjoint. -/
theorem finiteEulerForwardAverage_eq_normalizedTransportAdjoint
    (S : List CCM24VisiblePrime) :
    finiteEulerForwardAverage S =
      (finiteEulerLowerFactor S : ℂ) •
        (ccm24FiniteEulerTransportEquiv S).toContinuousLinearMap† := by
  induction S with
  | nil =>
      apply ContinuousLinearMap.ext
      intro u
      simp [finiteEulerForwardAverage, finiteEulerLowerFactor]
  | cons p S ih =>
      rw [finiteEulerForwardAverage, ih]
      have htransport :
          (ccm24FiniteEulerTransportEquiv (p :: S)).toContinuousLinearMap =
            (ccm24PrimeEulerTransportEquiv p).toContinuousLinearMap ∘L
              (ccm24FiniteEulerTransportEquiv S).toContinuousLinearMap := by
        apply ContinuousLinearMap.ext
        intro u
        exact ccm24FiniteEulerTransportEquiv_cons_apply p S u
      rw [htransport, ContinuousLinearMap.adjoint_comp]
      apply ContinuousLinearMap.ext
      intro u
      simp only [normalizedPrimeEulerTransportAdjoint,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
        map_smul, smul_smul, finiteEulerLowerFactor]
      congr 1
      norm_num

/-- Flattening theorem for the finite signed forward product. -/
theorem finiteEulerForwardAverage_eq_sum
    (S : List CCM24VisiblePrime) :
    finiteEulerForwardAverage S =
      ∑ index : FiniteEulerForwardIndex S,
        finiteEulerForwardOperatorTerm S index := by
  induction S with
  | nil =>
      apply ContinuousLinearMap.ext
      intro u
      simp [finiteEulerForwardAverage, finiteEulerForwardOperatorTerm,
        finiteEulerForwardSignedWeight, finiteEulerForwardDisplacement,
        cc20GlobalLogTranslation_zero_apply]
  | cons p S ih =>
      rw [finiteEulerForwardAverage, normalizedPrimeEulerTransportAdjoint_eq_sum,
        ih]
      apply ContinuousLinearMap.ext
      intro u
      simp only [ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.coe_sum', Finset.sum_apply, map_sum]
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro choice _
      apply Finset.sum_congr rfl
      intro index _
      simp only [finiteEulerForwardOperatorTerm,
        finiteEulerForwardSignedWeight, finiteEulerForwardDisplacement,
        ContinuousLinearMap.smul_apply, map_smul, smul_smul]
      change ((primeForwardSignedWeight p choice : ℂ) *
          (finiteEulerForwardSignedWeight S index : ℂ)) •
            cc20GlobalLogTranslation
              (finiteEulerForwardDisplacement S index)
              (cc20GlobalLogTranslation
                (primeForwardDisplacement p choice) u) = _
      rw [cc20GlobalLogTranslation_add_apply]
      rw [add_comm (finiteEulerForwardDisplacement S index)
        (primeForwardDisplacement p choice)]
      congr 1
      exact (Complex.ofReal_mul _ _).symm

/-- The actual normalized complete transport adjoint has the same finite
Boolean expansion. -/
theorem normalizedFiniteEulerTransportAdjoint_eq_sum
    (family : FinitePrimePowerFamily) :
    ((finiteEulerLowerFactor family.visiblePrimes : ℂ) •
        (finiteEulerTransportOperator family)†) =
      ∑ index : FiniteEulerForwardIndex family.visiblePrimes,
        finiteEulerForwardOperatorTerm family.visiblePrimes index := by
  rw [finiteEulerTransportOperator,
    ← finiteEulerForwardAverage_eq_normalizedTransportAdjoint,
    finiteEulerForwardAverage_eq_sum]

end CCM24FiniteSForwardRenewal
end CCM25Concrete
end Source
end ConnesWeilRH
