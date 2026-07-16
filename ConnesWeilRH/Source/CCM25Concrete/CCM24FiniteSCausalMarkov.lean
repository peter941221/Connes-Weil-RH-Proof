/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSNormalizedPhysicalResponse

/-!
# Exact causal Markov expansion of the normalized Euler inverse

For one visible prime, `(1-p⁻¹/²)(I-p⁻¹/² U)⁻¹` is written as the geometric
probability average of the genuine one-sided logarithmic translations.  The
complete finite product is then reconstructed recursively as a composition of
these one-prime averages.  This is the source-specific causal structure that
is absent from abstract metric-order countermodels.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCausalMarkov

open CC20Concrete
open CCM24FiniteSProjectionTrace
open CCM24FiniteSGramResponse
open CCM24FiniteSInverseMetric

/-- The geometric renewal weight at one visible prime. -/
noncomputable def primeEulerRenewalWeight
    (p : CCM24VisiblePrime) (n : ℕ) : ℝ :=
  (1 - ccm24PrimeEulerCoefficient p) *
    ccm24PrimeEulerCoefficient p ^ n

theorem primeEulerRenewalWeight_nonneg
    (p : CCM24VisiblePrime) (n : ℕ) :
    0 ≤ primeEulerRenewalWeight p n := by
  exact mul_nonneg
    (sub_nonneg.mpr (le_of_lt (ccm24PrimeEulerCoefficient_lt_one p)))
    (pow_nonneg (ccm24PrimeEulerCoefficient_nonneg p) n)

theorem summable_primeEulerRenewalWeight (p : CCM24VisiblePrime) :
    Summable (primeEulerRenewalWeight p) := by
  unfold primeEulerRenewalWeight
  exact (summable_geometric_of_norm_lt_one
    (show ‖ccm24PrimeEulerCoefficient p‖ < 1 by
      rw [Real.norm_eq_abs,
        abs_of_nonneg (ccm24PrimeEulerCoefficient_nonneg p)]
      exact ccm24PrimeEulerCoefficient_lt_one p)).mul_left _

/-- The one-prime renewal weights have total mass one. -/
theorem tsum_primeEulerRenewalWeight (p : CCM24VisiblePrime) :
    ∑' n : ℕ, primeEulerRenewalWeight p n = 1 := by
  simp only [primeEulerRenewalWeight]
  rw [tsum_mul_left,
    tsum_geometric_of_lt_one (ccm24PrimeEulerCoefficient_nonneg p)
      (ccm24PrimeEulerCoefficient_lt_one p)]
  field_simp [ne_of_gt (primeEulerLowerFactor_pos p)]

theorem cc20GlobalLogTranslation_zero_apply (u : finiteSCarrier) :
    cc20GlobalLogTranslation 0 u = u := by
  apply (cc20GlobalLogTranslation 0).injective
  simpa only [zero_add] using
    cc20GlobalLogTranslation_add_apply 0 0 u

/-- Every power in the Neumann series is the actual causal translation by
`-n log p`, with its exact Euler coefficient. -/
theorem primeEulerContraction_pow_apply
    (p : CCM24VisiblePrime) (n : ℕ) (u : finiteSCarrier) :
    (ccm24PrimeEulerContraction p ^ n) u =
      ((ccm24PrimeEulerCoefficient p : ℂ) ^ n) •
        cc20GlobalLogTranslation (-(n : ℝ) * Real.log p) u := by
  induction n with
  | zero =>
      simp only [pow_zero, ContinuousLinearMap.one_apply, one_smul,
        Nat.cast_zero, neg_zero, zero_mul]
      exact (cc20GlobalLogTranslation_zero_apply u).symm
  | succ n ih =>
      rw [pow_succ', ContinuousLinearMap.mul_apply, ih]
      simp only [ccm24PrimeEulerContraction,
        ContinuousLinearMap.smul_apply, map_smul, smul_smul]
      change (((ccm24PrimeEulerCoefficient p : ℂ) ^ n) *
          (ccm24PrimeEulerCoefficient p : ℂ)) •
            cc20GlobalLogTranslation (-Real.log p)
              (cc20GlobalLogTranslation (-(n : ℝ) * Real.log p) u) = _
      rw [cc20GlobalLogTranslation_add_apply]
      congr 1
      push_cast
      ring

/-- One normalized Euler inverse factor. -/
noncomputable def normalizedPrimeEulerInverse
    (p : CCM24VisiblePrime) : finiteSCarrier →L[ℂ] finiteSCarrier :=
  ((1 - ccm24PrimeEulerCoefficient p : ℝ) : ℂ) •
    (ccm24PrimeEulerTransportEquiv p).symm.toContinuousLinearMap

/-- Exact one-prime probability-average readback. -/
theorem normalizedPrimeEulerInverse_apply_eq_tsum
    (p : CCM24VisiblePrime) (u : finiteSCarrier) :
    normalizedPrimeEulerInverse p u =
      ∑' n : ℕ, (primeEulerRenewalWeight p n : ℂ) •
        cc20GlobalLogTranslation (-(n : ℝ) * Real.log p) u := by
  have hsummable : Summable
      (fun n : ℕ => ccm24PrimeEulerContraction p ^ n) :=
    summable_geometric_of_norm_lt_one
      (norm_ccm24PrimeEulerContraction_lt_one p)
  have heval :
      (∑' n : ℕ, ccm24PrimeEulerContraction p ^ n) u =
        ∑' n : ℕ, (ccm24PrimeEulerContraction p ^ n) u := by
    simpa using
      (ContinuousLinearMap.apply ℂ finiteSCarrier u).map_tsum hsummable
  rw [normalizedPrimeEulerInverse,
    ccm24PrimeEulerTransportEquiv_symm_toContinuousLinearMap,
    ccm24PrimeEulerInverseOperator, ContinuousLinearMap.smul_apply, heval,
    ← tsum_const_smul'']
  apply tsum_congr
  intro n
  rw [primeEulerContraction_pow_apply]
  simp only [primeEulerRenewalWeight, Complex.ofReal_mul,
    Complex.ofReal_pow, smul_smul]

/-- The paired outer-crossing scalar carried by one causal renewal atom.  The
forward and reflected channels are kept together. -/
noncomputable def primeEulerRenewalOuterPairAtom
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (p : CCM24VisiblePrime) (n : ℕ) : ℂ :=
  (primeEulerRenewalWeight p n : ℂ) *
    (((n : ℝ) * Real.log p : ℝ) : ℂ) *
      (owner.convolutionSquare.test ((n : ℝ) * Real.log p) +
        owner.convolutionSquare.test (-((n : ℝ) * Real.log p)))

/-- Compact root support deletes every one-prime renewal atom whose causal
displacement lies beyond the support radius.  The forward/reflected pair is
zeroed before any absolute value is taken. -/
theorem primeEulerRenewalOuterPairAtom_eq_zero_of_support_lt
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (p : CCM24VisiblePrime) (n : ℕ)
    (hfar : owner.supportRadius < (n : ℝ) * Real.log p) :
    primeEulerRenewalOuterPairAtom owner p n = 0 := by
  have hb : 0 ≤ (n : ℝ) * Real.log p :=
    mul_nonneg (Nat.cast_nonneg n)
      (Real.log_nonneg (by exact_mod_cast p.property.le))
  have hforward := owner.convolutionSquare_eq_zero_of_abs_gt
    ((n : ℝ) * Real.log p) (by simpa [abs_of_nonneg hb] using hfar)
  have hreflected := owner.convolutionSquare_eq_zero_of_abs_gt
    (-((n : ℝ) * Real.log p)) (by
      simpa [abs_neg, abs_of_nonneg hb] using hfar)
  simp [primeEulerRenewalOuterPairAtom, hforward, hreflected]

/-- The normalized inverse for an arbitrary visible-prime list. -/
noncomputable def normalizedFiniteEulerInverseList
    (S : List CCM24VisiblePrime) : finiteSCarrier →L[ℂ] finiteSCarrier :=
  (finiteEulerLowerFactor S : ℂ) •
    (ccm24FiniteEulerTransportEquiv S).symm.toContinuousLinearMap

theorem finiteEulerTransportEquiv_symm_cons_apply
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
    (u : finiteSCarrier) :
    (ccm24FiniteEulerTransportEquiv (p :: S)).symm u =
      (ccm24FiniteEulerTransportEquiv S).symm
        ((ccm24PrimeEulerTransportEquiv p).symm u) := by
  apply (ccm24FiniteEulerTransportEquiv (p :: S)).injective
  rw [(ccm24FiniteEulerTransportEquiv (p :: S)).apply_symm_apply,
    ccm24FiniteEulerTransportEquiv_cons_apply,
    (ccm24FiniteEulerTransportEquiv S).apply_symm_apply,
    (ccm24PrimeEulerTransportEquiv p).apply_symm_apply]

/-- Causal recursion for the normalized complete inverse. -/
theorem normalizedFiniteEulerInverseList_cons
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime) :
    normalizedFiniteEulerInverseList (p :: S) =
      normalizedFiniteEulerInverseList S ∘L normalizedPrimeEulerInverse p := by
  apply ContinuousLinearMap.ext
  intro u
  rw [normalizedFiniteEulerInverseList, normalizedFiniteEulerInverseList,
    normalizedPrimeEulerInverse, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply]
  change (finiteEulerLowerFactor (p :: S) : ℂ) •
      (ccm24FiniteEulerTransportEquiv (p :: S)).symm u =
    (finiteEulerLowerFactor S : ℂ) •
      (ccm24FiniteEulerTransportEquiv S).symm
        (((1 - ccm24PrimeEulerCoefficient p : ℝ) : ℂ) •
          (ccm24PrimeEulerTransportEquiv p).symm u)
  rw [finiteEulerTransportEquiv_symm_cons_apply]
  simp only [finiteEulerLowerFactor, map_smul, smul_smul]
  congr 1
  norm_num
  ring

/-- Recursive causal composition of the one-prime probability averages. -/
noncomputable def finiteEulerCausalAverage :
    List CCM24VisiblePrime → finiteSCarrier →L[ℂ] finiteSCarrier
  | [] => ContinuousLinearMap.id ℂ finiteSCarrier
  | p :: S => finiteEulerCausalAverage S ∘L normalizedPrimeEulerInverse p

theorem finiteEulerCausalAverage_eq_normalizedInverse
    (S : List CCM24VisiblePrime) :
    finiteEulerCausalAverage S = normalizedFiniteEulerInverseList S := by
  induction S with
  | nil =>
      apply ContinuousLinearMap.ext
      intro u
      simp [finiteEulerCausalAverage, normalizedFiniteEulerInverseList,
        finiteEulerLowerFactor]
  | cons p S ih =>
      rw [finiteEulerCausalAverage, ih,
        ← normalizedFiniteEulerInverseList_cons]

theorem normalizedFiniteEulerInverse_eq_causalAverage
    (family : FinitePrimePowerFamily) :
    normalizedFiniteEulerInverse family =
      finiteEulerCausalAverage family.visiblePrimes := by
  rw [finiteEulerCausalAverage_eq_normalizedInverse]
  rfl

end CCM24FiniteSCausalMarkov
end CCM25Concrete
end Source
end ConnesWeilRH
