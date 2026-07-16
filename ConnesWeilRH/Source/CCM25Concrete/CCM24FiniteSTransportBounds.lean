/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSInverseMetric

/-!
# Two-sided quantitative bounds for the finite Euler transport

The lower product `prod (1-a_p)` controls the inverse.  The companion upper
product `prod (1+a_p)` controls the forward transport.  Their product is at
most one because every Euler coefficient lies in `[0,1)`.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSTransportBounds

open scoped InnerProduct

open CC20Concrete
open CCM24FiniteSProjectionTrace
open CCM24FiniteSGramResponse
open CCM24FiniteSCausalSupport

/-- The scalar upper factor of the complete Euler product. -/
noncomputable def finiteEulerUpperFactor (S : List CCM24VisiblePrime) : ℝ :=
  (S.map fun p => 1 + ccm24PrimeEulerCoefficient p).prod

theorem primeEulerUpperFactor_pos (p : CCM24VisiblePrime) :
    0 < 1 + ccm24PrimeEulerCoefficient p := by
  exact add_pos_of_pos_of_nonneg zero_lt_one
    (ccm24PrimeEulerCoefficient_nonneg p)

theorem finiteEulerUpperFactor_pos (S : List CCM24VisiblePrime) :
    0 < finiteEulerUpperFactor S := by
  induction S with
  | nil => simp [finiteEulerUpperFactor]
  | cons p S ih =>
      simpa [finiteEulerUpperFactor] using
        mul_pos (primeEulerUpperFactor_pos p) ih

/-- One Euler factor is bounded above by `1+p⁻¹/²`. -/
theorem primeEulerTransport_upper_bound
    (p : CCM24VisiblePrime) (u : finiteSCarrier) :
    ‖ccm24PrimeEulerTransportEquiv p u‖ ≤
      (1 + ccm24PrimeEulerCoefficient p) * ‖u‖ := by
  rw [ccm24PrimeEulerTransportEquiv_apply]
  calc
    ‖u - (ccm24PrimeEulerCoefficient p : ℂ) •
        cc20GlobalLogTranslation (-Real.log p) u‖ ≤
      ‖u‖ + ‖(ccm24PrimeEulerCoefficient p : ℂ) •
        cc20GlobalLogTranslation (-Real.log p) u‖ := norm_sub_le _ _
    _ = ‖u‖ + ccm24PrimeEulerCoefficient p * ‖u‖ := by
      rw [norm_smul, norm_cc20GlobalLogTranslation,
        Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (ccm24PrimeEulerCoefficient_nonneg p)]
    _ = (1 + ccm24PrimeEulerCoefficient p) * ‖u‖ := by ring

/-- The complete Euler product has the product upper bound. -/
theorem finiteEulerTransport_upper_bound
    (S : List CCM24VisiblePrime) (u : finiteSCarrier) :
    ‖ccm24FiniteEulerTransportEquiv S u‖ ≤
      finiteEulerUpperFactor S * ‖u‖ := by
  induction S generalizing u with
  | nil => simp [finiteEulerUpperFactor, ccm24FiniteEulerTransportEquiv_nil]
  | cons p S ih =>
      rw [ccm24FiniteEulerTransportEquiv_cons_apply]
      change ‖ccm24PrimeEulerTransportEquiv p
          (ccm24FiniteEulerTransportEquiv S u)‖ ≤
        (1 + ccm24PrimeEulerCoefficient p) *
          finiteEulerUpperFactor S * ‖u‖
      calc
        ‖ccm24PrimeEulerTransportEquiv p
            (ccm24FiniteEulerTransportEquiv S u)‖ ≤
          (1 + ccm24PrimeEulerCoefficient p) *
            ‖ccm24FiniteEulerTransportEquiv S u‖ :=
          primeEulerTransport_upper_bound p _
        _ ≤ (1 + ccm24PrimeEulerCoefficient p) *
            (finiteEulerUpperFactor S * ‖u‖) := by
          exact mul_le_mul_of_nonneg_left (ih u)
            (le_of_lt (primeEulerUpperFactor_pos p))
        _ = _ := by ring

theorem norm_finiteEulerTransportOperator_le_upperFactor
    (S : List CCM24VisiblePrime) :
    ‖(ccm24FiniteEulerTransportEquiv S).toContinuousLinearMap‖ ≤
      finiteEulerUpperFactor S := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (le_of_lt (finiteEulerUpperFactor_pos S))
  intro u
  simpa only [mul_comm] using finiteEulerTransport_upper_bound S u

theorem primeLower_mul_upper_le_one (p : CCM24VisiblePrime) :
    (1 - ccm24PrimeEulerCoefficient p) *
        (1 + ccm24PrimeEulerCoefficient p) ≤ 1 := by
  have hnonneg := ccm24PrimeEulerCoefficient_nonneg p
  nlinarith [sq_nonneg (ccm24PrimeEulerCoefficient p)]

/-- The forward and inverse normalizations cancel their apparent condition
numbers before a norm is taken. -/
theorem finiteEulerLower_mul_upper_le_one (S : List CCM24VisiblePrime) :
    finiteEulerLowerFactor S * finiteEulerUpperFactor S ≤ 1 := by
  induction S with
  | nil => simp [finiteEulerLowerFactor, finiteEulerUpperFactor]
  | cons p S ih =>
      change ((1 - ccm24PrimeEulerCoefficient p) *
          finiteEulerLowerFactor S) *
        ((1 + ccm24PrimeEulerCoefficient p) *
          finiteEulerUpperFactor S) ≤ 1
      rw [show ((1 - ccm24PrimeEulerCoefficient p) *
            finiteEulerLowerFactor S) *
          ((1 + ccm24PrimeEulerCoefficient p) *
            finiteEulerUpperFactor S) =
          ((1 - ccm24PrimeEulerCoefficient p) *
            (1 + ccm24PrimeEulerCoefficient p)) *
          (finiteEulerLowerFactor S * finiteEulerUpperFactor S) by ring]
      calc
        _ ≤ 1 * (finiteEulerLowerFactor S * finiteEulerUpperFactor S) := by
          apply mul_le_mul_of_nonneg_right (primeLower_mul_upper_le_one p)
          exact mul_nonneg
            (le_of_lt (finiteEulerLowerFactor_pos S))
            (le_of_lt (finiteEulerUpperFactor_pos S))
        _ ≤ 1 * 1 := by simpa using ih
        _ = 1 := one_mul 1

/-- The lower-factor-normalized adjoint transport is also a contraction. -/
theorem norm_lowerFactor_smul_finiteEulerTransportAdjoint_le_one
    (S : List CCM24VisiblePrime) :
    ‖(finiteEulerLowerFactor S : ℂ) •
        ((ccm24FiniteEulerTransportEquiv S).toContinuousLinearMap)†‖ ≤ 1 := by
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (finiteEulerLowerFactor_pos S),
    ContinuousLinearMap.adjoint.norm_map]
  calc
    finiteEulerLowerFactor S *
        ‖(ccm24FiniteEulerTransportEquiv S).toContinuousLinearMap‖ ≤
      finiteEulerLowerFactor S * finiteEulerUpperFactor S := by
        exact mul_le_mul_of_nonneg_left
          (norm_finiteEulerTransportOperator_le_upperFactor S)
          (le_of_lt (finiteEulerLowerFactor_pos S))
    _ ≤ 1 := finiteEulerLower_mul_upper_le_one S

end CCM24FiniteSTransportBounds
end CCM25Concrete
end Source
end ConnesWeilRH
