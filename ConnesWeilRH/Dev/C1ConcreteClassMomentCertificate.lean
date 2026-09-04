/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1ScaledExpRationalEnvelope
import ConnesWeilRH.Dev.C1RationalPowerIntegral
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Record 1139: concrete class-moment certificate

This leaf assembles the scaled Taylor envelope and the rational-power
integral engine into the concrete order-0 and order-2 class-moment producer.
The coefficient and endpoint arithmetic is generated over `ℚ` and checked by
`native_decide`; the real theorem only sees casts of those exact rational
identities.  Endpoint tails are handled later in this file at radius `97/100`.

RH is NOT claimed.
-/

namespace ConnesWeilRH
namespace Source
namespace C1ConcreteClassMomentCertificate

open MeasureTheory Set
open C1ClassWindowObjects
open C1ClassGramMomentReduction
open C1ClassMomentIntegralCertificate
open C1ClassMomentTailCertificate
open C1RationalPowerIntegral
open C1Q28ClassGramIntervalTransfer
open Polynomial
open scoped BigOperators Interval

/-! ## Exact rational data used for the finite certificate -/

section Computable

def rationalRadiusQ : ℚ := 97 / 100

def taylorScaledPolynomialQ : ℚ[X] :=
  ∑ j ∈ Finset.range 20,
    Polynomial.C (((-(2 / 35 : ℚ)) ^ j) / (j.factorial : ℚ)) *
      Polynomial.X ^ j

def rationalPowerPolynomialQ : ℚ[X] := taylorScaledPolynomialQ ^ 35

def rationalPowerCoefficientQ (k : ℕ) : ℚ :=
  rationalPowerPolynomialQ.coeff k

def endpointAQ : ℕ → ℚ
  | 0 => 2 * rationalRadiusQ
  | 1 => 0
  | k + 2 =>
      rationalRadiusQ /
          (((k : ℚ) + 1) * (1 - rationalRadiusQ ^ 2) ^ (k + 1)) +
        ((2 * (k : ℚ) + 1) / (2 * ((k : ℚ) + 1))) * endpointAQ (k + 1)

def endpointBQ : ℕ → ℚ
  | 0 => 0
  | 1 => 1
  | k + 2 =>
      ((2 * (k : ℚ) + 1) / (2 * ((k : ℚ) + 1))) * endpointBQ (k + 1)

def momentAQ : ℕ → ℚ
  | 0 => 2 * rationalRadiusQ ^ 3 / 3
  | k + 1 => endpointAQ (k + 1) - endpointAQ k

def momentBQ : ℕ → ℚ
  | 0 => 0
  | k + 1 => endpointBQ (k + 1) - endpointBQ k

def comparisonIntegral0AQ : ℚ :=
  ∑ k ∈ Finset.range 666, rationalPowerCoefficientQ k * endpointAQ k

def comparisonIntegral0BQ : ℚ :=
  ∑ k ∈ Finset.range 666, rationalPowerCoefficientQ k * endpointBQ k

def comparisonIntegral2AQ : ℚ :=
  ∑ k ∈ Finset.range 666, rationalPowerCoefficientQ k * momentAQ k

def comparisonIntegral2BQ : ℚ :=
  ∑ k ∈ Finset.range 666, rationalPowerCoefficientQ k * momentBQ k

def logLowerQ : ℚ := 41845914400698788 / 10 ^ 16

def logUpperQ : ℚ := 41845914400698789 / 10 ^ 16

def centralErrorQ : ℚ :=
  2 * rationalRadiusQ *
    (70 * (21 / ((Nat.factorial 20 : ℚ) * 20)))

def tailBudgetQ : ℚ := 1 / 10 ^ 16

def q28Moment0LoQ : ℚ :=
  2397466416982805 / 18014398509481984 - 1 / 10 ^ 15

def q28Moment0HiQ : ℚ :=
  2397466416982805 / 18014398509481984 + 1 / 10 ^ 15

def q28Moment2LoQ : ℚ :=
  8817094793947821 / 576460752303423488 - 1 / 10 ^ 15

def q28Moment2HiQ : ℚ :=
  8817094793947821 / 576460752303423488 + 1 / 10 ^ 15

set_option maxHeartbeats 2000000000 in
-- reason: exact rational evaluation of four 666-term comparison sums
private theorem q28Moment0_lower_Q :
    q28Moment0LoQ + centralErrorQ ≤
      comparisonIntegral0AQ + comparisonIntegral0BQ * logUpperQ := by
  native_decide

set_option maxHeartbeats 2000000000 in
-- reason: exact rational evaluation of four 666-term comparison sums
private theorem q28Moment0_upper_Q :
    comparisonIntegral0AQ + comparisonIntegral0BQ * logLowerQ +
        centralErrorQ + 2 * tailBudgetQ ≤ q28Moment0HiQ := by
  native_decide

set_option maxHeartbeats 2000000000 in
-- reason: exact rational evaluation of four 666-term comparison sums
private theorem q28Moment2_lower_Q :
    q28Moment2LoQ + centralErrorQ ≤
      comparisonIntegral2AQ + comparisonIntegral2BQ * logUpperQ := by
  native_decide

set_option maxHeartbeats 2000000000 in
-- reason: exact rational evaluation of four 666-term comparison sums
private theorem q28Moment2_upper_Q :
    comparisonIntegral2AQ + comparisonIntegral2BQ * logLowerQ +
        centralErrorQ + 2 * tailBudgetQ ≤ q28Moment2HiQ := by
  native_decide

end Computable

noncomputable section

/-! ## Real polynomial representation -/

noncomputable def taylorScaledPolynomial : ℝ[X] :=
  ∑ j ∈ Finset.range 20,
    Polynomial.C (((-(2 / 35 : ℝ)) ^ j) / (j.factorial : ℝ)) *
      Polynomial.X ^ j

noncomputable def rationalPowerPolynomial : ℝ[X] :=
  taylorScaledPolynomial ^ 35

noncomputable def rationalPowerCoefficient (k : ℕ) : ℝ :=
  rationalPowerPolynomial.coeff k

theorem rationalPowerPolynomial_eq_map :
    rationalPowerPolynomial =
      rationalPowerPolynomialQ.map (algebraMap ℚ ℝ) := by
  have hbase : taylorScaledPolynomial =
      taylorScaledPolynomialQ.map (algebraMap ℚ ℝ) := by
    unfold taylorScaledPolynomial taylorScaledPolynomialQ
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [map_mul, map_C, map_pow, map_X]
    norm_num
  unfold rationalPowerPolynomial rationalPowerPolynomialQ
  rw [hbase, map_pow]

theorem rationalPowerCoefficient_eq_cast (k : ℕ) :
    rationalPowerCoefficient k = (rationalPowerCoefficientQ k : ℝ) := by
  rw [rationalPowerCoefficient, rationalPowerPolynomial_eq_map]
  simp [rationalPowerCoefficientQ]

private theorem taylorScaledPolynomial_natDegree_le :
    taylorScaledPolynomial.natDegree ≤ 19 := by
  unfold taylorScaledPolynomial
  refine natDegree_sum_le_of_forall_le
    (s := Finset.range 20)
    (f := fun j =>
      Polynomial.C (((-(2 / 35 : ℝ)) ^ j) / (j.factorial : ℝ)) *
        Polynomial.X ^ j)
    (n := 19) ?_
  intro j hj
  apply natDegree_le_iff_degree_le.mpr
  exact (degree_C_mul_X_pow_le j _).trans
    (WithBot.coe_le_coe.mpr
      (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))

private theorem rationalPowerPolynomial_natDegree_lt :
    rationalPowerPolynomial.natDegree < 666 := by
  calc
    rationalPowerPolynomial.natDegree ≤ 35 * taylorScaledPolynomial.natDegree :=
      natDegree_pow_le
    _ ≤ 35 * 19 := Nat.mul_le_mul_left 35 taylorScaledPolynomial_natDegree_le
    _ < 666 := by norm_num

theorem taylorScaledPolynomial_eval (z : ℝ) :
    eval z taylorScaledPolynomial =
      C1ScaledExpRationalEnvelope.expTaylor20 ((2 / 35 : ℝ) * z) := by
  rw [taylorScaledPolynomial, eval_finsetSum]
  simp [C1ScaledExpRationalEnvelope.expTaylor20]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem rationalPowerPolynomial_eval_eq_finite (z : ℝ) :
    eval z rationalPowerPolynomial =
      ∑ k ∈ Finset.range 666,
        rationalPowerCoefficient k * z ^ k := by
  rw [eval_eq_sum_range' rationalPowerPolynomial_natDegree_lt]
  rfl

theorem scaledClassWeightApprox_eq_finiteDenominatorPowerPolynomial
    (x : ℝ)
    (hx : x ∈ Icc (-(rationalRadius : ℝ)) (rationalRadius : ℝ)) :
    C1ScaledExpRationalEnvelope.scaledClassWeightApprox x =
      finiteDenominatorPowerPolynomial (Finset.range 666)
        rationalPowerCoefficient x := by
  have hsq := one_sub_sq_pos_of_abs_lt_one
    (abs_lt_one_of_mem_central hx)
  have hden : 1 - x ^ 2 ≠ 0 := hsq.ne'
  have hz :
      (2 / 35 : ℝ) / (1 - x ^ 2) =
        (2 / 35 : ℝ) * denominatorPower 1 x := by
    unfold denominatorPower
    field_simp [hden]
  unfold C1ScaledExpRationalEnvelope.scaledClassWeightApprox
  rw [hz]
  calc
    C1ScaledExpRationalEnvelope.expTaylor20
        ((2 / 35 : ℝ) * denominatorPower 1 x) ^ 35 =
        eval (denominatorPower 1 x) rationalPowerPolynomial := by
          rw [rationalPowerPolynomial, eval_pow,
            taylorScaledPolynomial_eval]
    _ = finiteDenominatorPowerPolynomial (Finset.range 666)
        rationalPowerCoefficient x :=
      rationalPowerPolynomial_eval_eq_finite (denominatorPower 1 x)

/-! ## Logarithm enclosure -/

private def logTwoLower : ℝ := 693147180559945309 / 10 ^ 18

private def logTwoUpper : ℝ := 693147180559945310 / 10 ^ 18

private def logSmallLower : ℝ := 25708356710206958 / 10 ^ 18

private def logSmallUpper : ℝ := 25708356710206959 / 10 ^ 18

private theorem log_two_lower : logTwoLower < Real.log 2 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have h := Real.exp_bound (x := logTwoLower)
    (by norm_num [logTwoLower]) (n := 20) (by norm_num)
  have hupp := (abs_sub_le_iff.mp h).1
  calc
    Real.exp logTwoLower ≤
        (∑ m ∈ Finset.range 20,
          logTwoLower ^ m / (m.factorial : ℝ)) +
          |logTwoLower| ^ 20 *
            ((↑(Nat.succ 20) : ℝ) /
              ((Nat.factorial 20 : ℝ) * 20)) := hupp
    _ < 2 := by norm_num [logTwoLower, Finset.sum_range_succ]

private theorem log_two_upper : Real.log 2 < logTwoUpper := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have h := Real.exp_bound (x := logTwoUpper)
    (by norm_num [logTwoUpper]) (n := 20) (by norm_num)
  have hlow := (abs_sub_le_iff.mp h).2
  calc
    2 <
        (∑ m ∈ Finset.range 20,
          logTwoUpper ^ m / (m.factorial : ℝ)) -
          |logTwoUpper| ^ 20 *
            ((↑(Nat.succ 20) : ℝ) /
              ((Nat.factorial 20 : ℝ) * 20)) := by
          norm_num [logTwoUpper, Finset.sum_range_succ]
    _ ≤ Real.exp logTwoUpper := hlow

private theorem log_small_lower :
    logSmallLower < Real.log (197 / 192) := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have h := Real.exp_bound (x := logSmallLower)
    (by norm_num [logSmallLower]) (n := 20) (by norm_num)
  have hupp := (abs_sub_le_iff.mp h).1
  calc
    Real.exp logSmallLower ≤
        (∑ m ∈ Finset.range 20,
          logSmallLower ^ m / (m.factorial : ℝ)) +
          |logSmallLower| ^ 20 *
            ((↑(Nat.succ 20) : ℝ) /
              ((Nat.factorial 20 : ℝ) * 20)) := hupp
    _ < 197 / 192 := by
          norm_num [logSmallLower, Finset.sum_range_succ]

private theorem log_small_upper :
    Real.log (197 / 192) < logSmallUpper := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have h := Real.exp_bound (x := logSmallUpper)
    (by norm_num [logSmallUpper]) (n := 20) (by norm_num)
  have hlow := (abs_sub_le_iff.mp h).2
  calc
    197 / 192 <
        (∑ m ∈ Finset.range 20,
          logSmallUpper ^ m / (m.factorial : ℝ)) -
          |logSmallUpper| ^ 20 *
            ((↑(Nat.succ 20) : ℝ) /
              ((Nat.factorial 20 : ℝ) * 20)) := by
          norm_num [logSmallUpper, Finset.sum_range_succ]
    _ ≤ Real.exp logSmallUpper := hlow

private theorem log_197_div_3_identity :
    Real.log (197 / 3) = 6 * Real.log 2 + Real.log (197 / 192) := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have hs : (0 : ℝ) < 197 / 192 := by norm_num
  calc
    Real.log (197 / 3) = Real.log ((2 : ℝ) ^ 6 * (197 / 192)) := by
      congr 1 <;> norm_num
    _ = Real.log ((2 : ℝ) ^ 6) + Real.log (197 / 192) := by
      rw [Real.log_mul (pow_ne_zero 6 h2.ne') hs.ne']
    _ = 6 * Real.log 2 + Real.log (197 / 192) := by
      rw [Real.log_pow]
      norm_num

private theorem log_197_div_3_lower :
    (logLowerQ : ℝ) ≤ Real.log (197 / 3) := by
  rw [log_197_div_3_identity]
  have h2 := log_two_lower
  have hs := log_small_lower
  norm_num [logLowerQ, logTwoLower, logSmallLower] at h2 hs ⊢
  linarith

private theorem log_197_div_3_upper :
    Real.log (197 / 3) ≤ (logUpperQ : ℝ) := by
  rw [log_197_div_3_identity]
  have h2 := log_two_upper
  have hs := log_small_upper
  norm_num [logUpperQ, logTwoUpper, logSmallUpper] at h2 hs ⊢
  linarith

/-! ## Linear endpoint form and exact comparison values -/

private theorem rationalPowerIntervalValue_linear (k : ℕ) :
    rationalPowerIntervalValue k =
      (endpointAQ k : ℝ) + (endpointBQ k : ℝ) * Real.log (197 / 3) := by
  induction k with
  | zero =>
      norm_num [rationalPowerIntervalValue, endpointAQ, endpointBQ,
        rationalRadiusQ, rationalRadius]
  | succ k ih =>
      cases k with
      | zero =>
          norm_num [rationalPowerIntervalValue, endpointAQ, endpointBQ,
            rationalRadiusQ, rationalRadius]
      | succ k =>
          simp only [rationalPowerIntervalValue, endpointAQ, endpointBQ]
          rw [ih]
          norm_num [rationalRadiusQ, rationalRadius]
          ring

private theorem denominatorPowerMomentValue_linear (k : ℕ) :
    denominatorPowerMomentValue k =
      (momentAQ k : ℝ) + (momentBQ k : ℝ) * Real.log (197 / 3) := by
  cases k with
  | zero =>
      norm_num [denominatorPowerMomentValue, momentAQ, momentBQ,
        rationalRadiusQ, rationalRadius]
  | succ k =>
      rw [denominatorPowerMomentValue, rationalPowerIntervalValue_linear,
        rationalPowerIntervalValue_linear]
      simp [momentAQ, momentBQ]

noncomputable def comparisonIntegral0 : ℝ :=
  finiteDenominatorPowerIntegralValue (Finset.range 666)
    rationalPowerCoefficient

noncomputable def comparisonIntegral2 : ℝ :=
  finiteDenominatorPowerMomentIntegralValue (Finset.range 666)
    rationalPowerCoefficient

private theorem comparisonIntegral0_linear :
    comparisonIntegral0 =
      (comparisonIntegral0AQ : ℝ) +
        (comparisonIntegral0BQ : ℝ) * Real.log (197 / 3) := by
  unfold comparisonIntegral0 finiteDenominatorPowerIntegralValue
  apply Finset.sum_congr rfl
  intro k hk
  rw [rationalPowerCoefficient_eq_cast,
    rationalPowerIntervalValue_linear]
  simp only [comparisonIntegral0AQ, comparisonIntegral0BQ]
  ring

private theorem comparisonIntegral2_linear :
    comparisonIntegral2 =
      (comparisonIntegral2AQ : ℝ) +
        (comparisonIntegral2BQ : ℝ) * Real.log (197 / 3) := by
  unfold comparisonIntegral2 finiteDenominatorPowerMomentIntegralValue
  apply Finset.sum_congr rfl
  intro k hk
  rw [rationalPowerCoefficient_eq_cast,
    denominatorPowerMomentValue_linear]
  simp only [comparisonIntegral2AQ, comparisonIntegral2BQ]
  ring

end
end C1ConcreteClassMomentCertificate
end Source
end ConnesWeilRH
