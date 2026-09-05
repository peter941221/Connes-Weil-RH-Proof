/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1ScaledExpRationalEnvelope
import ConnesWeilRH.Dev.C1RationalPowerIntegral
import ConnesWeilRH.Dev.C1ConcreteClassMomentGroundingC
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Record 1139/1145: concrete class-moment certificate (numeric gate)

The private checkpoint `q28_certificate_Q` and the two public q28
producers.  The computable data lives in C1ConcreteClassMomentBase and
the kernel-checked grounding machinery in
C1ConcreteClassMomentGrounding{A,B,C} (record-1145 RED-8 module split;
statements unchanged from 1139).

RH is NOT claimed.
-/

namespace ConnesWeilRH
namespace Source
namespace C1ConcreteClassMomentCertificate

open MeasureTheory Set
open Polynomial
open scoped BigOperators Interval

-- The numeric gate and its public consumers.  The computable data
-- lives in C1ConcreteClassMomentBase and the kernel-checked grounding
-- machinery in C1ConcreteClassMomentGrounding{A,B,C} (record 1145
-- RED-8 module split; statements unchanged from 1139).

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000000 in
-- reason: executable checkpoint for the shared 666-term comparison table;
-- the resulting native axiom is recorded in the 1139 post-run addendum.
private theorem q28_certificate_Q :
    let d := comparisonDataQ
    (q28Moment0LoQ + centralErrorQ ≤ d.a0 + d.b0 * logUpperQ ∧
      d.a0 + d.b0 * logLowerQ + centralErrorQ + 2 * tailBudgetQ ≤ q28Moment0HiQ) ∧
    (q28Moment2LoQ + centralErrorQ ≤ d.a2 + d.b2 * logUpperQ ∧
      d.a2 + d.b2 * logLowerQ + centralErrorQ + 2 * tailBudgetQ ≤ q28Moment2HiQ) ∧
    (d.b0 < 0 ∧ d.b2 < 0) := by
  simp only [comparisonDataQ]
  rw [comparison_a0_eq, comparison_b0_eq, comparison_a2_eq,
    comparison_b2_eq]
  norm_num (config := { maxSteps := 20000000 })




























private theorem q28Moment0_lower_Q :
    q28Moment0LoQ + centralErrorQ ≤
      comparisonIntegral0AQ + comparisonIntegral0BQ * logUpperQ := by
  simpa only [comparisonIntegral0AQ, comparisonIntegral0BQ] using q28_certificate_Q.1.1

private theorem q28Moment0_upper_Q :
    comparisonIntegral0AQ + comparisonIntegral0BQ * logLowerQ +
        centralErrorQ + 2 * tailBudgetQ ≤ q28Moment0HiQ := by
  simpa only [comparisonIntegral0AQ, comparisonIntegral0BQ] using q28_certificate_Q.1.2

private theorem q28Moment2_lower_Q :
    q28Moment2LoQ + centralErrorQ ≤
      comparisonIntegral2AQ + comparisonIntegral2BQ * logUpperQ := by
  simpa only [comparisonIntegral2AQ, comparisonIntegral2BQ] using q28_certificate_Q.2.1.1

private theorem q28Moment2_upper_Q :
    comparisonIntegral2AQ + comparisonIntegral2BQ * logLowerQ +
        centralErrorQ + 2 * tailBudgetQ ≤ q28Moment2HiQ := by
  simpa only [comparisonIntegral2AQ, comparisonIntegral2BQ] using q28_certificate_Q.2.1.2

private theorem comparisonBQ_negative :
    comparisonIntegral0BQ < 0 ∧ comparisonIntegral2BQ < 0 := by
  simpa only [comparisonIntegral0BQ, comparisonIntegral2BQ] using q28_certificate_Q.2.2

open C1ClassWindowObjects
open C1ClassGramMomentReduction
open C1ClassMomentIntegralCertificate
open C1ClassMomentTailCertificate
open C1ClassMomentCentralAssembly
open C1RationalPowerIntegral
open C1Q28ClassGramIntervalTransfer
open C1HboxRationalData
open C1ClassGramOwner

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
    rw [Polynomial.map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, map_X]
    norm_num
  unfold rationalPowerPolynomial rationalPowerPolynomialQ
  rw [hbase, ← Polynomial.map_pow]

theorem rationalPowerCoefficient_eq_cast (k : ℕ) :
    rationalPowerCoefficient k = (rationalPowerCoefficientQ k : ℝ) := by
  rw [rationalPowerCoefficient, rationalPowerPolynomial_eq_map]
  rw [Polynomial.coeff_map]
  change (algebraMap ℚ ℝ) ((taylorScaledPolynomialQ ^ 35).coeff k) =
    (powerCoefficientQSlow 35 k : ℝ)
  have h := powerCoefficientQSlow_eq_polynomial_coeff 35 k
  rw [← h]
  rfl

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
  simp only [eval_mul, eval_C, eval_pow, eval_X]
  refine Finset.sum_congr rfl ?_
  intro j hj
  ring

theorem rationalPowerPolynomial_eval_eq_finite (z : ℝ) :
    eval z rationalPowerPolynomial =
      ∑ k ∈ Finset.range 666,
        rationalPowerCoefficient k * z ^ k := by
  rw [eval_eq_sum_range' rationalPowerPolynomial_natDegree_lt]
  rfl

set_option maxRecDepth 1000000 in
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
      by
        simpa [finiteDenominatorPowerPolynomial, denominatorPower] using
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
  have hupp' : Real.exp logTwoLower ≤
      (∑ m ∈ Finset.range 20,
        logTwoLower ^ m / (m.factorial : ℝ)) +
        |logTwoLower| ^ 20 *
          ((↑(Nat.succ 20) : ℝ) /
            ((Nat.factorial 20 : ℝ) * 20)) := by
    linarith
  calc
    Real.exp logTwoLower ≤
        (∑ m ∈ Finset.range 20,
          logTwoLower ^ m / (m.factorial : ℝ)) +
          |logTwoLower| ^ 20 *
            ((↑(Nat.succ 20) : ℝ) /
              ((Nat.factorial 20 : ℝ) * 20)) := hupp'
    _ < 2 := by norm_num [logTwoLower, Finset.sum_range_succ]

private theorem log_two_upper : Real.log 2 < logTwoUpper := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have h := Real.exp_bound (x := logTwoUpper)
    (by norm_num [logTwoUpper]) (n := 20) (by norm_num)
  have hlow := (abs_sub_le_iff.mp h).2
  have hlow' :
      (∑ m ∈ Finset.range 20,
        logTwoUpper ^ m / (m.factorial : ℝ)) -
          |logTwoUpper| ^ 20 *
            ((↑(Nat.succ 20) : ℝ) /
              ((Nat.factorial 20 : ℝ) * 20)) ≤
        Real.exp logTwoUpper := by
    linarith
  calc
    2 <
        (∑ m ∈ Finset.range 20,
          logTwoUpper ^ m / (m.factorial : ℝ)) -
          |logTwoUpper| ^ 20 *
            ((↑(Nat.succ 20) : ℝ) /
              ((Nat.factorial 20 : ℝ) * 20)) := by
          norm_num [logTwoUpper, Finset.sum_range_succ]
    _ ≤ Real.exp logTwoUpper := hlow'

private theorem log_small_lower :
    logSmallLower < Real.log (197 / 192) := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have h := Real.exp_bound (x := logSmallLower)
    (by norm_num [logSmallLower]) (n := 20) (by norm_num)
  have hupp := (abs_sub_le_iff.mp h).1
  have hupp' : Real.exp logSmallLower ≤
      (∑ m ∈ Finset.range 20,
        logSmallLower ^ m / (m.factorial : ℝ)) +
        |logSmallLower| ^ 20 *
          ((↑(Nat.succ 20) : ℝ) /
            ((Nat.factorial 20 : ℝ) * 20)) := by
    linarith
  calc
    Real.exp logSmallLower ≤
        (∑ m ∈ Finset.range 20,
          logSmallLower ^ m / (m.factorial : ℝ)) +
          |logSmallLower| ^ 20 *
            ((↑(Nat.succ 20) : ℝ) /
              ((Nat.factorial 20 : ℝ) * 20)) := hupp'
    _ < 197 / 192 := by
          norm_num [logSmallLower, Finset.sum_range_succ]

private theorem log_small_upper :
    Real.log (197 / 192) < logSmallUpper := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have h := Real.exp_bound (x := logSmallUpper)
    (by norm_num [logSmallUpper]) (n := 20) (by norm_num)
  have hlow := (abs_sub_le_iff.mp h).2
  have hlow' :
      (∑ m ∈ Finset.range 20,
        logSmallUpper ^ m / (m.factorial : ℝ)) -
          |logSmallUpper| ^ 20 *
            ((↑(Nat.succ 20) : ℝ) /
              ((Nat.factorial 20 : ℝ) * 20)) ≤
        Real.exp logSmallUpper := by
    linarith
  calc
    197 / 192 <
        (∑ m ∈ Finset.range 20,
          logSmallUpper ^ m / (m.factorial : ℝ)) -
          |logSmallUpper| ^ 20 *
            ((↑(Nat.succ 20) : ℝ) /
              ((Nat.factorial 20 : ℝ) * 20)) := by
          norm_num [logSmallUpper, Finset.sum_range_succ]
    _ = _ := by ring
    _ ≤ Real.exp logSmallUpper := hlow'

private theorem log_197_div_3_identity :
    Real.log (197 / 3) = 6 * Real.log 2 + Real.log (197 / 192) := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have hs : (0 : ℝ) < 197 / 192 := by norm_num
  calc
    Real.log (197 / 3) = Real.log ((2 : ℝ) ^ 6 * (197 / 192)) := by
      congr 1; norm_num
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
      ring

noncomputable def comparisonIntegral0 : ℝ :=
  finiteDenominatorPowerIntegralValue (Finset.range 666)
    rationalPowerCoefficient

noncomputable def comparisonIntegral2 : ℝ :=
  finiteDenominatorPowerMomentIntegralValue (Finset.range 666)
    rationalPowerCoefficient

private theorem rationalPowerCoefficient_eq_cached (k : ℕ) (hk : k < 666) :
    rationalPowerCoefficient k =
      (powerCoefficientQ 35 k : ℝ) := by
  rw [rationalPowerCoefficient_eq_cast]
  change (powerCoefficientQSlow 35 k : ℝ) =
    (powerCoefficientQ 35 k : ℝ)
  rw [powerCoefficientQ_eq_slow 35 k hk]

private theorem cast_cached_sum (f : ℕ → ℚ) :
    ((∑ k ∈ Finset.range 666, powerCoefficientQ 35 k * f k : ℚ) : ℝ) =
      ∑ k ∈ Finset.range 666,
        (powerCoefficientQ 35 k : ℝ) * (f k : ℝ) := by
  norm_cast

private theorem comparisonIntegral0AQ_cast :
    (comparisonIntegral0AQ : ℝ) =
      ∑ k ∈ Finset.range 666,
        (powerCoefficientQ 35 k : ℝ) * (endpointAQ k : ℝ) := by
  simpa [comparisonIntegral0AQ, comparisonDataQ, powerCoefficientQ] using
    (cast_cached_sum endpointAQ)

private theorem comparisonIntegral0BQ_cast :
    (comparisonIntegral0BQ : ℝ) =
      ∑ k ∈ Finset.range 666,
        (powerCoefficientQ 35 k : ℝ) * (endpointBQ k : ℝ) := by
  simpa [comparisonIntegral0BQ, comparisonDataQ, powerCoefficientQ] using
    (cast_cached_sum endpointBQ)

private theorem comparisonIntegral2AQ_cast :
    (comparisonIntegral2AQ : ℝ) =
      ∑ k ∈ Finset.range 666,
        (powerCoefficientQ 35 k : ℝ) * (momentAQ k : ℝ) := by
  simpa [comparisonIntegral2AQ, comparisonDataQ, powerCoefficientQ] using
    (cast_cached_sum momentAQ)

private theorem comparisonIntegral2BQ_cast :
    (comparisonIntegral2BQ : ℝ) =
      ∑ k ∈ Finset.range 666,
        (powerCoefficientQ 35 k : ℝ) * (momentBQ k : ℝ) := by
  simpa [comparisonIntegral2BQ, comparisonDataQ, powerCoefficientQ] using
    (cast_cached_sum momentBQ)

private theorem sum_cached_linear (a b : ℕ → ℚ) (L : ℝ) :
    (∑ k ∈ Finset.range 666,
        (powerCoefficientQ 35 k : ℝ) *
          ((a k : ℝ) + (b k : ℝ) * L)) =
      (∑ k ∈ Finset.range 666,
        (powerCoefficientQ 35 k : ℝ) * (a k : ℝ)) +
      (∑ k ∈ Finset.range 666,
        (powerCoefficientQ 35 k : ℝ) * (b k : ℝ)) * L := by
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  have hsecond :
      (∑ k ∈ Finset.range 666,
        (powerCoefficientQ 35 k : ℝ) * ((b k : ℝ) * L)) =
        (∑ k ∈ Finset.range 666,
          (powerCoefficientQ 35 k : ℝ) * (b k : ℝ)) * L := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hsecond]

set_option maxRecDepth 1000000 in
private theorem comparisonIntegral0_linear :
    comparisonIntegral0 =
      (comparisonIntegral0AQ : ℝ) +
        (comparisonIntegral0BQ : ℝ) * Real.log (197 / 3) := by
  unfold comparisonIntegral0 finiteDenominatorPowerIntegralValue
  calc
    (∑ k ∈ Finset.range 666,
        rationalPowerCoefficient k * rationalPowerIntervalValue k) =
        ∑ k ∈ Finset.range 666, rationalPowerCoefficient k *
          ((endpointAQ k : ℝ) + (endpointBQ k : ℝ) * Real.log (197 / 3)) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [rationalPowerIntervalValue_linear]
    _ = ∑ k ∈ Finset.range 666, (powerCoefficientQ 35 k : ℝ) *
          ((endpointAQ k : ℝ) + (endpointBQ k : ℝ) * Real.log (197 / 3)) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [rationalPowerCoefficient_eq_cached k (Finset.mem_range.mp hk)]
    _ = (comparisonIntegral0AQ : ℝ) +
          (comparisonIntegral0BQ : ℝ) * Real.log (197 / 3) := by
      rw [sum_cached_linear, comparisonIntegral0AQ_cast,
        comparisonIntegral0BQ_cast]

set_option maxRecDepth 1000000 in
private theorem comparisonIntegral2_linear :
    comparisonIntegral2 =
      (comparisonIntegral2AQ : ℝ) +
        (comparisonIntegral2BQ : ℝ) * Real.log (197 / 3) := by
  unfold comparisonIntegral2 finiteDenominatorPowerMomentIntegralValue
  calc
    (∑ k ∈ Finset.range 666,
        rationalPowerCoefficient k * denominatorPowerMomentValue k) =
        ∑ k ∈ Finset.range 666, rationalPowerCoefficient k *
          ((momentAQ k : ℝ) + (momentBQ k : ℝ) * Real.log (197 / 3)) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [denominatorPowerMomentValue_linear]
    _ = ∑ k ∈ Finset.range 666, (powerCoefficientQ 35 k : ℝ) *
          ((momentAQ k : ℝ) + (momentBQ k : ℝ) * Real.log (197 / 3)) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [rationalPowerCoefficient_eq_cached k (Finset.mem_range.mp hk)]
    _ = (comparisonIntegral2AQ : ℝ) +
          (comparisonIntegral2BQ : ℝ) * Real.log (197 / 3) := by
      rw [sum_cached_linear, comparisonIntegral2AQ_cast,
        comparisonIntegral2BQ_cast]

/-! ## Concrete central comparison functions -/

private noncomputable def centralPointwiseError : ℝ :=
  (70 : ℝ) * C1ScaledExpRationalEnvelope.expTaylor20Error

private noncomputable def centralComparison0 (x : ℝ) : ℝ :=
  finiteDenominatorPowerPolynomial (Finset.range 666)
    rationalPowerCoefficient x

private noncomputable def centralComparison2 (x : ℝ) : ℝ :=
  finiteDenominatorPowerMomentPolynomial (Finset.range 666)
    rationalPowerCoefficient x

private theorem central_error_eq_cast :
    (2 * rationalRadius) * centralPointwiseError = (centralErrorQ : ℝ) := by
  norm_num [centralPointwiseError, centralErrorQ, rationalRadius,
    rationalRadiusQ, C1ScaledExpRationalEnvelope.expTaylor20Error]

private theorem centralComparison0_intervalIntegrable :
    IntervalIntegrable centralComparison0 volume
      (-rationalRadius) rationalRadius := by
  unfold centralComparison0 finiteDenominatorPowerPolynomial
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le (by norm_num [rationalRadius])]
  exact continuousOn_finsetSum _ (fun k hk =>
    continuousOn_const.mul (denominatorPower_continuousOn k))

private theorem centralComparison2_intervalIntegrable :
    IntervalIntegrable centralComparison2 volume
      (-rationalRadius) rationalRadius := by
  unfold centralComparison2 finiteDenominatorPowerMomentPolynomial
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le (by norm_num [rationalRadius])]
  exact continuousOn_finsetSum _ (fun k hk =>
    continuousOn_const.mul ((continuousOn_id.pow 2).mul
      (denominatorPower_continuousOn k)))

private theorem centralComparison0_integral :
    (∫ x in (-rationalRadius)..rationalRadius, centralComparison0 x) =
      comparisonIntegral0 := by
  simpa [centralComparison0, comparisonIntegral0] using
    (intervalIntegral_finiteDenominatorPowerPolynomial
      (Finset.range 666) rationalPowerCoefficient)

private theorem centralComparison2_integral :
    (∫ x in (-rationalRadius)..rationalRadius, centralComparison2 x) =
      comparisonIntegral2 := by
  simpa [centralComparison2, comparisonIntegral2] using
    (intervalIntegral_finiteDenominatorPowerMomentPolynomial
      (Finset.range 666) rationalPowerCoefficient)

private theorem centralComparison0_lower_integral :
    (∫ x in (-rationalRadius)..rationalRadius,
      centralComparison0 x - centralPointwiseError) =
      comparisonIntegral0 - (centralErrorQ : ℝ) := by
  rw [intervalIntegral.integral_sub centralComparison0_intervalIntegrable
      intervalIntegrable_const, centralComparison0_integral,
    intervalIntegral.integral_const, smul_eq_mul]
  rw [show rationalRadius - (-rationalRadius) = 2 * rationalRadius by ring,
    central_error_eq_cast]

private theorem centralComparison0_upper_integral :
    (∫ x in (-rationalRadius)..rationalRadius,
      centralComparison0 x + centralPointwiseError) =
      comparisonIntegral0 + (centralErrorQ : ℝ) := by
  rw [intervalIntegral.integral_add centralComparison0_intervalIntegrable
      intervalIntegrable_const, centralComparison0_integral,
    intervalIntegral.integral_const, smul_eq_mul]
  rw [show rationalRadius - (-rationalRadius) = 2 * rationalRadius by ring,
    central_error_eq_cast]

private theorem centralComparison2_lower_integral :
    (∫ x in (-rationalRadius)..rationalRadius,
      centralComparison2 x - centralPointwiseError) =
      comparisonIntegral2 - (centralErrorQ : ℝ) := by
  rw [intervalIntegral.integral_sub centralComparison2_intervalIntegrable
      intervalIntegrable_const, centralComparison2_integral,
    intervalIntegral.integral_const, smul_eq_mul]
  rw [show rationalRadius - (-rationalRadius) = 2 * rationalRadius by ring,
    central_error_eq_cast]

private theorem centralComparison2_upper_integral :
    (∫ x in (-rationalRadius)..rationalRadius,
      centralComparison2 x + centralPointwiseError) =
      comparisonIntegral2 + (centralErrorQ : ℝ) := by
  rw [intervalIntegral.integral_add centralComparison2_intervalIntegrable
      intervalIntegrable_const, centralComparison2_integral,
    intervalIntegral.integral_const, smul_eq_mul]
  rw [show rationalRadius - (-rationalRadius) = 2 * rationalRadius by ring,
    central_error_eq_cast]

private theorem centralComparison0_error {x : ℝ}
    (hx : x ∈ Icc (-rationalRadius) rationalRadius) :
    |classMomentIntegrand 0 x - centralComparison0 x| ≤
      centralPointwiseError := by
  have hx' : x ∈ Icc (-(97 / 100 : ℝ)) (97 / 100) := by
    simpa [rationalRadius] using hx
  have h := C1ScaledExpRationalEnvelope.classMomentIntegrand_central_approx_error
    0 x hx'
  rw [scaledClassWeightApprox_eq_finiteDenominatorPowerPolynomial x hx] at h
  simpa [centralComparison0, centralPointwiseError] using h

private theorem scaledMomentApprox_eq_finiteMoment {x : ℝ}
    (hx : x ∈ Icc (-rationalRadius) rationalRadius) :
    x ^ 2 * C1ScaledExpRationalEnvelope.scaledClassWeightApprox x =
      finiteDenominatorPowerMomentPolynomial (Finset.range 666)
        rationalPowerCoefficient x := by
  rw [scaledClassWeightApprox_eq_finiteDenominatorPowerPolynomial x hx]
  unfold finiteDenominatorPowerMomentPolynomial
    finiteDenominatorPowerPolynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

private theorem centralComparison2_error {x : ℝ}
    (hx : x ∈ Icc (-rationalRadius) rationalRadius) :
    |classMomentIntegrand 2 x - centralComparison2 x| ≤
      centralPointwiseError := by
  have hx' : x ∈ Icc (-(97 / 100 : ℝ)) (97 / 100) := by
    simpa [rationalRadius] using hx
  have h := C1ScaledExpRationalEnvelope.classMomentIntegrand_central_approx_error
    2 x hx'
  rw [scaledMomentApprox_eq_finiteMoment hx] at h
  simpa [centralComparison2, centralPointwiseError] using h

/-! ## Transport of the exact rational certificate -/

private theorem q28Moment0LoQ_cast :
    (q28Moment0LoQ : ℝ) = q28Moment0Lo := by
  norm_num [q28Moment0LoQ, q28Moment0Lo]

private theorem q28Moment0HiQ_cast :
    (q28Moment0HiQ : ℝ) = q28Moment0Hi := by
  norm_num [q28Moment0HiQ, q28Moment0Hi]

private theorem q28Moment2LoQ_cast :
    (q28Moment2LoQ : ℝ) = q28Moment2Lo := by
  norm_num [q28Moment2LoQ, q28Moment2Lo]

private theorem q28Moment2HiQ_cast :
    (q28Moment2HiQ : ℝ) = q28Moment2Hi := by
  norm_num [q28Moment2HiQ, q28Moment2Hi]

private theorem q28Moment0_lower_real :
    (q28Moment0LoQ : ℝ) + (centralErrorQ : ℝ) ≤
      (comparisonIntegral0AQ : ℝ) +
        (comparisonIntegral0BQ : ℝ) * (logUpperQ : ℝ) := by
  exact_mod_cast q28Moment0_lower_Q

private theorem q28Moment0_upper_real :
    (comparisonIntegral0AQ : ℝ) +
        (comparisonIntegral0BQ : ℝ) * (logLowerQ : ℝ) +
        (centralErrorQ : ℝ) + 2 * (tailBudgetQ : ℝ) ≤
      (q28Moment0HiQ : ℝ) := by
  exact_mod_cast q28Moment0_upper_Q

private theorem q28Moment2_lower_real :
    (q28Moment2LoQ : ℝ) + (centralErrorQ : ℝ) ≤
      (comparisonIntegral2AQ : ℝ) +
        (comparisonIntegral2BQ : ℝ) * (logUpperQ : ℝ) := by
  exact_mod_cast q28Moment2_lower_Q

private theorem q28Moment2_upper_real :
    (comparisonIntegral2AQ : ℝ) +
        (comparisonIntegral2BQ : ℝ) * (logLowerQ : ℝ) +
        (centralErrorQ : ℝ) + 2 * (tailBudgetQ : ℝ) ≤
      (q28Moment2HiQ : ℝ) := by
  exact_mod_cast q28Moment2_upper_Q

private theorem comparisonBQ_negative_real :
    (comparisonIntegral0BQ : ℝ) < 0 ∧
      (comparisonIntegral2BQ : ℝ) < 0 := by
  exact_mod_cast comparisonBQ_negative

private theorem centralComparison0_lower_value :
  q28Moment0Lo ≤
      ∫ x in (-rationalRadius)..rationalRadius,
        centralComparison0 x - centralPointwiseError := by
  rw [centralComparison0_lower_integral, ← q28Moment0LoQ_cast,
    comparisonIntegral0_linear]
  have hq := q28Moment0_lower_real
  have hlog := log_197_div_3_upper
  have hB := comparisonBQ_negative_real.1
  have hprod :
      (comparisonIntegral0BQ : ℝ) * (logUpperQ : ℝ) ≤
        (comparisonIntegral0BQ : ℝ) * Real.log (197 / 3) :=
    mul_le_mul_of_nonpos_left hlog (le_of_lt hB)
  linarith

private theorem centralComparison0_upper_value :
    (∫ x in (-rationalRadius)..rationalRadius,
      centralComparison0 x + centralPointwiseError) ≤
      q28Moment0Hi - 2 * (tailBudgetQ : ℝ) := by
  rw [centralComparison0_upper_integral, ← q28Moment0HiQ_cast,
    comparisonIntegral0_linear]
  have hq := q28Moment0_upper_real
  have hlog := log_197_div_3_lower
  have hB := comparisonBQ_negative_real.1
  have hprod :
      (comparisonIntegral0BQ : ℝ) * Real.log (197 / 3) ≤
        (comparisonIntegral0BQ : ℝ) * (logLowerQ : ℝ) :=
    mul_le_mul_of_nonpos_left hlog (le_of_lt hB)
  linarith

private theorem centralComparison2_lower_value :
  q28Moment2Lo ≤
      ∫ x in (-rationalRadius)..rationalRadius,
        centralComparison2 x - centralPointwiseError := by
  rw [centralComparison2_lower_integral, ← q28Moment2LoQ_cast,
    comparisonIntegral2_linear]
  have hq := q28Moment2_lower_real
  have hlog := log_197_div_3_upper
  have hB := comparisonBQ_negative_real.2
  have hprod :
      (comparisonIntegral2BQ : ℝ) * (logUpperQ : ℝ) ≤
        (comparisonIntegral2BQ : ℝ) * Real.log (197 / 3) :=
    mul_le_mul_of_nonpos_left hlog (le_of_lt hB)
  linarith

private theorem centralComparison2_upper_value :
    (∫ x in (-rationalRadius)..rationalRadius,
      centralComparison2 x + centralPointwiseError) ≤
      q28Moment2Hi - 2 * (tailBudgetQ : ℝ) := by
  rw [centralComparison2_upper_integral, ← q28Moment2HiQ_cast,
    comparisonIntegral2_linear]
  have hq := q28Moment2_upper_real
  have hlog := log_197_div_3_lower
  have hB := comparisonBQ_negative_real.2
  have hprod :
      (comparisonIntegral2BQ : ℝ) * Real.log (197 / 3) ≤
        (comparisonIntegral2BQ : ℝ) * (logLowerQ : ℝ) :=
    mul_le_mul_of_nonpos_left hlog (le_of_lt hB)
  linarith

private noncomputable def concreteCentralEnvelope0 :
    IntegralEnvelope (classMomentIntegrand 0) (-rationalRadius) rationalRadius
      q28Moment0Lo (q28Moment0Hi - 2 * (tailBudgetQ : ℝ)) := by
  refine
    { lower := fun x => centralComparison0 x - centralPointwiseError
      upper := fun x => centralComparison0 x + centralPointwiseError
      lower_integrable := centralComparison0_intervalIntegrable.sub
        intervalIntegrable_const
      target_integrable := classMomentIntegrand_intervalIntegrable 0 _ _
      upper_integrable := centralComparison0_intervalIntegrable.add
        intervalIntegrable_const
      lower_le := ?_
      upper_le := ?_
      lower_value := centralComparison0_lower_value
      upper_value := centralComparison0_upper_value }
  · intro x hx
    linarith [(abs_le.mp (centralComparison0_error hx)).1]
  · intro x hx
    linarith [(abs_le.mp (centralComparison0_error hx)).2]

private noncomputable def concreteCentralEnvelope2 :
    IntegralEnvelope (classMomentIntegrand 2) (-rationalRadius) rationalRadius
      q28Moment2Lo (q28Moment2Hi - 2 * (tailBudgetQ : ℝ)) := by
  refine
    { lower := fun x => centralComparison2 x - centralPointwiseError
      upper := fun x => centralComparison2 x + centralPointwiseError
      lower_integrable := centralComparison2_intervalIntegrable.sub
        intervalIntegrable_const
      target_integrable := classMomentIntegrand_intervalIntegrable 2 _ _
      upper_integrable := centralComparison2_intervalIntegrable.add
        intervalIntegrable_const
      lower_le := ?_
      upper_le := ?_
      lower_value := centralComparison2_lower_value
      upper_value := centralComparison2_upper_value }
  · intro x hx
    linarith [(abs_le.mp (centralComparison2_error hx)).1]
  · intro x hx
    linarith [(abs_le.mp (centralComparison2_error hx)).2]

/-! ## The `97/100` endpoint tail -/

private lemma exp_neg_one_lt_three_eighths_97 :
    Real.exp (-1) < (3 / 8 : ℝ) := by
  have h := Real.exp_bound (x := (-1 : ℝ))
    (by norm_num) (n := 7) (by norm_num)
  have hup := (abs_sub_le_iff.mp h).1
  norm_num [Finset.sum_range_succ] at hup
  nlinarith

private lemma exp_neg_nat_eq_pow_97 (n : ℕ) :
    Real.exp (-(n : ℝ)) = Real.exp (-1) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.cast_succ]
      have harg : -((n : ℝ) + 1) = -(n : ℝ) + (-1 : ℝ) := by ring
      rw [harg, Real.exp_add, ih, pow_succ]

private lemma tail_constant_97_lt :
    (1 - (97 / 100 : ℝ)) *
        Real.exp (-(2 / (1 - (97 / 100 : ℝ) ^ 2))) <
      (tailBudgetQ : ℝ) := by
  have hq : (169 / 5 : ℝ) ≤ 2 / (1 - (97 / 100 : ℝ) ^ 2) := by
    norm_num
  have hexp : Real.exp (-(2 / (1 - (97 / 100 : ℝ) ^ 2))) ≤
      Real.exp (-(169 / 5 : ℝ)) := by
    apply Real.exp_le_exp.mpr
    linarith
  have hexp_one : Real.exp (-1) < (3679 / 10000 : ℝ) := by
    have h := Real.exp_bound (x := (-1 : ℝ))
      (by norm_num) (n := 12) (by norm_num)
    have hup := (abs_sub_le_iff.mp h).1
    norm_num [Finset.sum_range_succ] at hup
    linarith
  have hexp_four_fifths : Real.exp (-(4 / 5 : ℝ)) <
      (9 / 20 : ℝ) := by
    have h := Real.exp_bound (x := (-(4 / 5 : ℝ)))
      (by norm_num) (n := 7) (by norm_num)
    have hup := (abs_sub_le_iff.mp h).1
    norm_num [Finset.sum_range_succ] at hup
    linarith
  have hexp_split : Real.exp (-(169 / 5 : ℝ)) <
      (3679 / 10000 : ℝ) ^ 33 * (9 / 20 : ℝ) := by
    rw [show -(169 / 5 : ℝ) = -(33 : ℝ) + -(4 / 5 : ℝ) by norm_num,
      Real.exp_add]
    have h33 : Real.exp (-33 : ℝ) = Real.exp (-1) ^ 33 := by
      exact exp_neg_nat_eq_pow_97 33
    rw [h33]
    have hpow := pow_lt_pow_left₀ hexp_one
      (Real.exp_pos (-1)).le (n := 33) (by norm_num)
    exact (mul_lt_mul_of_pos_right hpow
      (Real.exp_pos (-(4 / 5 : ℝ)))).trans
      (mul_lt_mul_of_pos_left hexp_four_fifths (by norm_num))
  calc
    (1 - (97 / 100 : ℝ)) *
          Real.exp (-(2 / (1 - (97 / 100 : ℝ) ^ 2))) ≤
        (1 - (97 / 100 : ℝ)) * Real.exp (-(169 / 5 : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hexp (by norm_num)
    _ < (1 - (97 / 100 : ℝ)) *
          ((3679 / 10000 : ℝ) ^ 33 * (9 / 20 : ℝ)) := by
      exact mul_lt_mul_of_pos_left hexp_split (by norm_num)
    _ < (1 / 10 ^ 16 : ℝ) := by norm_num
    _ = (tailBudgetQ : ℝ) := by norm_num [tailBudgetQ]

private theorem rightTail_97_lt (n : ℕ) :
    ‖∫ x in rationalRadius..1, classMomentIntegrand n x‖ <
      (tailBudgetQ : ℝ) := by
  exact lt_of_le_of_lt
    (norm_intervalIntegral_classMoment_rightTail_le n
      (r := rationalRadius) rationalRadius_pos rationalRadius_lt_one)
    (by simpa [rationalRadius] using tail_constant_97_lt)

private theorem leftTail_97_lt (n : ℕ) :
    ‖∫ x in (-1 : ℝ)..(-rationalRadius), classMomentIntegrand n x‖ <
      (tailBudgetQ : ℝ) := by
  exact lt_of_le_of_lt
    (norm_intervalIntegral_classMoment_leftTail_le n
      (r := rationalRadius) rationalRadius_pos rationalRadius_lt_one)
    (by simpa [rationalRadius] using tail_constant_97_lt)

private theorem classMoment_leftTail_eq_rightTail_97
    {n : ℕ} (hn : Even n) :
    (∫ x in (-1 : ℝ)..(-rationalRadius), classMomentIntegrand n x) =
      ∫ x in rationalRadius..1, classMomentIntegrand n x := by
  rw [← intervalIntegral.integral_comp_neg
    (f := classMomentIntegrand n) (a := rationalRadius) (b := (1 : ℝ))]
  refine intervalIntegral.integral_congr ?_
  intro x hx
  exact classMomentIntegrand_neg_of_even hn x

private theorem classMoment_eq_three_interval_97 (n : ℕ) :
    classMoment n =
      (∫ x in (-1 : ℝ)..(-rationalRadius), classMomentIntegrand n x) +
        (∫ x in (-rationalRadius)..rationalRadius,
          classMomentIntegrand n x) +
        (∫ x in rationalRadius..1, classMomentIntegrand n x) := by
  rw [classMoment_eq_intervalIntegral]
  have hleft := classMomentIntegrand_intervalIntegrable n
    (-1 : ℝ) (-rationalRadius)
  have hmiddle := classMomentIntegrand_intervalIntegrable n
    (-rationalRadius) rationalRadius
  have hright := classMomentIntegrand_intervalIntegrable n
    rationalRadius 1
  have hleftRest := classMomentIntegrand_intervalIntegrable n
    (-rationalRadius) (1 : ℝ)
  rw [← intervalIntegral.integral_add_adjacent_intervals hleft hleftRest,
    ← intervalIntegral.integral_add_adjacent_intervals hmiddle hright]
  ring

private theorem rightTail_nonneg_97 {n : ℕ} (hn : Even n) :
    0 ≤ ∫ x in rationalRadius..1, classMomentIntegrand n x := by
  apply intervalIntegral.integral_nonneg_of_forall
  · norm_num [rationalRadius]
  · intro x
    unfold classMomentIntegrand
    exact mul_nonneg (Even.pow_nonneg hn x) (classUnitWeight_nonneg x)

private theorem classMoment_bounds_of_concreteCentralEnvelope
    {n : ℕ} (hn : Even n) {lo hi : ℝ}
    (h : IntegralEnvelope (classMomentIntegrand n) (-rationalRadius)
      rationalRadius lo hi) :
    lo ≤ classMoment n ∧
      classMoment n < hi + 2 * (tailBudgetQ : ℝ) := by
  have hcentral := integral_bounds_of_integralEnvelope
    (by norm_num [rationalRadius]) h
  have htailAbs :
      |∫ x in rationalRadius..1, classMomentIntegrand n x| <
        (tailBudgetQ : ℝ) := by
    simpa [Real.norm_eq_abs] using rightTail_97_lt n
  have htailUpper := (abs_lt.mp htailAbs).2
  have htailNonneg := rightTail_nonneg_97 hn
  rw [classMoment_eq_three_interval_97 n,
    classMoment_leftTail_eq_rightTail_97 hn]
  constructor <;> linarith [hcentral.1, hcentral.2, htailUpper, htailNonneg]

/-! ## Public G-side producer and Hbox consumer -/

theorem q28_baseMoment_bounds_of_concrete_certificate :
    (q28Moment0Lo ≤ classMoment 0 ∧
      classMoment 0 ≤ q28Moment0Hi) ∧
    (q28Moment2Lo ≤ classMoment 2 ∧
      classMoment 2 ≤ q28Moment2Hi) := by
  have h0 := classMoment_bounds_of_concreteCentralEnvelope
    (n := 0) (lo := q28Moment0Lo)
    (hi := q28Moment0Hi - 2 * (tailBudgetQ : ℝ))
    (by exact ⟨0, by norm_num⟩) concreteCentralEnvelope0
  have h2 := classMoment_bounds_of_concreteCentralEnvelope
    (n := 2) (lo := q28Moment2Lo)
    (hi := q28Moment2Hi - 2 * (tailBudgetQ : ℝ))
    (by exact ⟨1, by norm_num⟩) concreteCentralEnvelope2
  constructor
  · exact ⟨h0.1, by linarith [h0.2]⟩
  · exact ⟨h2.1, by linarith [h2.2]⟩

theorem q28_hbox_of_concrete_certificate
    (M_true : Matrix (Fin 8) (Fin 8) ℝ)
    (hM : ∀ i j, MLo_q28 i j ≤ M_true i j ∧
      M_true i j ≤ MHi_q28 i j) :
    Hbox GLo_q28 GHi_q28 MLo_q28 MHi_q28
      (classGramMatrix 2 (by norm_num)) M_true := by
  have hMom := q28_baseMoment_bounds_of_concrete_certificate
  exact q28_hbox_of_baseMomentBounds M_true hMom.1 hMom.2 hM

end
end C1ConcreteClassMomentCertificate
end Source
end ConnesWeilRH
