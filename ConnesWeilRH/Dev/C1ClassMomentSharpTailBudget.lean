/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1ClassMomentCentralAssembly

/-!
# Record 1136: sharp endpoint budget for the true class moments

The coarse `10 ^ 15` endpoint estimate in record 1134 is sufficient for a
standalone tail statement but is too wide to feed the registered q28 moment
boxes after the two tails are assembled.  The same Taylor estimate gives a
`10 ^ 40` bound.  This file exposes that sharper result and consumes it in a
sign-sensitive even-moment assembly: nonnegativity preserves the central lower
endpoint, while the upper endpoint pays twice the sharp tail budget.

No central target value is supplied here.  RH is NOT claimed.
-/

namespace ConnesWeilRH
namespace Source
namespace C1ClassMomentSharpTailBudget

open MeasureTheory Set
open C1ClassWindowObjects
open C1ClassGramMomentReduction
open C1ClassMomentIntegralCertificate
open C1ClassMomentTailCertificate
open C1ClassMomentCentralAssembly
open C1Q28ClassGramIntervalTransfer
open scoped BigOperators Interval

noncomputable section

/-! ## The sharper rational exponential estimate -/

private lemma exp_neg_one_lt_three_eighths_sharp :
    Real.exp (-1) < (3 / 8 : ℝ) := by
  have h := Real.exp_bound (x := (-1 : ℝ))
    (by norm_num) (n := 7) (by norm_num)
  have hup := (abs_sub_le_iff.mp h).1
  norm_num [Finset.sum_range_succ] at hup
  nlinarith

private lemma exp_neg_nat_eq_pow_sharp (n : ℕ) :
    Real.exp (-(n : ℝ)) = Real.exp (-1) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.cast_succ]
      have harg : -((n : ℝ) + 1) = -(n : ℝ) + (-1 : ℝ) := by ring
      rw [harg, Real.exp_add, ih, pow_succ]

private lemma q99_tail_constant_lt_one_div_ten_pow_40 :
    (1 - (99 / 100 : ℝ)) *
        Real.exp (-(2 / (1 - (99 / 100 : ℝ) ^ 2))) <
      (1 / 10 ^ 40 : ℝ) := by
  have hq : (100 : ℝ) ≤ 2 / (1 - (99 / 100 : ℝ) ^ 2) := by
    norm_num
  have hexp : Real.exp (-(2 / (1 - (99 / 100 : ℝ) ^ 2))) ≤
      Real.exp (-100) := by
    apply Real.exp_le_exp.mpr
    linarith
  have hpowid : Real.exp (-100) = Real.exp (-1) ^ 100 := by
    exact exp_neg_nat_eq_pow_sharp 100
  have hpow : Real.exp (-100) < (3 / 8 : ℝ) ^ 100 := by
    rw [hpowid]
    exact pow_lt_pow_left₀ exp_neg_one_lt_three_eighths_sharp
      (Real.exp_pos (-1)).le (by norm_num)
  calc
    (1 - (99 / 100 : ℝ)) *
          Real.exp (-(2 / (1 - (99 / 100 : ℝ) ^ 2))) ≤
        (1 - (99 / 100 : ℝ)) * Real.exp (-100) := by
      exact mul_le_mul_of_nonneg_left hexp (by norm_num)
    _ < (1 - (99 / 100 : ℝ)) * (3 / 8 : ℝ) ^ 100 := by
      gcongr
    _ < (1 / 10 ^ 40 : ℝ) := by norm_num

/-! ## Sharp tail bounds -/

theorem norm_intervalIntegral_classMoment_rightTail_q99_lt_one_div_ten_pow_40
    (n : ℕ) :
    ‖∫ x in (99 / 100 : ℝ)..1, classMomentIntegrand n x‖ <
      (1 / 10 ^ 40 : ℝ) := by
  exact lt_of_le_of_lt
    (norm_intervalIntegral_classMoment_rightTail_le n
      (r := (99 / 100 : ℝ)) (by norm_num) (by norm_num))
    q99_tail_constant_lt_one_div_ten_pow_40

theorem norm_intervalIntegral_classMoment_leftTail_q99_lt_one_div_ten_pow_40
    (n : ℕ) :
    ‖∫ x in (-1 : ℝ)..(-(99 / 100 : ℝ)), classMomentIntegrand n x‖ <
      (1 / 10 ^ 40 : ℝ) := by
  exact lt_of_le_of_lt
    (norm_intervalIntegral_classMoment_leftTail_le n
      (r := (99 / 100 : ℝ)) (by norm_num) (by norm_num))
    q99_tail_constant_lt_one_div_ten_pow_40

/-! ## Sign-sensitive even-moment assembly -/

theorem classMomentIntegrand_nonneg_of_even {n : ℕ} (hn : Even n) (x : ℝ) :
    0 ≤ classMomentIntegrand n x := by
  unfold classMomentIntegrand
  exact mul_nonneg (Even.pow_nonneg hn x) (classUnitWeight_nonneg x)

theorem classMoment_rightTail_nonneg_of_even {n : ℕ} (hn : Even n) :
    0 ≤ ∫ x in centralRadius..1, classMomentIntegrand n x := by
  apply intervalIntegral.integral_nonneg_of_forall
  · unfold centralRadius
    norm_num
  · intro x
    exact classMomentIntegrand_nonneg_of_even hn x

/-! ## Sharp central-to-whole-line transport -/

/-- A central envelope for an even moment transports to a lower bound with no
tail loss and an upper bound paying twice `10 ^ (-40)`. -/
theorem classMoment_bounds_of_centralEnvelope_of_even_sharp
    {n : ℕ} (hn : Even n) {lo hi : ℝ}
    (h : centralMomentEnvelope n lo hi) :
    lo ≤ classMoment n ∧
      classMoment n < hi + (2 / 10 ^ 40 : ℝ) := by
  have hcentral :
      lo ≤ (∫ x in (-centralRadius)..centralRadius,
        classMomentIntegrand n x) ∧
        (∫ x in (-centralRadius)..centralRadius,
          classMomentIntegrand n x) ≤ hi := by
    simpa [centralMoment] using
      (centralMoment_bounds_of_centralEnvelope n lo hi h)
  have htailAbs :
      |∫ x in centralRadius..1, classMomentIntegrand n x| <
        (1 / 10 ^ 40 : ℝ) := by
    simpa [centralRadius, Real.norm_eq_abs] using
      (norm_intervalIntegral_classMoment_rightTail_q99_lt_one_div_ten_pow_40 n)
  have htailUpper := (abs_lt.mp htailAbs).2
  have htailNonneg := classMoment_rightTail_nonneg_of_even hn
  rw [classMoment_eq_three_interval n,
    classMoment_leftTail_eq_rightTail_of_even hn]
  constructor <;> linarith [hcentral.1, hcentral.2, htailUpper, htailNonneg]

/-! ## q28-facing central sockets -/

theorem q28Moment0_bounds_of_centralEnvelope
    (h : centralMomentEnvelope 0 q28Moment0Lo
      (q28Moment0Hi - (2 / 10 ^ 40 : ℝ))) :
    q28Moment0Lo ≤ classMoment 0 ∧ classMoment 0 ≤ q28Moment0Hi := by
  have hfull := classMoment_bounds_of_centralEnvelope_of_even_sharp
    (n := 0) (lo := q28Moment0Lo)
    (hi := q28Moment0Hi - (2 / 10 ^ 40 : ℝ))
    ⟨0, rfl⟩ h
  constructor
  · exact hfull.1
  · linarith [hfull.2]

theorem q28Moment2_bounds_of_centralEnvelope
    (h : centralMomentEnvelope 2 q28Moment2Lo
      (q28Moment2Hi - (2 / 10 ^ 40 : ℝ))) :
    q28Moment2Lo ≤ classMoment 2 ∧ classMoment 2 ≤ q28Moment2Hi := by
  have hfull := classMoment_bounds_of_centralEnvelope_of_even_sharp
    (n := 2) (lo := q28Moment2Lo)
    (hi := q28Moment2Hi - (2 / 10 ^ 40 : ℝ))
    ⟨1, by norm_num⟩ h
  constructor
  · exact hfull.1
  · linarith [hfull.2]

theorem q28_baseMoment_bounds_of_centralEnvelopes
    (h0 : centralMomentEnvelope 0 q28Moment0Lo
      (q28Moment0Hi - (2 / 10 ^ 40 : ℝ)))
    (h2 : centralMomentEnvelope 2 q28Moment2Lo
      (q28Moment2Hi - (2 / 10 ^ 40 : ℝ))) :
    (q28Moment0Lo ≤ classMoment 0 ∧ classMoment 0 ≤ q28Moment0Hi) ∧
      (q28Moment2Lo ≤ classMoment 2 ∧ classMoment 2 ≤ q28Moment2Hi) :=
  ⟨q28Moment0_bounds_of_centralEnvelope h0,
    q28Moment2_bounds_of_centralEnvelope h2⟩

/-! ## Symbolic fidelity -/

example :
    0 ≤ classMoment 0 ∧
      classMoment 0 < 2 + (2 / 10 ^ 40 : ℝ) := by
  simpa using
    (classMoment_bounds_of_centralEnvelope_of_even_sharp
      (n := 0) (lo := 0) (hi := 2) ⟨0, rfl⟩ symbolicCentralEnvelopeZero)

end
end C1ClassMomentSharpTailBudget
end Source
end ConnesWeilRH
