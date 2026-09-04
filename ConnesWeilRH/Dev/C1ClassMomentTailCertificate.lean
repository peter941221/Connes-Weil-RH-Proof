/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1ClassMomentPolynomialIntegral
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Record 1134: exponential endpoint tails for class moments

This file proves the exact exponential form of the squared class bump and
uses it to bound both endpoint tails of every class moment.  The concrete
`99 / 100` tail estimate is reduced to rational arithmetic plus an explicit
Taylor bound for `exp (-1)`.  It is a reduction of the true moment certificate
to a central interval; no Hbox or RH conclusion is asserted.
-/

namespace ConnesWeilRH
namespace Source
namespace C1ClassMomentTailCertificate

open MeasureTheory Set
open C1ClassWindowObjects
open C1ClassGramMomentReduction
open C1ClassMomentIntegralCertificate
open scoped BigOperators Interval

noncomputable section

/-! ## Exact interior form and pointwise tail bound -/

/-- The squared class bump has the expected exponential form in the open
interval. -/
theorem classUnitWeight_eq_exp_neg_two_div {x : ℝ} (hx : |x| < 1) :
    classUnitWeight x = Real.exp (-(2 / (1 - x ^ 2))) := by
  rw [classUnitWeight, classBump_eq_exp hx,
    ← Real.exp_add]
  congr 1
  ring

theorem classUnitWeight_nonneg (x : ℝ) : 0 ≤ classUnitWeight x := by
  unfold classUnitWeight
  exact mul_self_nonneg _

/-- On an endpoint annulus the class weight is bounded by its value at the
inner radius. -/
theorem classUnitWeight_le_exp_of_abs_bounds
    {r x : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hxr : r ≤ |x|) (hx1 : |x| ≤ 1) :
    classUnitWeight x ≤ Real.exp (-(2 / (1 - r ^ 2))) := by
  by_cases hboundary : |x| = (1 : ℝ)
  · have hzero : classBump x = 0 :=
      classBump_eq_zero (le_of_eq hboundary.symm)
    simpa [classUnitWeight, hzero] using
      (Real.exp_nonneg (-(2 / (1 - r ^ 2))))
  have hlt : |x| < (1 : ℝ) := lt_of_le_of_ne hx1 hboundary
  have hsqabs : r ^ 2 ≤ |x| ^ 2 := by
    have hprod : 0 ≤ (|x| - r) * (|x| + r) := by
      exact mul_nonneg (sub_nonneg.mpr hxr) (by positivity)
    nlinarith
  have hsq : r ^ 2 ≤ x ^ 2 := by
    simpa only [sq_abs] using hsqabs
  have hrden : 0 < 1 - r ^ 2 := by
    have hprod : 0 < (1 - r) * (1 + r) := by
      exact mul_pos (sub_pos.mpr hr1) (by linarith)
    nlinarith
  have hxden : 0 < 1 - x ^ 2 := by
    have hprod : 0 < (1 - |x|) * (1 + |x|) := by
      exact mul_pos (sub_pos.mpr hlt) (by linarith [abs_nonneg x])
    nlinarith [hprod, sq_abs x]
  have hfrac : (2 : ℝ) / (1 - r ^ 2) ≤ 2 / (1 - x ^ 2) := by
    apply (div_le_div_iff₀ hrden hxden).2
    nlinarith [hsq]
  rw [classUnitWeight_eq_exp_neg_two_div hlt]
  exact Real.exp_le_exp.mpr (by linarith [hfrac])

/-- The polynomial factor `x^n` does not enlarge the endpoint weight on
`[-1,1]`. -/
theorem classMomentIntegrand_norm_le_exp_of_abs_bounds
    (n : ℕ) {r x : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hxr : r ≤ |x|) (hx1 : |x| ≤ 1) :
    ‖classMomentIntegrand n x‖ ≤ Real.exp (-(2 / (1 - r ^ 2))) := by
  have hweight : 0 ≤ classUnitWeight x := classUnitWeight_nonneg x
  have hpow : |x| ^ n ≤ 1 := pow_le_one₀ (abs_nonneg x) hx1
  have habs : |x ^ n * classUnitWeight x| ≤
      Real.exp (-(2 / (1 - r ^ 2))) := by
    rw [abs_mul, abs_pow, abs_of_nonneg hweight]
    calc
      |x| ^ n * classUnitWeight x ≤ 1 * classUnitWeight x :=
        mul_le_mul_of_nonneg_right hpow hweight
      _ ≤ 1 * Real.exp (-(2 / (1 - r ^ 2))) :=
        mul_le_mul_of_nonneg_left
          (classUnitWeight_le_exp_of_abs_bounds hr0 hr1 hxr hx1) (by norm_num)
      _ = Real.exp (-(2 / (1 - r ^ 2))) := by rw [one_mul]
  simpa [classMomentIntegrand, Real.norm_eq_abs] using habs

/-! ## Interval-integral tails -/

theorem norm_intervalIntegral_classMoment_rightTail_le
    (n : ℕ) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ‖∫ x in r..1, classMomentIntegrand n x‖ ≤
      (1 - r) * Real.exp (-(2 / (1 - r ^ 2))) := by
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := classMomentIntegrand n) (a := r) (b := 1)
    (C := Real.exp (-(2 / (1 - r ^ 2)))) (by
      intro x hx
      rw [uIoc_of_le (le_of_lt hr1)] at hx
      have hxnonneg : 0 ≤ x := by linarith [hr0, hx.1]
      have hxr : r ≤ |x| := by
        simpa [abs_of_nonneg hxnonneg] using (le_of_lt hx.1)
      have hx1 : |x| ≤ 1 := by
        simpa [abs_of_nonneg hxnonneg] using hx.2
      simpa [Real.norm_eq_abs] using
        classMomentIntegrand_norm_le_exp_of_abs_bounds n hr0 hr1 hxr hx1)
  calc
    ‖∫ x in r..1, classMomentIntegrand n x‖ ≤
        Real.exp (-(2 / (1 - r ^ 2))) * |1 - r| := hnorm
    _ = (1 - r) * Real.exp (-(2 / (1 - r ^ 2))) := by
      rw [abs_of_nonneg (by linarith)]
      ring

theorem norm_intervalIntegral_classMoment_leftTail_le
    (n : ℕ) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ‖∫ x in (-1 : ℝ)..(-r), classMomentIntegrand n x‖ ≤
      (1 - r) * Real.exp (-(2 / (1 - r ^ 2))) := by
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := classMomentIntegrand n) (a := (-1 : ℝ)) (b := -r)
    (C := Real.exp (-(2 / (1 - r ^ 2)))) (by
      intro x hx
      have hab : (-1 : ℝ) ≤ -r := by linarith [hr1]
      rw [uIoc_of_le hab] at hx
      have hxnonpos : x ≤ 0 := by linarith [hx.2, hr0]
      have hxr : r ≤ |x| := by
        rw [abs_of_nonpos hxnonpos]
        linarith [hx.2]
      have hx1 : |x| ≤ 1 := by
        rw [abs_of_nonpos hxnonpos]
        linarith [hx.1]
      simpa [Real.norm_eq_abs] using
        classMomentIntegrand_norm_le_exp_of_abs_bounds n hr0 hr1 hxr hx1)
  calc
    ‖∫ x in (-1 : ℝ)..(-r), classMomentIntegrand n x‖ ≤
        Real.exp (-(2 / (1 - r ^ 2))) * |(-r) - (-1)| := hnorm
    _ = (1 - r) * Real.exp (-(2 / (1 - r ^ 2))) := by
      have harg : (-r : ℝ) - (-1) = 1 - r := by ring
      rw [harg, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - r)]
      ring

/-! ## A concrete rational tail radius -/

private lemma exp_neg_one_lt_three_eighths : Real.exp (-1) < (3 / 8 : ℝ) := by
  have h := Real.exp_bound (x := (-1 : ℝ))
    (by norm_num) (n := 7) (by norm_num)
  have hup := (abs_sub_le_iff.mp h).1
  norm_num [Finset.sum_range_succ] at hup
  nlinarith

private lemma exp_neg_nat_eq_pow (n : ℕ) :
    Real.exp (-(n : ℝ)) = Real.exp (-1) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.cast_succ]
      have harg : -((n : ℝ) + 1) = -(n : ℝ) + (-1 : ℝ) := by ring
      rw [harg, Real.exp_add, ih, pow_succ]

private lemma q99_tail_constant_lt :
    (1 - (99 / 100 : ℝ)) *
        Real.exp (-(2 / (1 - (99 / 100 : ℝ) ^ 2))) <
      (1 / 10 ^ 15 : ℝ) := by
  have hq : (100 : ℝ) ≤ 2 / (1 - (99 / 100 : ℝ) ^ 2) := by
    norm_num
  have hexp : Real.exp (-(2 / (1 - (99 / 100 : ℝ) ^ 2))) ≤
      Real.exp (-100) := by
    apply Real.exp_le_exp.mpr
    linarith
  have hpowid : Real.exp (-100) = Real.exp (-1) ^ 100 := by
    exact exp_neg_nat_eq_pow 100
  have hpow : Real.exp (-100) < (3 / 8 : ℝ) ^ 100 := by
    rw [hpowid]
    exact pow_lt_pow_left₀ exp_neg_one_lt_three_eighths
      (Real.exp_pos (-1)).le (by norm_num)
  calc
    (1 - (99 / 100 : ℝ)) *
          Real.exp (-(2 / (1 - (99 / 100 : ℝ) ^ 2))) ≤
        (1 - (99 / 100 : ℝ)) * Real.exp (-100) := by
      exact mul_le_mul_of_nonneg_left hexp (by norm_num)
    _ < (1 - (99 / 100 : ℝ)) * (3 / 8 : ℝ) ^ 100 := by
      gcongr
    _ < (1 / 10 ^ 15 : ℝ) := by norm_num

theorem norm_intervalIntegral_classMoment_rightTail_q99_lt (n : ℕ) :
    ‖∫ x in (99 / 100 : ℝ)..1, classMomentIntegrand n x‖ <
      (1 / 10 ^ 15 : ℝ) := by
  exact lt_of_le_of_lt
    (norm_intervalIntegral_classMoment_rightTail_le n (by norm_num) (by norm_num))
    q99_tail_constant_lt

theorem norm_intervalIntegral_classMoment_leftTail_q99_lt (n : ℕ) :
    ‖∫ x in (-1 : ℝ)..(-(99 / 100 : ℝ)), classMomentIntegrand n x‖ <
      (1 / 10 ^ 15 : ℝ) := by
  exact lt_of_le_of_lt
    (norm_intervalIntegral_classMoment_leftTail_le n (by norm_num) (by norm_num))
    q99_tail_constant_lt

end
end C1ClassMomentTailCertificate
end Source
end ConnesWeilRH
