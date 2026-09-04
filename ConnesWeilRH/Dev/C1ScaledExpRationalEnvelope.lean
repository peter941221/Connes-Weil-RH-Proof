/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1ClassMomentSharpTailBudget
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Record 1137: scaled exponential rational envelope

On the central interval `|x| <= 97/100`, the exponent
`2 / (1 - x^2)` is at most `34`, so it can be divided by `35` before applying
the unit-radius Taylor remainder for the exponential.  The resulting degree-
19 Taylor polynomial is raised to the exact power `35`; this gives a rational
function in `(1 - x^2)⁻¹` and an explicit pointwise error.  No integral value
is supplied here.  RH is NOT claimed.
-/

namespace ConnesWeilRH
namespace Source
namespace C1ScaledExpRationalEnvelope

open MeasureTheory Set
open C1ClassWindowObjects
open C1ClassGramMomentReduction
open C1ClassMomentIntegralCertificate
open C1ClassMomentTailCertificate
open C1ClassMomentCentralAssembly
open scoped BigOperators Interval

noncomputable section

/-! ## The scaled Taylor polynomial -/

def expTaylor20 (z : ℝ) : ℝ :=
  ∑ k ∈ Finset.range 20, (-z) ^ k / (k.factorial : ℝ)

def expTaylor20Error : ℝ :=
  (21 : ℝ) / (((Nat.factorial 20 : ℕ) : ℝ) * 20)

def scaledClassWeightApprox (x : ℝ) : ℝ :=
  expTaylor20 ((2 / 35 : ℝ) / (1 - x ^ 2)) ^ 35

theorem expTaylor20_eq_range (z : ℝ) :
    expTaylor20 z =
      ∑ k ∈ Finset.range 20, (-z) ^ k / (k.factorial : ℝ) :=
  rfl

/-! ## Unit-range bounds for the Taylor polynomial -/

private theorem exp_neg_one_gt_one_third :
    (1 / 3 : ℝ) < Real.exp (-1) := by
  have h := Real.exp_bound (x := (-1 : ℝ))
    (by norm_num) (n := 7) (by norm_num)
  have hlo := (abs_sub_le_iff.mp h).2
  norm_num [Finset.sum_range_succ] at hlo
  nlinarith

theorem expTaylor20_error (z : ℝ) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
      |Real.exp (-z) - expTaylor20 z| ≤ expTaylor20Error := by
  have h := Real.exp_bound (x := -z)
    (by
      have hzabs : |(-z : ℝ)| = z := by
        rw [abs_of_nonpos (by linarith), neg_neg]
      rw [hzabs]
      exact hz1)
    (n := 20) (by norm_num)
  have hpow : |z| ^ 20 ≤ (1 : ℝ) := by
    simpa [abs_of_nonneg hz0] using pow_le_one₀ hz0 hz1
  have hfactor :
      |z| ^ 20 *
        ((↑(Nat.succ 20) : ℝ) /
            (((Nat.factorial 20 : ℕ) : ℝ) * 20)) ≤
        expTaylor20Error := by
    dsimp [expTaylor20Error]
    calc
      |z| ^ 20 *
          ((↑(Nat.succ 20) : ℝ) /
            (((Nat.factorial 20 : ℕ) : ℝ) * 20)) ≤
          1 * ((↑(Nat.succ 20) : ℝ) /
            (((Nat.factorial 20 : ℕ) : ℝ) * 20)) := by
        exact mul_le_mul_of_nonneg_right hpow (by positivity)
      _ = (21 : ℝ) / (((Nat.factorial 20 : ℕ) : ℝ) * 20) := by norm_num
  have hfactor' :
      |(-z : ℝ)| ^ 20 *
          ((↑(Nat.succ 20) : ℝ) /
            (((Nat.factorial 20 : ℕ) : ℝ) * ((20 : ℕ) : ℝ))) ≤
        expTaylor20Error := by
    convert hfactor using 1 <;> norm_num [abs_neg]
  simpa [expTaylor20] using h.trans hfactor'

theorem expTaylor20_nonneg (z : ℝ) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    0 ≤ expTaylor20 z := by
  have herror := expTaylor20_error z hz0 hz1
  have hmono : Real.exp (-1) ≤ Real.exp (-z) := by
    apply Real.exp_le_exp.mpr
    linarith
  have hexp : (1 / 3 : ℝ) < Real.exp (-z) :=
    lt_of_lt_of_le exp_neg_one_gt_one_third hmono
  have herr : expTaylor20Error < (1 / 3 : ℝ) := by
    norm_num [expTaylor20Error]
  have hlow := (abs_le.mp herror).2
  linarith

theorem expTaylor20_le_one_add_error (z : ℝ) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    expTaylor20 z ≤ 1 + expTaylor20Error := by
  have herror := expTaylor20_error z hz0 hz1
  have hexp : Real.exp (-z) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  have hupp := (abs_le.mp herror).1
  linarith

/-! ## A finite power-difference estimate -/

private theorem pow35_sub_factor (a b : ℝ) :
    a ^ 35 - b ^ 35 =
      (a - b) * ∑ k ∈ Finset.range 35, a ^ (34 - k) * b ^ k := by
  have h := geom_sum₂_mul b a 35
  have hsum :
      (∑ k ∈ Finset.range 35, b ^ k * a ^ (34 - k)) =
        ∑ k ∈ Finset.range 35, a ^ (34 - k) * b ^ k := by
    apply Finset.sum_congr rfl
    intro k hk
    ring
  calc
    a ^ 35 - b ^ 35 = -(b ^ 35 - a ^ 35) := by ring
    _ = -((∑ k ∈ Finset.range 35, b ^ k * a ^ (34 - k)) * (b - a)) := by
      rw [h]
    _ = (a - b) * ∑ k ∈ Finset.range 35, a ^ (34 - k) * b ^ k := by
      rw [← hsum]
      ring

private theorem pow_le_two_of_le_one_add_error
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1 + expTaylor20Error) :
    ∀ k : ℕ, k ≤ 34 → p ^ k ≤ 2 := by
  intro k hk
  have hp : p ≤ (101 / 100 : ℝ) := by
    calc
      p ≤ 1 + expTaylor20Error := hp1
      _ ≤ 101 / 100 := by norm_num [expTaylor20Error]
  have hpow : p ^ k ≤ (101 / 100 : ℝ) ^ k :=
    pow_le_pow_left₀ hp0 hp k
  have hgeom : (101 / 100 : ℝ) ^ k ≤ (101 / 100 : ℝ) ^ 34 :=
    pow_le_pow_right₀ (by norm_num) hk
  have h34 : (101 / 100 : ℝ) ^ 34 ≤ 2 := by norm_num
  exact hpow.trans (hgeom.trans h34)

theorem expTaylor20_pow35_error (z : ℝ) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    |Real.exp (-z) ^ 35 - expTaylor20 z ^ 35| ≤
      (70 : ℝ) * expTaylor20Error := by
  have ha0 : 0 ≤ Real.exp (-z) := (Real.exp_pos _).le
  have ha1 : Real.exp (-z) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  have hb0 := expTaylor20_nonneg z hz0 hz1
  have hb1 := expTaylor20_le_one_add_error z hz0 hz1
  have hpow := pow35_sub_factor (Real.exp (-z)) (expTaylor20 z)
  rw [hpow]
  rw [abs_mul]
  have hdiff := expTaylor20_error z hz0 hz1
  have hsum :
      |∑ k ∈ Finset.range 35,
          Real.exp (-z) ^ (34 - k) * expTaylor20 z ^ k| ≤ 70 := by
    calc
      |∑ k ∈ Finset.range 35,
          Real.exp (-z) ^ (34 - k) * expTaylor20 z ^ k| ≤
          ∑ k ∈ Finset.range 35,
            |Real.exp (-z) ^ (34 - k) * expTaylor20 z ^ k| :=
        by
          simpa only [Real.norm_eq_abs] using
            (norm_sum_le (s := Finset.range 35)
              (f := fun k : ℕ =>
                Real.exp (-z) ^ (34 - k) * expTaylor20 z ^ k))
      _ = ∑ k ∈ Finset.range 35,
          Real.exp (-z) ^ (34 - k) * expTaylor20 z ^ k := by
        simp only [abs_mul, abs_pow, abs_of_nonneg ha0, abs_of_nonneg hb0]
      _ ≤ ∑ _k ∈ Finset.range 35, (2 : ℝ) := by
        apply Finset.sum_le_sum
        intro k hk
        have hkpow := pow_le_two_of_le_one_add_error hb0 hb1 k
          (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
        have hapow : Real.exp (-z) ^ (34 - k) ≤ 1 :=
          pow_le_one₀ (Real.exp_nonneg _) ha1
        have hapow0 : 0 ≤ Real.exp (-z) ^ (34 - k) := by positivity
        calc
          Real.exp (-z) ^ (34 - k) * expTaylor20 z ^ k ≤
              1 * expTaylor20 z ^ k :=
            mul_le_mul_of_nonneg_right hapow (by positivity)
          _ ≤ 1 * 2 :=
            mul_le_mul_of_nonneg_left hkpow (by positivity)
          _ = 2 := by norm_num
      _ = 70 := by norm_num
  calc
    |Real.exp (-z) - expTaylor20 z| *
          |∑ k ∈ Finset.range 35,
            Real.exp (-z) ^ (34 - k) * expTaylor20 z ^ k| ≤
        expTaylor20Error *
          |∑ k ∈ Finset.range 35,
            Real.exp (-z) ^ (34 - k) * expTaylor20 z ^ k| :=
      mul_le_mul_of_nonneg_right hdiff (abs_nonneg _)
    _ ≤ expTaylor20Error * 70 :=
      mul_le_mul_of_nonneg_left hsum (by norm_num [expTaylor20Error])
    _ = 70 * expTaylor20Error := by ring

/-! ## Central-interval scaling and the actual class weight -/

theorem centralRadius97_abs_sq_lt_one (x : ℝ)
    (hx : x ∈ Icc (-(97 / 100 : ℝ)) (97 / 100 : ℝ)) :
    x ^ 2 < 1 := by
  rcases hx with ⟨hlo, hhi⟩
  nlinarith

theorem centralRadius97_scaled_argument_bounds (x : ℝ)
    (hx : x ∈ Icc (-(97 / 100 : ℝ)) (97 / 100 : ℝ)) :
    0 ≤ (2 / 35 : ℝ) / (1 - x ^ 2) ∧
      (2 / 35 : ℝ) / (1 - x ^ 2) ≤ 1 := by
  have hsq := centralRadius97_abs_sq_lt_one x hx
  have hden : 0 < 1 - x ^ 2 := by linarith
  constructor
  · positivity
  · have hbound : x ^ 2 ≤ (97 / 100 : ℝ) ^ 2 := by
      rcases hx with ⟨hlo, hhi⟩
      nlinarith
    apply (div_le_iff₀ hden).2
    nlinarith

private theorem exp_neg_nat_eq_pow_scaled (x : ℝ) (n : ℕ) :
    Real.exp (-(n : ℝ) * x) = Real.exp (-x) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.cast_succ]
      have harg : -((n : ℝ) + 1) * x = -(n : ℝ) * x + (-x) := by ring
      rw [harg, Real.exp_add, ih, pow_succ]

theorem classUnitWeight_eq_scaled_power_approximation (x : ℝ)
    (hx : x ∈ Icc (-(97 / 100 : ℝ)) (97 / 100 : ℝ)) :
    classUnitWeight x =
      Real.exp (-((2 / 35 : ℝ) / (1 - x ^ 2))) ^ 35 := by
  have hsq := centralRadius97_abs_sq_lt_one x hx
  have habs : |x| < 1 := by
    rw [abs_lt]
    rcases hx with ⟨hlo, hhi⟩
    constructor <;> linarith
  rw [classUnitWeight_eq_exp_neg_two_div habs]
  have harg :
      -(2 / (1 - x ^ 2) : ℝ) =
        -(35 : ℝ) * ((2 / 35 : ℝ) / (1 - x ^ 2)) := by
    field_simp [ne_of_gt (by linarith : (0 : ℝ) < 1 - x ^ 2)]
  rw [harg]
  simpa [mul_comm] using
    (exp_neg_nat_eq_pow_scaled ((2 / 35 : ℝ) / (1 - x ^ 2)) 35)

theorem classUnitWeight_central_approx_error (x : ℝ)
    (hx : x ∈ Icc (-(97 / 100 : ℝ)) (97 / 100 : ℝ)) :
    |classUnitWeight x - scaledClassWeightApprox x| ≤
      (70 : ℝ) * expTaylor20Error := by
  have hz := centralRadius97_scaled_argument_bounds x hx
  rw [classUnitWeight_eq_scaled_power_approximation x hx]
  exact expTaylor20_pow35_error _ hz.1 hz.2

theorem classMomentIntegrand_central_approx_error (n : ℕ) (x : ℝ)
    (hx : x ∈ Icc (-(97 / 100 : ℝ)) (97 / 100 : ℝ)) :
    |classMomentIntegrand n x -
        x ^ n * scaledClassWeightApprox x| ≤
      (70 : ℝ) * expTaylor20Error := by
  have hweight := classUnitWeight_nonneg x
  have hpow : |x| ^ n ≤ 1 := by
    rcases hx with ⟨hlo, hhi⟩
    have habs : |x| ≤ (1 : ℝ) := by
      rw [abs_le]
      constructor <;> linarith
    exact pow_le_one₀ (abs_nonneg x) habs
  rw [classMomentIntegrand, scaledClassWeightApprox]
  rw [← mul_sub]
  rw [abs_mul, abs_pow]
  calc
    |x| ^ n * |classUnitWeight x - scaledClassWeightApprox x| ≤
        1 * |classUnitWeight x - scaledClassWeightApprox x| :=
      mul_le_mul_of_nonneg_right hpow (abs_nonneg _)
    _ = |classUnitWeight x - scaledClassWeightApprox x| := by rw [one_mul]
    _ ≤ (70 : ℝ) * expTaylor20Error :=
      classUnitWeight_central_approx_error x hx

end
end C1ScaledExpRationalEnvelope
end Source
end ConnesWeilRH
