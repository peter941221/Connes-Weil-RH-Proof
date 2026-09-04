/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1ClassGramMomentReduction
import ConnesWeilRH.Dev.C1ClassGramScale
import Mathlib.Algebra.Polynomial.Degree.Support

/-!
# Record 1130: polynomial-to-moment consumption for the class Gram owner

The unit-scale class Gram entries are integrals of products of the first
eight Legendre polynomials against the actual weight
`classUnitWeight = classBump ^ 2`.  This module exposes that integral as an
exact finite sum of the moments from record 1129.  It is the algebraic
consumer needed before a true interval certificate for the two base moments
can close the q28 Gram box.

No numerical interval is assumed here.  RH is NOT claimed.
-/

namespace ConnesWeilRH
namespace Source
namespace C1ClassGramMomentConsumer

open MeasureTheory
open C1ClassWindowObjects
open C1ClassGramOwner
open C1ClassGramScale
open C1ClassGramMomentReduction
open Polynomial
open scoped BigOperators

noncomputable section

/-! ## Polynomial integration against the actual class weight -/

/-- The weighted integral of a real polynomial against the actual unit
class-window weight. -/
noncomputable def classWeightedPolyIntegral (p : ℝ[X]) : ℝ :=
  ∫ x : ℝ, eval x p * classUnitWeight x

/-- Polynomial evaluation against the class weight is integrable. -/
theorem classWeightedPolyIntegral_integrable (p : ℝ[X]) :
    Integrable (fun x : ℝ => eval x p * classUnitWeight x) := by
  have hcont : Continuous (fun x : ℝ => eval x p * classUnitWeight x) :=
    p.continuous.mul classUnitWeight_contDiff.continuous
  have hcompact : HasCompactSupport
      (fun x : ℝ => eval x p * classUnitWeight x) := by
    exact classUnitWeight_hasCompactSupport.mul_left
  exact hcont.integrable_of_hasCompactSupport hcompact

/-- Exact finite moment expansion of a polynomial weighted integral. -/
theorem classWeightedPolyIntegral_eq_moment_sum (p : ℝ[X]) :
    classWeightedPolyIntegral p =
      ∑ n ∈ p.support, p.coeff n * classMoment n := by
  have hp : p = ∑ n ∈ p.support, C (p.coeff n) * X ^ n :=
    p.as_sum_support_C_mul_X_pow
  calc
    classWeightedPolyIntegral p =
        ∫ x : ℝ, eval x (∑ n ∈ p.support, C (p.coeff n) * X ^ n) *
          classUnitWeight x := by
      unfold classWeightedPolyIntegral
      congr 1
      funext x
      rw [← hp]
    _ = ∫ x : ℝ, ∑ n ∈ p.support,
          p.coeff n * (x ^ n * classUnitWeight x) := by
      congr 1
      funext x
      rw [Polynomial.eval_finsetSum, Finset.sum_mul]
      refine Finset.sum_congr rfl ?_
      intro n hn
      simp [Polynomial.eval_mul]
      ring
    _ = ∑ n ∈ p.support, p.coeff n * classMoment n := by
      rw [MeasureTheory.integral_finsetSum]
      · refine Finset.sum_congr rfl ?_
        intro n hn
        rw [MeasureTheory.integral_const_mul]
        rfl
      · intro n hn
        exact (classMoment_integrable n).const_mul' (p.coeff n)

theorem classWeightedPolyIntegral_add (p q : ℝ[X]) :
    classWeightedPolyIntegral (p + q) =
      classWeightedPolyIntegral p + classWeightedPolyIntegral q := by
  calc
    classWeightedPolyIntegral (p + q) =
        ∫ x : ℝ, (eval x p * classUnitWeight x) +
          (eval x q * classUnitWeight x) := by
      unfold classWeightedPolyIntegral
      congr 1
      funext x
      simp [Polynomial.eval_add, add_mul]
    _ = classWeightedPolyIntegral p + classWeightedPolyIntegral q := by
      rw [integral_add (classWeightedPolyIntegral_integrable p)
        (classWeightedPolyIntegral_integrable q)]
      rfl

theorem classWeightedPolyIntegral_sub (p q : ℝ[X]) :
    classWeightedPolyIntegral (p - q) =
      classWeightedPolyIntegral p - classWeightedPolyIntegral q := by
  calc
    classWeightedPolyIntegral (p - q) =
        ∫ x : ℝ, (eval x p * classUnitWeight x) -
          (eval x q * classUnitWeight x) := by
      unfold classWeightedPolyIntegral
      congr 1
      funext x
      simp [Polynomial.eval_sub, sub_mul]
    _ = classWeightedPolyIntegral p - classWeightedPolyIntegral q := by
      rw [integral_sub (classWeightedPolyIntegral_integrable p)
        (classWeightedPolyIntegral_integrable q)]
      rfl

theorem classWeightedPolyIntegral_C_mul (c : ℝ) (p : ℝ[X]) :
    classWeightedPolyIntegral (C c * p) =
      c * classWeightedPolyIntegral p := by
  calc
    classWeightedPolyIntegral (C c * p) =
        ∫ x : ℝ, c * (eval x p * classUnitWeight x) := by
      unfold classWeightedPolyIntegral
      congr 1
      funext x
      simp [Polynomial.eval_mul]
      ring
    _ = c * classWeightedPolyIntegral p := by
      rw [integral_const_mul]
      rfl

theorem classWeightedPolyIntegral_mul_C (p : ℝ[X]) (c : ℝ) :
    classWeightedPolyIntegral (p * C c) =
      c * classWeightedPolyIntegral p := by
  calc
    classWeightedPolyIntegral (p * C c) =
        ∫ x : ℝ, c * (eval x p * classUnitWeight x) := by
      unfold classWeightedPolyIntegral
      congr 1
      funext x
      simp [Polynomial.eval_mul]
      ring
    _ = c * classWeightedPolyIntegral p := by
      rw [integral_const_mul]
      rfl

theorem classWeightedPolyIntegral_mul_nat (p : ℝ[X]) (n : ℕ) :
    classWeightedPolyIntegral (p * (n : ℝ[X])) =
      (n : ℝ) * classWeightedPolyIntegral p := by
  have hn : (n : ℝ[X]) = C (n : ℝ) := by
    norm_num
  rw [hn]
  exact classWeightedPolyIntegral_mul_C p (n : ℝ)

theorem classWeightedPolyIntegral_smul (c : ℝ) (p : ℝ[X]) :
    classWeightedPolyIntegral (c • p) =
      c * classWeightedPolyIntegral p := by
  rw [Polynomial.smul_eq_C_mul]
  exact classWeightedPolyIntegral_C_mul c p

theorem classWeightedPolyIntegral_monomial (c : ℝ) (n : ℕ) :
    classWeightedPolyIntegral (C c * X ^ n) = c * classMoment n := by
  rw [classWeightedPolyIntegral_C_mul]
  unfold classWeightedPolyIntegral classMoment
  simp

@[simp] theorem classWeightedPolyIntegral_X_pow (n : ℕ) :
    classWeightedPolyIntegral (X ^ n) = classMoment n := by
  simpa using classWeightedPolyIntegral_monomial (1 : ℝ) n

@[simp] theorem classWeightedPolyIntegral_X_mul_X_pow (n : ℕ) :
    classWeightedPolyIntegral ((X : ℝ[X]) * X ^ n) = classMoment (n + 1) := by
  have hpoly : (X : ℝ[X]) * X ^ n = X ^ (n + 1) := by
    rw [pow_succ]
    ring
  rw [hpoly]
  exact classWeightedPolyIntegral_X_pow (n + 1)

theorem classWeightedPolyIntegral_X_mul_add (p q : ℝ[X]) :
    classWeightedPolyIntegral (X * (p + q)) =
      classWeightedPolyIntegral (X * p) + classWeightedPolyIntegral (X * q) := by
  calc
    classWeightedPolyIntegral (X * (p + q)) =
        classWeightedPolyIntegral (X * p + X * q) := by
      congr 1
      ring
    _ = classWeightedPolyIntegral (X * p) + classWeightedPolyIntegral (X * q) :=
      classWeightedPolyIntegral_add _ _

theorem classWeightedPolyIntegral_X_mul_sub (p q : ℝ[X]) :
    classWeightedPolyIntegral (X * (p - q)) =
      classWeightedPolyIntegral (X * p) - classWeightedPolyIntegral (X * q) := by
  calc
    classWeightedPolyIntegral (X * (p - q)) =
        classWeightedPolyIntegral (X * p - X * q) := by
      congr 1
      ring
    _ = classWeightedPolyIntegral (X * p) - classWeightedPolyIntegral (X * q) :=
      classWeightedPolyIntegral_sub _ _

theorem classWeightedPolyIntegral_X_mul_C_mul (c : ℝ) (p : ℝ[X]) :
    classWeightedPolyIntegral (X * (C c * p)) =
      c * classWeightedPolyIntegral (X * p) := by
  calc
    classWeightedPolyIntegral (X * (C c * p)) =
        classWeightedPolyIntegral (C c * (X * p)) := by
      congr 1
      ring
    _ = c * classWeightedPolyIntegral (X * p) :=
      classWeightedPolyIntegral_C_mul c (X * p)

@[simp] theorem classWeightedPolyIntegral_X_mul_C (c : ℝ) :
    classWeightedPolyIntegral (X * C c) = c * classMoment 1 := by
  calc
    classWeightedPolyIntegral (X * C c) =
        classWeightedPolyIntegral (C c * X) := by
      congr 1
      ring
    _ = c * classWeightedPolyIntegral X :=
      classWeightedPolyIntegral_C_mul c X
    _ = c * classMoment 1 := by
      congr 1
      simpa using classWeightedPolyIntegral_X_pow 1

@[simp] theorem classPolynomial_X_mul_X :
    (X : ℝ[X]) * X = X ^ 2 := by
  simp [pow_two]

@[simp] theorem classPolynomial_X_mul_X_pow (n : ℕ) :
    (X : ℝ[X]) * X ^ n = X ^ (n + 1) := by
  rw [pow_succ]
  ring

@[simp] theorem classPolynomial_X_pow_mul_X (n : ℕ) :
    (X : ℝ[X]) ^ n * X = X ^ (n + 1) := by
  exact (pow_succ X n).symm

@[simp] theorem classPolynomial_X_pow_mul_X_pow (m n : ℕ) :
    (X : ℝ[X]) ^ m * X ^ n = X ^ (m + n) := by
  exact (pow_add X m n).symm

@[simp] theorem classPolynomial_X_pow_mul_C (n : ℕ) (c : ℝ) :
    (X : ℝ[X]) ^ n * C c = C c * X ^ n := by
  ring

@[simp] theorem classPolynomial_X_pow_mul_C_mul (n : ℕ) (c : ℝ)
    (p : ℝ[X]) :
    (X : ℝ[X]) ^ n * (C c * p) = C c * (X ^ n * p) := by
  ring

theorem classPolynomial_X_mul_add (p q : ℝ[X]) :
    (X : ℝ[X]) * (p + q) = X * p + X * q := by
  ring

theorem classPolynomial_X_mul_sub (p q : ℝ[X]) :
    (X : ℝ[X]) * (p - q) = X * p - X * q := by
  ring

theorem classPolynomial_X_mul_C_mul (c : ℝ) (p : ℝ[X]) :
    (X : ℝ[X]) * (C c * p) = C c * (X * p) := by
  ring

@[simp] theorem classWeightedPolyIntegral_zero :
    classWeightedPolyIntegral (0 : ℝ[X]) = 0 := by
  simp [classWeightedPolyIntegral]

@[simp] theorem classWeightedPolyIntegral_one :
    classWeightedPolyIntegral (1 : ℝ[X]) = classMoment 0 := by
  simpa only [pow_zero] using classWeightedPolyIntegral_X_pow 0

@[simp] theorem classWeightedPolyIntegral_C (c : ℝ) :
    classWeightedPolyIntegral (C c) = c * classMoment 0 := by
  simpa only [mul_one, classWeightedPolyIntegral_one] using
    classWeightedPolyIntegral_C_mul c (1 : ℝ[X])

@[simp] theorem classWeightedPolyIntegral_X_mul_X :
    classWeightedPolyIntegral ((X : ℝ[X]) * X) = classMoment 2 := by
  rw [classPolynomial_X_mul_X]
  exact classWeightedPolyIntegral_X_pow 2

@[simp] theorem classWeightedPolyIntegral_X :
    classWeightedPolyIntegral (X : ℝ[X]) = classMoment 1 := by
  simpa only [pow_one] using classWeightedPolyIntegral_X_pow 1

theorem classWeightedPolyIntegral_neg (p : ℝ[X]) :
    classWeightedPolyIntegral (-p) = -classWeightedPolyIntegral p := by
  have h := classWeightedPolyIntegral_sub (0 : ℝ[X]) p
  simpa using h

/-! ## The unit-scale Gram owner -/

/-- A unit-scale Gram entry is the weighted integral of the product of its
two actual recursively defined Legendre factors. -/
theorem classGramUnitEntry_eq_weightedPolyIntegral (i j : Fin 8) :
    classGramUnitEntry i j =
      classWeightedPolyIntegral (legendrePoly (i : ℕ) * legendrePoly (j : ℕ)) := by
  unfold classGramUnitEntry classWeightedPolyIntegral classGramEntry
  apply integral_congr_ae
  filter_upwards [] with x
  simp [classWindowFun, classUnitWeight, Polynomial.eval_mul]
  ring

/-- Exact finite moment expansion of every unit-scale Gram entry. -/
theorem classGramUnitEntry_eq_moment_sum (i j : Fin 8) :
    classGramUnitEntry i j =
      ∑ n ∈ (legendrePoly (i : ℕ) * legendrePoly (j : ℕ)).support,
        (legendrePoly (i : ℕ) * legendrePoly (j : ℕ)).coeff n * classMoment n := by
  rw [classGramUnitEntry_eq_weightedPolyIntegral]
  exact classWeightedPolyIntegral_eq_moment_sum _

end
end C1ClassGramMomentConsumer
end Source
end ConnesWeilRH
