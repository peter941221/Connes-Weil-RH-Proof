/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1ClassMomentIntegralCertificate
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Record 1133: exact integrals for finite power-polynomial comparisons

This file supplies the calculus layer used by the proof-carrying moment
envelope of record 1132.  A comparison function is represented as a finite
sum of powers.  Its interval integral is reduced to a finite sum of exact
power integrals, so a later bump certificate can expose rational arithmetic
instead of storing a numerical target value.  The pointwise comparison
hypotheses remain explicit at the adapter boundary.  RH is NOT claimed.
-/

namespace ConnesWeilRH
namespace Source
namespace C1ClassMomentPolynomialIntegral

open MeasureTheory Set
open C1ClassGramMomentReduction
open C1ClassMomentIntegralCertificate
open scoped BigOperators Interval

noncomputable section

/-! ## Finite power sums -/

/-- A finite power polynomial with real coefficients. -/
def finitePowerPolynomial (s : Finset ℕ) (c : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ k ∈ s, c k * x ^ k

/-- The exact algebraic value obtained by integrating each power term. -/
def finitePowerIntegralValue
    (s : Finset ℕ) (c : ℕ → ℝ) (a b : ℝ) : ℝ :=
  ∑ k ∈ s, c k * ((b ^ (k + 1) - a ^ (k + 1)) / (k + 1))

theorem finitePowerPolynomial_continuous (s : Finset ℕ) (c : ℕ → ℝ) :
    Continuous (finitePowerPolynomial s c) := by
  unfold finitePowerPolynomial
  exact continuous_finsetSum _ (fun k hk =>
    continuous_const.mul (continuous_id.pow k))

theorem finitePowerPolynomial_intervalIntegrable
    (s : Finset ℕ) (c : ℕ → ℝ) (a b : ℝ) :
    IntervalIntegrable (finitePowerPolynomial s c) volume a b := by
  exact (finitePowerPolynomial_continuous s c).intervalIntegrable a b

/-- Exact interval integration of a finite power polynomial. -/
theorem intervalIntegral_finitePowerPolynomial
    (s : Finset ℕ) (c : ℕ → ℝ) (a b : ℝ) :
    (∫ x in a..b, finitePowerPolynomial s c x) =
      finitePowerIntegralValue s c a b := by
  unfold finitePowerPolynomial finitePowerIntegralValue
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [intervalIntegral.integral_const_mul, integral_pow]
  · intro k hk
    exact (continuous_const.mul (continuous_id.pow k)).intervalIntegrable a b

/-! ## Adapter to the 1132 envelope carrier -/

/-- Two finite power bounds produce an `IntegralEnvelope` once their
pointwise inequalities and exact finite-sum value bounds are supplied. -/
noncomputable def integralEnvelope_of_finitePowerBounds
    {f : ℝ → ℝ} {a b lo hi : ℝ}
    (hf : IntervalIntegrable f volume a b)
    (sLower sUpper : Finset ℕ) (cLower cUpper : ℕ → ℝ)
    (hLower : ∀ x ∈ Icc a b,
      finitePowerPolynomial sLower cLower x ≤ f x)
    (hUpper : ∀ x ∈ Icc a b,
      f x ≤ finitePowerPolynomial sUpper cUpper x)
    (hLowerValue : lo ≤ finitePowerIntegralValue sLower cLower a b)
    (hUpperValue : finitePowerIntegralValue sUpper cUpper a b ≤ hi) :
    IntegralEnvelope f a b lo hi := by
  refine
    { lower := finitePowerPolynomial sLower cLower
      upper := finitePowerPolynomial sUpper cUpper
      lower_integrable := finitePowerPolynomial_intervalIntegrable sLower cLower a b
      target_integrable := hf
      upper_integrable := finitePowerPolynomial_intervalIntegrable sUpper cUpper a b
      lower_le := hLower
      upper_le := hUpper
      lower_value := ?_
      upper_value := ?_ }
  · rw [intervalIntegral_finitePowerPolynomial]
    exact hLowerValue
  · rw [intervalIntegral_finitePowerPolynomial]
    exact hUpperValue

/-- Class-moment specialization of the finite-power adapter.  The only
remaining inputs are the genuine pointwise and finite-sum value bounds. -/
noncomputable def classMomentEnvelope_of_finitePowerBounds
    (n : ℕ) (lo hi : ℝ)
    (sLower sUpper : Finset ℕ) (cLower cUpper : ℕ → ℝ)
    (hLower : ∀ x ∈ Icc (-1 : ℝ) 1,
      finitePowerPolynomial sLower cLower x ≤ classMomentIntegrand n x)
    (hUpper : ∀ x ∈ Icc (-1 : ℝ) 1,
      classMomentIntegrand n x ≤ finitePowerPolynomial sUpper cUpper x)
    (hLowerValue : lo ≤ finitePowerIntegralValue sLower cLower (-1) 1)
    (hUpperValue : finitePowerIntegralValue sUpper cUpper (-1) 1 ≤ hi) :
    IntegralEnvelope (classMomentIntegrand n) (-1) 1 lo hi := by
  have hcont : Continuous (classMomentIntegrand n) := by
    unfold classMomentIntegrand
    exact (continuous_pow n).mul classUnitWeight_contDiff.continuous
  exact integralEnvelope_of_finitePowerBounds
    (f := classMomentIntegrand n) (a := (-1 : ℝ)) (b := 1)
    (lo := lo) (hi := hi) (hcont.intervalIntegrable (-1) 1)
    sLower sUpper cLower cUpper hLower hUpper hLowerValue hUpperValue

/-! ## Symbolic exactness check -/

example :
    (∫ x in (-1 : ℝ)..1,
      finitePowerPolynomial ({0, 2} : Finset ℕ)
        (fun k => if k = 0 then 1 else if k = 2 then 2 else 0) x) =
      (10 / 3 : ℝ) := by
  rw [intervalIntegral_finitePowerPolynomial]
  norm_num [finitePowerIntegralValue]

end
end C1ClassMomentPolynomialIntegral
end Source
end ConnesWeilRH
