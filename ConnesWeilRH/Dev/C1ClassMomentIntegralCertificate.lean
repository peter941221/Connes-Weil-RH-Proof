/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1Q28ClassGramIntervalTransfer
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Record 1132: proof-carrying class-moment integral envelopes

Record 1131 transfers two numerical intervals to the q28 Gram owner, but it
does not pretend that the actual `classMoment 0` and `classMoment 2` lie in
those intervals.  This file fixes the lower-level carrier for that missing
producer.  An `IntegralEnvelope` carries globally visible comparison
functions, their interval integrability, pointwise inequalities on the
integration interval, and the values of the comparison integrals.  The target
integral bounds are then derived by the interval-integral monotonicity theorem.

There is no numerical instance here.  In particular, a future bump certificate
must prove its pointwise exponential bounds and its comparison-integral values;
the target bounds cannot be inserted as a data field.  RH is NOT claimed.
-/

namespace ConnesWeilRH
namespace Source
namespace C1ClassMomentIntegralCertificate

open MeasureTheory Set
open C1ClassGramMomentReduction
open scoped BigOperators Interval

noncomputable section

/-! ## The proof-carrying envelope -/

/-- A two-sided interval-integral envelope for a real function.

The `lower_value` and `upper_value` fields refer only to the comparison
functions.  They are intentionally not fields asserting an integral bound for
`f`; that conclusion is the theorem below. -/
structure IntegralEnvelope (f : ℝ → ℝ) (a b lo hi : ℝ) where
  lower : ℝ → ℝ
  upper : ℝ → ℝ
  lower_integrable : IntervalIntegrable lower volume a b
  target_integrable : IntervalIntegrable f volume a b
  upper_integrable : IntervalIntegrable upper volume a b
  lower_le : ∀ x ∈ Icc a b, lower x ≤ f x
  upper_le : ∀ x ∈ Icc a b, f x ≤ upper x
  lower_value : lo ≤ ∫ x in a..b, lower x
  upper_value : (∫ x in a..b, upper x) ≤ hi

/-! ## Generic transport -/

theorem integral_bounds_of_integralEnvelope
    {f : ℝ → ℝ} {a b lo hi : ℝ}
    (hab : a ≤ b) (h : IntegralEnvelope f a b lo hi) :
    lo ≤ (∫ x in a..b, f x) ∧ (∫ x in a..b, f x) ≤ hi := by
  have hlow : (∫ x in a..b, h.lower x) ≤ ∫ x in a..b, f x :=
    intervalIntegral.integral_mono_on hab h.lower_integrable
      h.target_integrable h.lower_le
  have hhigh : (∫ x in a..b, f x) ≤ ∫ x in a..b, h.upper x :=
    intervalIntegral.integral_mono_on hab h.target_integrable
      h.upper_integrable h.upper_le
  exact ⟨h.lower_value.trans hlow, hhigh.trans h.upper_value⟩

/-! ## The actual class-moment integrand and its compact interval -/

/-- The real integrand defining the class moment of order `n`. -/
noncomputable def classMomentIntegrand (n : ℕ) (x : ℝ) : ℝ :=
  x ^ n * classUnitWeight x

theorem classMomentIntegrand_support_subset_Ioc (n : ℕ) :
    Function.support (classMomentIntegrand n) ⊆ Ioc (-1 : ℝ) 1 := by
  intro x hx
  rw [Function.mem_support] at hx
  have hbump : classBump x ≠ 0 := by
    intro hzero
    apply hx
    simp [classMomentIntegrand, classUnitWeight, hzero]
  have habs : |x| < (1 : ℝ) := by
    by_contra hnot
    exact hbump (classBump_eq_zero (le_of_not_gt hnot))
  exact ⟨(abs_lt.mp habs).1, (abs_lt.mp habs).2.le⟩

theorem classMoment_eq_intervalIntegral (n : ℕ) :
    classMoment n = ∫ x in (-1 : ℝ)..1, classMomentIntegrand n x := by
  unfold classMoment
  symm
  apply intervalIntegral.integral_eq_integral_of_support_subset
  simpa [classMomentIntegrand] using
    classMomentIntegrand_support_subset n

/-- A proof-carrying envelope for the actual order-`n` class moment yields the
corresponding whole-line moment bounds. -/
theorem classMoment_bounds_of_integralEnvelope
    (n : ℕ) (lo hi : ℝ)
    (h : IntegralEnvelope (classMomentIntegrand n) (-1) 1 lo hi) :
    lo ≤ classMoment n ∧ classMoment n ≤ hi := by
  rw [classMoment_eq_intervalIntegral]
  exact integral_bounds_of_integralEnvelope (by norm_num) h

/-! ## A symbolic fidelity instance -/

/-- The carrier can be instantiated without any analytic assumption: this is
only a symbolic constant-function check of the transport theorem. -/
example : IntegralEnvelope (fun _ : ℝ => (1 : ℝ)) (-1) 1 0 4 := by
  refine
    { lower := fun _ => 0
      upper := fun _ => 2
      lower_integrable := continuous_const.intervalIntegrable _ _
      target_integrable := continuous_const.intervalIntegrable _ _
      upper_integrable := continuous_const.intervalIntegrable _ _
      lower_le := ?_
      upper_le := ?_
      lower_value := ?_
      upper_value := ?_ }
  · intro x hx
    norm_num
  · intro x hx
    norm_num
  · norm_num
  · norm_num

end
end C1ClassMomentIntegralCertificate
end Source
end ConnesWeilRH
