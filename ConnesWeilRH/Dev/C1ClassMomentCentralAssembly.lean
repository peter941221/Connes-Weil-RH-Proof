/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1ClassMomentTailCertificate

/-!
# Record 1135: central class-moment assembly and endpoint budget

The endpoint certificate of record 1134 bounds both tails of every class
moment at radius `99 / 100`.  This file performs the exact interval assembly
which reduces the remaining true-data producer to the central interval.  For
even moments the two tails agree by reflection, so a central `IntegralEnvelope`
transports to a whole-line bound with the explicit endpoint budget
`2 / 10 ^ 15`.

No central numerical value is stored here.  The central envelope retains its
comparison functions, pointwise inequalities, and exact comparison-integral
value bounds.  RH is NOT claimed.
-/

namespace ConnesWeilRH
namespace Source
namespace C1ClassMomentCentralAssembly

open MeasureTheory Set
open C1ClassWindowObjects
open C1ClassGramMomentReduction
open C1ClassMomentIntegralCertificate
open C1ClassMomentTailCertificate
open scoped BigOperators Interval

noncomputable section

/-! ## The central interval -/

/-- The rational radius retained for the central class-moment integral. -/
noncomputable def centralRadius : ℝ := 99 / 100

theorem centralRadius_pos : 0 < centralRadius := by
  unfold centralRadius
  norm_num

theorem centralRadius_lt_one : centralRadius < 1 := by
  unfold centralRadius
  norm_num

/-- The central interval integral of the order-`n` class moment integrand. -/
noncomputable def centralMoment (n : ℕ) : ℝ :=
  ∫ x in (-centralRadius)..centralRadius, classMomentIntegrand n x

theorem classMomentIntegrand_intervalIntegrable
    (n : ℕ) (a b : ℝ) :
    IntervalIntegrable (classMomentIntegrand n) volume a b := by
  have hcont : Continuous (classMomentIntegrand n) := by
    unfold classMomentIntegrand
    exact (continuous_pow n).mul classUnitWeight_contDiff.continuous
  exact hcont.intervalIntegrable a b

/-! ## Reflection and exact interval assembly -/

theorem classMomentIntegrand_neg_of_even {n : ℕ} (hn : Even n) (x : ℝ) :
    classMomentIntegrand n (-x) = classMomentIntegrand n x := by
  change (-x) ^ n * classUnitWeight (-x) =
    x ^ n * classUnitWeight x
  rw [hn.neg_pow x, classUnitWeight_neg]

/-- Reflection identifies the left endpoint tail with the right tail for an
even moment. -/
theorem classMoment_leftTail_eq_rightTail_of_even
    {n : ℕ} (hn : Even n) :
    (∫ x in (-1 : ℝ)..(-centralRadius), classMomentIntegrand n x) =
      ∫ x in centralRadius..1, classMomentIntegrand n x := by
  rw [← intervalIntegral.integral_comp_neg
    (f := classMomentIntegrand n) (a := centralRadius) (b := (1 : ℝ))]
  refine intervalIntegral.integral_congr ?_
  intro x hx
  exact classMomentIntegrand_neg_of_even hn x

/-- Exact three-interval decomposition of a class moment. -/
theorem classMoment_eq_three_interval (n : ℕ) :
    classMoment n =
      (∫ x in (-1 : ℝ)..(-centralRadius), classMomentIntegrand n x) +
        (∫ x in (-centralRadius)..centralRadius, classMomentIntegrand n x) +
        (∫ x in centralRadius..1, classMomentIntegrand n x) := by
  rw [classMoment_eq_intervalIntegral]
  have hleft := classMomentIntegrand_intervalIntegrable n
    (-1 : ℝ) (-centralRadius)
  have hmiddle := classMomentIntegrand_intervalIntegrable n
    (-centralRadius) centralRadius
  have hright := classMomentIntegrand_intervalIntegrable n
    centralRadius 1
  have hleftRest := classMomentIntegrand_intervalIntegrable n
    (-centralRadius) (1 : ℝ)
  rw [← intervalIntegral.integral_add_adjacent_intervals hleft hleftRest,
    ← intervalIntegral.integral_add_adjacent_intervals hmiddle hright]
  ring

/-! ## The central proof-carrying certificate -/

/-- A central-interval `IntegralEnvelope` for the actual class-moment
integrand.  Its comparison data, rather than a desired whole-line conclusion,
is the producer interface. -/
def centralMomentEnvelope (n : ℕ) (lo hi : ℝ) : Type :=
  IntegralEnvelope (classMomentIntegrand n) (-centralRadius) centralRadius lo hi

theorem centralMoment_bounds_of_centralEnvelope
    (n : ℕ) (lo hi : ℝ)
    (h : centralMomentEnvelope n lo hi) :
    lo ≤ centralMoment n ∧ centralMoment n ≤ hi := by
  unfold centralMoment centralMomentEnvelope at *
  exact integral_bounds_of_integralEnvelope (by
    unfold centralRadius
    norm_num) h

/-! ## Transport of the endpoint budget -/

/-- A genuine central envelope for an even moment yields a whole-line bound;
the strict endpoint tails contribute exactly `2 / 10 ^ 15`. -/
theorem classMoment_bounds_of_centralEnvelope_of_even
    {n : ℕ} (hn : Even n) {lo hi : ℝ}
    (h : centralMomentEnvelope n lo hi) :
    lo - (2 / 10 ^ 15 : ℝ) < classMoment n ∧
      classMoment n < hi + (2 / 10 ^ 15 : ℝ) := by
  have hcentral :
      lo ≤ (∫ x in (-centralRadius)..centralRadius,
        classMomentIntegrand n x) ∧
        (∫ x in (-centralRadius)..centralRadius,
          classMomentIntegrand n x) ≤ hi := by
    simpa [centralMoment] using
      (centralMoment_bounds_of_centralEnvelope n lo hi h)
  have htailAbs :
      |∫ x in centralRadius..1, classMomentIntegrand n x| <
        (1 / 10 ^ 15 : ℝ) := by
    simpa [centralRadius, Real.norm_eq_abs] using
      (norm_intervalIntegral_classMoment_rightTail_q99_lt n)
  have htail := (abs_lt.mp htailAbs)
  rw [classMoment_eq_three_interval n,
    classMoment_leftTail_eq_rightTail_of_even hn]
  constructor <;> linarith [hcentral.1, hcentral.2, htail.1, htail.2]

end
end C1ClassMomentCentralAssembly
end Source
end ConnesWeilRH
