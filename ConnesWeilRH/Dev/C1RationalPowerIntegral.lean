/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1ClassMomentPolynomialIntegral
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Record 1138: rational-power interval integral engine

The pointwise envelope of record 1137 is a finite power of a polynomial in
`(1 - x^2)⁻¹`.  This file supplies the exact calculus layer for that form on
the central interval `[-97/100, 97/100]`.  The primitive recurrence is the
standard reduction for powers of `1 - x^2`; its only transcendental endpoint
value is `Real.log (197/3)`.  No numerical target or RH conclusion is
introduced.
-/

namespace ConnesWeilRH
namespace Source
namespace C1RationalPowerIntegral

open MeasureTheory Set
open scoped BigOperators Interval

noncomputable section

/-! ## The fixed central interval and denominator powers -/

/-- The central radius used by the exact rational comparison. -/
noncomputable def rationalRadius : ℝ := 97 / 100

/-- The `k`-th power of the reciprocal quadratic denominator. -/
noncomputable def denominatorPower (k : ℕ) (x : ℝ) : ℝ :=
  (1 - x ^ 2)⁻¹ ^ k

theorem rationalRadius_pos : 0 < rationalRadius := by
  norm_num [rationalRadius]

theorem rationalRadius_lt_one : rationalRadius < 1 := by
  norm_num [rationalRadius]

theorem one_sub_sq_pos_of_abs_lt_one {x : ℝ} (hx : |x| < 1) :
    0 < 1 - x ^ 2 := by
  rw [abs_lt] at hx
  have hsq : x ^ 2 < 1 := by
    nlinarith
  linarith

theorem abs_lt_one_of_mem_central {x : ℝ}
    (hx : x ∈ Icc (-rationalRadius) rationalRadius) : |x| < 1 := by
  rw [abs_lt]
  constructor <;> linarith [hx.1, hx.2, rationalRadius_pos,
    rationalRadius_lt_one]

private theorem one_sub_sq_ne_zero_of_mem_central {x : ℝ}
    (hx : x ∈ Icc (-rationalRadius) rationalRadius) :
    1 - x ^ 2 ≠ 0 :=
  (one_sub_sq_pos_of_abs_lt_one (abs_lt_one_of_mem_central hx)).ne'

theorem denominatorPower_continuousOn (k : ℕ) :
    ContinuousOn (denominatorPower k) (Icc (-rationalRadius) rationalRadius) := by
  unfold denominatorPower
  have hbase : ContinuousOn (fun x : ℝ => 1 - x ^ 2)
      (Icc (-rationalRadius) rationalRadius) :=
    continuousOn_const.sub (continuousOn_id.pow 2)
  have hne : ∀ x ∈ Icc (-rationalRadius) rationalRadius,
      1 - x ^ 2 ≠ 0 := by
    intro x hx
    exact one_sub_sq_ne_zero_of_mem_central hx
  exact (hbase.inv₀ hne).pow k

theorem denominatorPower_intervalIntegrable (k : ℕ) :
    IntervalIntegrable (denominatorPower k) volume
      (-rationalRadius) rationalRadius := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le (by linarith [rationalRadius_pos])]
  exact denominatorPower_continuousOn k

private theorem const_denominatorPower_intervalIntegrable (k : ℕ) (c : ℝ) :
    IntervalIntegrable (fun x : ℝ => c * denominatorPower k x) volume
      (-rationalRadius) rationalRadius := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le (by linarith [rationalRadius_pos])]
  exact continuousOn_const.mul (denominatorPower_continuousOn k)

/-! ## The recursive primitive -/

/-- A primitive of `(1-x^2)⁻ᵏ` on the open unit interval. -/
noncomputable def rationalPowerPrimitive : ℕ → ℝ → ℝ
  | 0 => fun x => x
  | 1 => fun x => (Real.log (1 + x) - Real.log (1 - x)) / 2
  | k + 2 => fun x =>
      x * (1 - x ^ 2)⁻¹ ^ (k + 1) / (2 * ((k : ℝ) + 1)) +
        ((2 * (k : ℝ) + 1) / (2 * ((k : ℝ) + 1))) *
          rationalPowerPrimitive (k + 1) x

theorem rationalPowerPrimitive_hasDerivAt {k : ℕ} {x : ℝ}
    (hx : |x| < 1) :
    HasDerivAt (rationalPowerPrimitive k) (denominatorPower k x) x := by
  induction k with
  | zero =>
      simpa [rationalPowerPrimitive, denominatorPower] using (hasDerivAt_id x)
  | succ k ih =>
      cases k with
      | zero =>
          have hplus : HasDerivAt (fun y : ℝ => 1 + y) 1 x := by
            simpa using (hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x)
          have hminus : HasDerivAt (fun y : ℝ => 1 - y) (-1 : ℝ) x := by
            simpa using (hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)
          have hpluspos : 0 < 1 + x := by
            rw [abs_lt] at hx
            linarith
          have hminuspos : 0 < 1 - x := by
            rw [abs_lt] at hx
            linarith
          have hlogplus :=
            (Real.hasDerivAt_log (ne_of_gt hpluspos)).comp x hplus
          have hlogminus :=
            (Real.hasDerivAt_log (ne_of_gt hminuspos)).comp x hminus
          have hbase := (hlogplus.sub hlogminus).div_const (2 : ℝ)
          have hvalue :
              ((1 + x)⁻¹ * 1 - (1 - x)⁻¹ * (-1 : ℝ)) / 2 =
                (1 - x ^ 2)⁻¹ := by
            field_simp [hpluspos.ne', hminuspos.ne',
              (one_sub_sq_pos_of_abs_lt_one hx).ne']; ring
          have hbase' := hbase.congr_deriv hvalue
          simpa [rationalPowerPrimitive, denominatorPower,
            Function.comp_apply] using hbase'
      | succ k =>
          have hden : HasDerivAt (fun y : ℝ => 1 - y ^ 2)
              (-2 * x) x := by
            convert (hasDerivAt_const x (1 : ℝ)).sub
              ((hasDerivAt_id x).pow 2) using 1; simp [id_eq]
          have hden_ne : 1 - x ^ 2 ≠ 0 :=
            (one_sub_sq_pos_of_abs_lt_one hx).ne'
          have hinv := hden.inv hden_ne
          have hpow := hinv.pow (k + 1)
          have hterm :=
            (hasDerivAt_id x).mul hpow |>.div_const
              (2 * ((k : ℝ) + 1))
          have hrec := ih.const_mul
            ((2 * (k : ℝ) + 1) / (2 * ((k : ℝ) + 1)))
          have hsum := hterm.add hrec
          convert hsum using 1
          all_goals simp [denominatorPower]
          all_goals field_simp [hden_ne]
          all_goals ring

/-! ## Endpoint recurrence -/

/-- The exact symmetric endpoint values of the primitive recurrence. -/
noncomputable def rationalPowerIntervalValue : ℕ → ℝ
  | 0 => 2 * rationalRadius
  | 1 => Real.log ((1 + rationalRadius) / (1 - rationalRadius))
  | k + 2 =>
      rationalRadius /
          (((k : ℝ) + 1) * (1 - rationalRadius ^ 2) ^ (k + 1)) +
        ((2 * (k : ℝ) + 1) / (2 * ((k : ℝ) + 1))) *
          rationalPowerIntervalValue (k + 1)

theorem rationalPowerPrimitive_endpoint_difference (k : ℕ) :
    rationalPowerPrimitive k rationalRadius -
        rationalPowerPrimitive k (-rationalRadius) =
      rationalPowerIntervalValue k := by
  induction k with
  | zero =>
      simp [rationalPowerPrimitive, rationalPowerIntervalValue]
      ring
  | succ k ih =>
      cases k with
      | zero =>
          have hp : 0 < 1 + rationalRadius := by
            linarith [rationalRadius_pos]
          have hm : 0 < 1 - rationalRadius := by
            linarith [rationalRadius_lt_one]
          simp only [rationalPowerPrimitive, rationalPowerIntervalValue]
          calc
            (Real.log (1 + rationalRadius) - Real.log (1 - rationalRadius)) / 2 -
                (Real.log (1 + -rationalRadius) -
                  Real.log (1 - -rationalRadius)) / 2 =
                Real.log (1 + rationalRadius) - Real.log (1 - rationalRadius) := by
                  ring_nf
            _ = Real.log ((1 + rationalRadius) / (1 - rationalRadius)) := by
              rw [Real.log_div hp.ne' hm.ne']
      | succ k =>
          simp only [rationalPowerPrimitive, rationalPowerIntervalValue]
          have hrad : 1 - (-rationalRadius) ^ 2 =
              1 - rationalRadius ^ 2 := by ring
          have hden : 1 - rationalRadius ^ 2 ≠ 0 := by
            exact (one_sub_sq_pos_of_abs_lt_one (by
              rw [abs_lt]
              constructor <;> linarith [rationalRadius_pos,
                rationalRadius_lt_one])).ne'
          have hfirst :
              rationalRadius * (1 - rationalRadius ^ 2)⁻¹ ^ (k + 1) /
                    (2 * ((k : ℝ) + 1)) -
                (-rationalRadius) * (1 - (-rationalRadius) ^ 2)⁻¹ ^ (k + 1) /
                    (2 * ((k : ℝ) + 1)) =
                rationalRadius /
                    (((k : ℝ) + 1) *
                      (1 - rationalRadius ^ 2) ^ (k + 1)) := by
            rw [hrad]
            rw [inv_pow]
            field_simp [hden]
            ring
          calc
            rationalRadius * (1 - rationalRadius ^ 2)⁻¹ ^ (k + 1) /
                  (2 * ((k : ℝ) + 1)) +
                ((2 * (k : ℝ) + 1) / (2 * ((k : ℝ) + 1))) *
                    rationalPowerPrimitive (k + 1) rationalRadius -
                ((-rationalRadius) * (1 - (-rationalRadius) ^ 2)⁻¹ ^ (k + 1) /
                  (2 * ((k : ℝ) + 1)) +
                ((2 * (k : ℝ) + 1) / (2 * ((k : ℝ) + 1))) *
                    rationalPowerPrimitive (k + 1) (-rationalRadius)) =
              (rationalRadius * (1 - rationalRadius ^ 2)⁻¹ ^ (k + 1) /
                  (2 * ((k : ℝ) + 1)) -
                (-rationalRadius) * (1 - (-rationalRadius) ^ 2)⁻¹ ^ (k + 1) /
                  (2 * ((k : ℝ) + 1))) +
                ((2 * (k : ℝ) + 1) / (2 * ((k : ℝ) + 1))) *
                  (rationalPowerPrimitive (k + 1) rationalRadius -
                    rationalPowerPrimitive (k + 1) (-rationalRadius)) := by
              ring
            _ = rationalPowerIntervalValue (k + 2) := by
              rw [hfirst, ih]
              rfl

theorem intervalIntegral_denominatorPower (k : ℕ) :
    (∫ x in (-rationalRadius)..rationalRadius, denominatorPower k x) =
      rationalPowerIntervalValue k := by
  have hderiv : ∀ x ∈ uIcc (-rationalRadius) rationalRadius,
      HasDerivAt (rationalPowerPrimitive k) (denominatorPower k x) x := by
    intro x hx
    rw [uIcc_of_le (by linarith [rationalRadius_pos])] at hx
    exact rationalPowerPrimitive_hasDerivAt
      (abs_lt_one_of_mem_central hx)
  calc
    (∫ x in (-rationalRadius)..rationalRadius, denominatorPower k x) =
        rationalPowerPrimitive k rationalRadius -
          rationalPowerPrimitive k (-rationalRadius) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
        (denominatorPower_intervalIntegrable k)
    _ = rationalPowerIntervalValue k :=
      rationalPowerPrimitive_endpoint_difference k

/-! ## Finite sums and order-2 moments -/

/-- A finite rational function in the reciprocal quadratic denominator. -/
noncomputable def finiteDenominatorPowerPolynomial
    (s : Finset ℕ) (c : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ k ∈ s, c k * denominatorPower k x

/-- The exact endpoint expression for a finite denominator-power sum. -/
noncomputable def finiteDenominatorPowerIntegralValue
    (s : Finset ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ k ∈ s, c k * rationalPowerIntervalValue k

theorem intervalIntegral_finiteDenominatorPowerPolynomial
    (s : Finset ℕ) (c : ℕ → ℝ) :
    (∫ x in (-rationalRadius)..rationalRadius,
      finiteDenominatorPowerPolynomial s c x) =
      finiteDenominatorPowerIntegralValue s c := by
  unfold finiteDenominatorPowerPolynomial finiteDenominatorPowerIntegralValue
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral_denominatorPower]
  · intro k hk
    exact const_denominatorPower_intervalIntegrable k (c k)

/-- The exact interval value of `x² (1-x²)⁻ᵏ`. -/
noncomputable def denominatorPowerMomentValue : ℕ → ℝ
  | 0 => 2 * rationalRadius ^ 3 / 3
  | k + 1 => rationalPowerIntervalValue (k + 1) -
      rationalPowerIntervalValue k

theorem denominatorPowerMoment_intervalIntegrable (k : ℕ) :
    IntervalIntegrable (fun x : ℝ => x ^ 2 * denominatorPower k x)
      volume (-rationalRadius) rationalRadius := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le (by linarith [rationalRadius_pos])]
  exact (continuousOn_id.pow 2).mul (denominatorPower_continuousOn k)

private theorem const_denominatorPowerMoment_intervalIntegrable
    (k : ℕ) (c : ℝ) :
    IntervalIntegrable
      (fun x : ℝ => c * (x ^ 2 * denominatorPower k x)) volume
      (-rationalRadius) rationalRadius := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le (by linarith [rationalRadius_pos])]
  exact continuousOn_const.mul
    ((continuousOn_id.pow 2).mul (denominatorPower_continuousOn k))

theorem intervalIntegral_denominatorPowerMoment (k : ℕ) :
    (∫ x in (-rationalRadius)..rationalRadius,
      x ^ 2 * denominatorPower k x) = denominatorPowerMomentValue k := by
  cases k with
  | zero =>
      simp only [denominatorPower, pow_zero, mul_one,
        denominatorPowerMomentValue]
      rw [integral_pow]
      norm_num [rationalRadius]
  | succ k =>
      have hrewrite :
          (∫ x in (-rationalRadius)..rationalRadius,
            x ^ 2 * denominatorPower (k + 1) x) =
            (∫ x in (-rationalRadius)..rationalRadius, denominatorPower (k + 1) x) -
              ∫ x in (-rationalRadius)..rationalRadius, denominatorPower k x := by
        rw [← intervalIntegral.integral_sub
          (denominatorPower_intervalIntegrable (k + 1))
          (denominatorPower_intervalIntegrable k)]
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le (by linarith [rationalRadius_pos])] at hx
        have hne := one_sub_sq_ne_zero_of_mem_central hx
        unfold denominatorPower
        have hbase : x ^ 2 * (1 - x ^ 2)⁻¹ =
            (1 - x ^ 2)⁻¹ - 1 := by
          field_simp [hne]
          ring
        change x ^ 2 * (1 - x ^ 2)⁻¹ ^ (k + 1) =
          (1 - x ^ 2)⁻¹ ^ (k + 1) - (1 - x ^ 2)⁻¹ ^ k
        have hpow_succ :
            (1 - x ^ 2)⁻¹ ^ (k + 1) =
              (1 - x ^ 2)⁻¹ ^ k * (1 - x ^ 2)⁻¹ := by
          rw [pow_succ]
        calc
          x ^ 2 * (1 - x ^ 2)⁻¹ ^ (k + 1) =
              x ^ 2 * ((1 - x ^ 2)⁻¹ ^ k * (1 - x ^ 2)⁻¹) := by
            rw [hpow_succ]
          _ =
              (x ^ 2 * (1 - x ^ 2)⁻¹) * (1 - x ^ 2)⁻¹ ^ k := by ring
          _ = ((1 - x ^ 2)⁻¹ - 1) * (1 - x ^ 2)⁻¹ ^ k := by
            rw [hbase]
          _ = (1 - x ^ 2)⁻¹ * (1 - x ^ 2)⁻¹ ^ k -
              (1 - x ^ 2)⁻¹ ^ k := by ring
          _ = (1 - x ^ 2)⁻¹ ^ (k + 1) -
              (1 - x ^ 2)⁻¹ ^ k := by
            rw [hpow_succ]
            ring
      rw [hrewrite, intervalIntegral_denominatorPower,
        intervalIntegral_denominatorPower]
      rfl

/-- A finite order-2 rational comparison function. -/
noncomputable def finiteDenominatorPowerMomentPolynomial
    (s : Finset ℕ) (c : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ k ∈ s, c k * (x ^ 2 * denominatorPower k x)

/-- The exact endpoint expression for a finite order-2 comparison. -/
noncomputable def finiteDenominatorPowerMomentIntegralValue
    (s : Finset ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ k ∈ s, c k * denominatorPowerMomentValue k

theorem intervalIntegral_finiteDenominatorPowerMomentPolynomial
    (s : Finset ℕ) (c : ℕ → ℝ) :
    (∫ x in (-rationalRadius)..rationalRadius,
      finiteDenominatorPowerMomentPolynomial s c x) =
      finiteDenominatorPowerMomentIntegralValue s c := by
  unfold finiteDenominatorPowerMomentPolynomial
    finiteDenominatorPowerMomentIntegralValue
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral_denominatorPowerMoment]
  · intro k hk
    exact const_denominatorPowerMoment_intervalIntegrable k (c k)

/-! ## Small symbolic checks -/

example : rationalPowerIntervalValue 0 = (97 / 50 : ℝ) := by
  norm_num [rationalPowerIntervalValue, rationalRadius]

example : denominatorPowerMomentValue 0 =
    (2 * (97 / 100 : ℝ) ^ 3 / 3 : ℝ) := by
  rfl

end
end C1RationalPowerIntegral
end Source
end ConnesWeilRH
