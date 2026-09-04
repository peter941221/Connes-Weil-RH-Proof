/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1ClassGramMomentConsumer

/-!
# Record 1130: the finite class Gram moment model

This module consumes the exact polynomial-to-moment bridge and the record
1129 recurrence.  It proves the complete first-eight unit Gram matrix is a
two-base-moment expression.  The result is an exact algebraic reduction; it
does not assert that any numerical interval contains the two base moments.

RH is NOT claimed.
-/

namespace ConnesWeilRH
namespace Source
namespace C1ClassGramMomentModel

open C1ClassWindowObjects
open C1ClassGramScale
open C1ClassGramMomentReduction
open C1ClassGramMomentConsumer
open Matrix
open Polynomial
open scoped BigOperators

noncomputable section

/-- The exact unit-scale Gram matrix obtained after reducing its even moments
to `I_0` and `I_2`.  This is an algebraic model, not a numerical enclosure. -/
noncomputable def classGramMomentModel (I0 I2 : ℝ) :
    Matrix (Fin 8) (Fin 8) ℝ :=
  !![
    I0, 0, -(I0 - 3 * I2) / 2, 0, -(I0 - 10 * I2) / 2, 0,
      -(43 * I0 - 375 * I2) / 20, 0;
    0, I2, 0, -(I0 - 7 * I2) / 2, 0,
      -(14 * I0 - 125 * I2) / 10, 0, -(427 * I0 - 3715 * I2) / 84;
    -(I0 - 3 * I2) / 2, 0, -(I0 - 15 * I2) / 5, 0,
      -(5 * I0 - 41 * I2) / 4, 0, -4 * I0 + 35 * I2, 0;
    0, -(I0 - 7 * I2) / 2, 0,
      -(7 * I0 - 67 * I2) / 7, 0,
      -(73 * I0 - 625 * I2) / 20, 0,
      -(35 * I0 - 305 * I2) / 3;
    -(I0 - 10 * I2) / 2, 0,
      -(5 * I0 - 41 * I2) / 4, 0,
      -(122 * I0 - 1085 * I2) / 36, 0,
      -(1313 * I0 - 11375 * I2) / 120, 0;
    0, -(14 * I0 - 125 * I2) / 10, 0,
      -(73 * I0 - 625 * I2) / 20, 0,
      -(2331 * I0 - 20400 * I2) / 220, 0,
      -(27251 * I0 - 236825 * I2) / 840;
    -(43 * I0 - 375 * I2) / 20, 0,
      -4 * I0 + 35 * I2, 0,
      -(1313 * I0 - 11375 * I2) / 120, 0,
      -(8287 * I0 - 72225 * I2) / 260, 0;
    0, -(427 * I0 - 3715 * I2) / 84, 0,
      -(35 * I0 - 305 * I2) / 3, 0,
      -(27251 * I0 - 236825 * I2) / 840, 0,
      -(195433 * I0 - 1701325 * I2) / 2100
  ]

/-- The finite even-moment instances needed by the first eight products. -/
theorem classMoment_even_recurrence_instances :
    classMoment 4 = 2 * classMoment 2 - (1 / 5 : ℝ) * classMoment 0 ∧
    classMoment 6 = 2 * classMoment 4 - (3 / 7 : ℝ) * classMoment 2 ∧
    classMoment 8 = 2 * classMoment 6 - (5 / 9 : ℝ) * classMoment 4 ∧
    classMoment 10 = 2 * classMoment 8 - (7 / 11 : ℝ) * classMoment 6 ∧
    classMoment 12 = 2 * classMoment 10 - (9 / 13 : ℝ) * classMoment 8 ∧
    classMoment 14 = 2 * classMoment 12 - (11 / 15 : ℝ) * classMoment 10 := by
  have h4 := classMoment_even_step 0
  have h6 := classMoment_even_step 1
  have h8 := classMoment_even_step 2
  have h10 := classMoment_even_step 3
  have h12 := classMoment_even_step 4
  have h14 := classMoment_even_step 5
  norm_num at h4 h6 h8 h10 h12 h14
  exact ⟨h4, h6, h8, h10, h12, h14⟩

/-! The first-eight unit Gram matrix is exactly the two-base-moment model. -/
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000000 in
-- reason: 64 finite-index cases, each expanding a recursively defined Legendre product
theorem classGramUnitMatrix_eq_classGramMomentModel :
    classGramUnitMatrix =
      classGramMomentModel (classMoment 0) (classMoment 2) := by
  rcases classMoment_even_recurrence_instances with
    ⟨h4, h6, h8, h10, h12, h14⟩
  have h1 := classMoment_odd_zero (n := 1) (⟨0, by norm_num⟩ : Odd 1)
  have h3 := classMoment_odd_zero (n := 3) (⟨1, by norm_num⟩ : Odd 3)
  have h5 := classMoment_odd_zero (n := 5) (⟨2, by norm_num⟩ : Odd 5)
  have h7 := classMoment_odd_zero (n := 7) (⟨3, by norm_num⟩ : Odd 7)
  have h9 := classMoment_odd_zero (n := 9) (⟨4, by norm_num⟩ : Odd 9)
  have h11 := classMoment_odd_zero (n := 11) (⟨5, by norm_num⟩ : Odd 11)
  have h13 := classMoment_odd_zero (n := 13) (⟨6, by norm_num⟩ : Odd 13)
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    rw [classGramUnitEntry_apply, classGramUnitEntry_eq_weightedPolyIntegral]
    simp [classGramMomentModel, legendrePoly, Polynomial.smul_eq_C_mul,
      mul_sub, sub_mul, mul_assoc, ← Polynomial.C_ofNat,
      classWeightedPolyIntegral_sub, classWeightedPolyIntegral_C_mul,
      classWeightedPolyIntegral_mul_C, classWeightedPolyIntegral_X_pow,
      classPolynomial_X_mul_X, classPolynomial_X_mul_C_mul,
      h1, h3, h5, h7, h9, h11, h13, h4, h6, h8, h10, h12, h14]
  all_goals ring_nf

end
end C1ClassGramMomentModel
end Source
end ConnesWeilRH
