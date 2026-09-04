/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1ClassGramParity
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Record 1129: exact moment reduction for the class Gram owner

The even class bump gives the unit-scale weight

    w(x) = classBump x ^ 2.

This file proves two exact identities for its moments.  Odd moments vanish
by reflection.  For `k > 0`, integration of the derivative of
`x^k (1-x^2)^2 w(x)` gives

    k I_(k-1) - (2 k + 8) I_(k+1) + (k + 4) I_(k+3) = 0.

The factor `(1-x^2)^2` cancels the inverse-square derivative of the flat
exponential branch, and compact support removes the boundary term.  The
derived even-step form exposes the future Hbox-G certificate as a two-base-
moment problem.  No numerical interval or RH conclusion is supplied here.
-/

namespace ConnesWeilRH
namespace Source
namespace C1ClassGramMomentReduction

open MeasureTheory Set Filter
open C1ClassWindowObjects
open C1ClassGramOwner
open C1ClassGramParity
open scoped ContDiff Filter
open Polynomial

noncomputable section

/-! ## Weight and moments -/

/-- The unit-scale real weight carried by the class bump square. -/
noncomputable def classUnitWeight (x : ℝ) : ℝ :=
  classBump x * classBump x

/-- The unit-scale moments of the class bump square. -/
noncomputable def classMoment (n : ℕ) : ℝ :=
  ∫ x : ℝ, x ^ n * classUnitWeight x

theorem classBump_hasCompactSupport :
    HasCompactSupport classBump := by
  have h := classWindowFun_hasCompactSupport (1 : ℝ) (by norm_num) 0
  have heq : (fun x : ℝ => classBump x) = classWindowFun 1 0 := by
    funext x
    simp [classWindowFun, legendrePoly]
  change HasCompactSupport (fun x : ℝ => classBump x)
  rw [heq]
  exact h

theorem classUnitWeight_contDiff :
    ContDiff ℝ ∞ classUnitWeight := by
  simpa [classUnitWeight] using classBump_contDiff.mul classBump_contDiff

theorem classUnitWeight_hasCompactSupport :
    HasCompactSupport classUnitWeight := by
  have h := classBump_hasCompactSupport
  exact h.mul_right

theorem classUnitWeight_integrable :
    Integrable classUnitWeight := by
  exact classUnitWeight_contDiff.continuous.integrable_of_hasCompactSupport
    classUnitWeight_hasCompactSupport

theorem classMoment_integrable (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n * classUnitWeight x) := by
  have hcont : Continuous (fun x : ℝ => x ^ n * classUnitWeight x) :=
    (continuous_pow n).mul classUnitWeight_contDiff.continuous
  have hcompact : HasCompactSupport
      (fun x : ℝ => x ^ n * classUnitWeight x) := by
    exact classUnitWeight_hasCompactSupport.mul_left
  exact hcont.integrable_of_hasCompactSupport hcompact

/-! ## Reflection -/

theorem classUnitWeight_neg (x : ℝ) :
    classUnitWeight (-x) = classUnitWeight x := by
  simp [classUnitWeight, classBump_neg]

theorem classMoment_odd_zero {n : ℕ} (hn : Odd n) :
    classMoment n = 0 := by
  let f : ℝ → ℝ := fun x => x ^ n * classUnitWeight x
  obtain ⟨k, hk⟩ := hn
  have hpow : (-1 : ℝ) ^ n = -1 := by
    rw [hk]
    simp [pow_add]
  have hpoint : ∀ x : ℝ, f (-x) = -f x := by
    intro x
    dsimp [f]
    rw [classUnitWeight_neg]
    calc
      (-x) ^ n * classUnitWeight x =
          (-1 : ℝ) ^ n * (x ^ n * classUnitWeight x) := by
            rw [neg_pow]
            ring
      _ = -(x ^ n * classUnitWeight x) := by simp [hpow]
  have hsym : (∫ x : ℝ, f (-x)) = ∫ x : ℝ, f x :=
    integral_neg_eq_self f (volume : Measure ℝ)
  have hneg : (∫ x : ℝ, f (-x)) = -∫ x : ℝ, f x := by
    calc
      (∫ x : ℝ, f (-x)) = ∫ x : ℝ, -f x := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hpoint
      _ = -∫ x : ℝ, f x := by rw [integral_neg]
  have hz : (∫ x : ℝ, f x) = 0 := by
    linarith [hsym, hneg]
  simpa [classMoment, f] using hz

/-! ## The flat-bump derivative -/

/-- The global derivative formula for the class bump.  The flat branch at
zero is supplied by Mathlib's polynomial-times-inverse exponential lemma. -/
theorem hasDerivAt_classBump (x : ℝ) :
    HasDerivAt classBump
      ((-2 * x) * (1 - x ^ 2)⁻¹ ^ 2 * classBump x) x := by
  have harg : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-2 * x) x := by
    simpa [id_eq] using
      (hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).pow 2)
  have hflat :=
    expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul
      (1 : ℝ[X]) (1 - x ^ 2)
  have hcomp := hflat.comp x harg
  change HasDerivAt (fun y : ℝ => expNegInvGlue (1 - y ^ 2))
    ((-2 * x) * (1 - x ^ 2)⁻¹ ^ 2 * classBump x) x
  simpa [classBump, Function.comp_def] using hcomp

theorem hasDerivAt_classUnitWeight (x : ℝ) :
    HasDerivAt classUnitWeight
      ((-4 * x) * (1 - x ^ 2)⁻¹ ^ 2 * classUnitWeight x) x := by
  have h := (hasDerivAt_classBump x).mul (hasDerivAt_classBump x)
  convert h using 1
  simp only [classUnitWeight, inv_pow]
  ring

/-! ## Integration-by-parts core -/

noncomputable def momentIBPCore (k : ℕ) (x : ℝ) : ℝ :=
  x ^ k * (1 - x ^ 2) ^ 2 * classUnitWeight x

noncomputable def momentIBPDerivative (k : ℕ) (x : ℝ) : ℝ :=
  ((k : ℝ) * x ^ (k - 1) - (2 * (k : ℝ) + 8) * x ^ (k + 1) +
      ((k : ℝ) + 4) * x ^ (k + 3)) * classUnitWeight x

theorem momentIBPCore_integrable (k : ℕ) :
    Integrable (momentIBPCore k) := by
  have hcont : Continuous (momentIBPCore k) := by
    dsimp [momentIBPCore]
    exact ((continuous_pow k).mul
      ((continuous_const.sub (continuous_pow 2)).pow 2)).mul
      classUnitWeight_contDiff.continuous
  have hcompact : HasCompactSupport (momentIBPCore k) := by
    exact classUnitWeight_hasCompactSupport.mul_left
  exact hcont.integrable_of_hasCompactSupport hcompact

theorem momentIBPDerivative_integrable (k : ℕ) :
    Integrable (momentIBPDerivative k) := by
  have hcont : Continuous (momentIBPDerivative k) := by
    have h1 : Continuous (fun x : ℝ => (k : ℝ) * x ^ (k - 1)) :=
      continuous_const.mul (continuous_pow (k - 1))
    have h2 : Continuous
        (fun x : ℝ => (2 * (k : ℝ) + 8) * x ^ (k + 1)) :=
      continuous_const.mul (continuous_pow (k + 1))
    have h3 : Continuous
        (fun x : ℝ => ((k : ℝ) + 4) * x ^ (k + 3)) :=
      continuous_const.mul (continuous_pow (k + 3))
    have hpoly : Continuous
        (fun x : ℝ => (k : ℝ) * x ^ (k - 1) -
          (2 * (k : ℝ) + 8) * x ^ (k + 1) +
          ((k : ℝ) + 4) * x ^ (k + 3)) :=
      (h1.sub h2).add h3
    simpa [momentIBPDerivative] using hpoly.mul classUnitWeight_contDiff.continuous
  have hcompact : HasCompactSupport (momentIBPDerivative k) := by
    exact classUnitWeight_hasCompactSupport.mul_left
  exact hcont.integrable_of_hasCompactSupport hcompact

theorem momentIBPCore_hasDerivAt (k : ℕ) (hk : 0 < k) (x : ℝ) :
    HasDerivAt (momentIBPCore k) (momentIBPDerivative k x) x := by
  have hpow : HasDerivAt (fun y : ℝ => y ^ k)
      ((k : ℝ) * x ^ (k - 1)) x := by
    simpa using hasDerivAt_pow k x
  have hpoly : HasDerivAt (fun y : ℝ => (1 - y ^ 2) ^ 2)
      (-4 * x * (1 - x ^ 2)) x := by
    convert ((hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).pow 2)).pow 2 using 1
    simp [id_eq]
    ring
  have hweight := hasDerivAt_classUnitWeight x
  have hprod := (hpow.mul hpoly).mul hweight
  convert hprod using 1
  · dsimp [momentIBPCore, momentIBPDerivative]
    by_cases hy : 1 - x ^ 2 = 0
    · have hb : classUnitWeight x = 0 := by
        simp [classUnitWeight, classBump, hy]
      simp [hy, hb]
    · field_simp [hy]
      have hxpow : x ^ k = x ^ (k - 1) * x := by
        calc
          x ^ k = x ^ (k - 1 + 1) := by rw [Nat.sub_add_cancel hk]
          _ = x ^ (k - 1) * x := by simp [pow_add]
      have hxpow1 : x ^ (k + 1) = x ^ (k - 1) * x ^ 2 := by
        rw [show k + 1 = (k - 1) + 2 by omega, pow_add]
      have hxpow3 : x ^ (k + 3) = x ^ (k - 1) * x ^ 4 := by
        rw [show k + 3 = (k - 1) + 4 by omega, pow_add]
      repeat rw [hxpow]
      repeat rw [hxpow1]
      repeat rw [hxpow3]
      ring

/-! ## Exact moment recurrence -/

theorem classMoment_recurrence (k : ℕ) (hk : 0 < k) :
    (k : ℝ) * classMoment (k - 1) -
        (2 * (k : ℝ) + 8) * classMoment (k + 1) +
        ((k : ℝ) + 4) * classMoment (k + 3) = 0 := by
  have hzero : (∫ x : ℝ, momentIBPDerivative k x) = 0 :=
    integral_eq_zero_of_hasDerivAt_of_integrable
      (fun x => momentIBPCore_hasDerivAt k hk x)
      (momentIBPDerivative_integrable k) (momentIBPCore_integrable k)
  have hA := (classMoment_integrable (k - 1)).const_mul' (k : ℝ)
  have hB := (classMoment_integrable (k + 1)).const_mul'
    (2 * (k : ℝ) + 8)
  have hC := (classMoment_integrable (k + 3)).const_mul'
    ((k : ℝ) + 4)
  have hrewrite : (∫ x : ℝ, momentIBPDerivative k x) =
      (k : ℝ) * classMoment (k - 1) -
        (2 * (k : ℝ) + 8) * classMoment (k + 1) +
        ((k : ℝ) + 4) * classMoment (k + 3) := by
    have hfun : (fun x : ℝ => momentIBPDerivative k x) =
        (fun x => (k : ℝ) * (x ^ (k - 1) * classUnitWeight x) -
          (2 * (k : ℝ) + 8) * (x ^ (k + 1) * classUnitWeight x) +
          ((k : ℝ) + 4) * (x ^ (k + 3) * classUnitWeight x)) := by
      funext x
      dsimp [momentIBPDerivative]
      ring
    have hA' : Integrable
        (fun x : ℝ => (k : ℝ) * (x ^ (k - 1) * classUnitWeight x)) := by
      simpa only [Pi.mul_apply] using hA
    have hB' : Integrable
        (fun x : ℝ => (2 * (k : ℝ) + 8) *
          (x ^ (k + 1) * classUnitWeight x)) := by
      simpa only [Pi.mul_apply] using hB
    have hC' : Integrable
        (fun x : ℝ => ((k : ℝ) + 4) *
          (x ^ (k + 3) * classUnitWeight x)) := by
      simpa only [Pi.mul_apply] using hC
    have hsplit :
        (∫ x : ℝ,
          (k : ℝ) * (x ^ (k - 1) * classUnitWeight x) -
            (2 * (k : ℝ) + 8) * (x ^ (k + 1) * classUnitWeight x) +
            ((k : ℝ) + 4) * (x ^ (k + 3) * classUnitWeight x)) =
          (∫ x : ℝ,
            (k : ℝ) * (x ^ (k - 1) * classUnitWeight x) -
              (2 * (k : ℝ) + 8) * (x ^ (k + 1) * classUnitWeight x)) +
            ∫ x : ℝ, ((k : ℝ) + 4) *
              (x ^ (k + 3) * classUnitWeight x) := by
      simpa only [Pi.add_apply, Pi.sub_apply] using
        (integral_add (hA'.sub hB') hC')
    have hsplit' :
        (∫ x : ℝ,
          (k : ℝ) * (x ^ (k - 1) * classUnitWeight x) -
            (2 * (k : ℝ) + 8) * (x ^ (k + 1) * classUnitWeight x)) =
          (∫ x : ℝ, (k : ℝ) *
            (x ^ (k - 1) * classUnitWeight x)) -
            ∫ x : ℝ, (2 * (k : ℝ) + 8) *
              (x ^ (k + 1) * classUnitWeight x) := by
      simpa only [Pi.sub_apply] using (integral_sub hA' hB')
    rw [hfun, hsplit, hsplit']
    rw [integral_const_mul, integral_const_mul, integral_const_mul]
    rfl
  rw [← hrewrite]
  exact hzero

/-- The recurrence in the form consumed by a two-base even-moment
certificate.  Iterating this identity determines `I_(2n+4)` from the two
preceding even moments. -/
theorem classMoment_even_step (n : ℕ) :
    classMoment (2 * n + 4) =
      2 * classMoment (2 * n + 2) -
        ((2 * (n : ℝ) + 1) / (2 * (n : ℝ) + 5)) * classMoment (2 * n) := by
  have hrec := classMoment_recurrence (2 * n + 1) (by omega)
  have hden : (2 * (n : ℝ) + 5) ≠ 0 := by positivity
  have hcast1 : ((2 * n + 1 : ℕ) : ℝ) = 2 * (n : ℝ) + 1 := by norm_num
  have hcast2 : ((2 * n + 1 - 1 : ℕ) : ℕ) = 2 * n := by omega
  have hcast3 : ((2 * n + 1 + 1 : ℕ) : ℕ) = 2 * n + 2 := by omega
  have hcast4 : ((2 * n + 1 + 3 : ℕ) : ℕ) = 2 * n + 4 := by omega
  rw [hcast1, hcast2, hcast3, hcast4] at hrec
  field_simp [hden] at hrec ⊢
  linarith

end
end C1ClassGramMomentReduction
end Source
end ConnesWeilRH
