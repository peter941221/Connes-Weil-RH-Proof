/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.CC20YoshidaConvolution

/-!
# C1CompactLogL2Export - L2 norm accessor and the global mass bridge bound

The B5 path is value-based: `HealthyYoshidaDetectorData` pins values at
nodes, and no `‖·‖₂` accessor exists on `CompactLogTest`.  This file
exports the squared L2 norm and proves the 1377 Lemma A bound: the
Laplace evaluation at any point `s` is Cauchy-Schwarz-bounded by the
exact window antiderivative times the L2 norm,

```
‖laplaceAt f s‖^2  ≤  (∫ x in a..b, exp(2 * s.re * x)) * (∫ x, ‖f.test x‖ ^ 2)
```

for `f` supported in `(a, b)`.  The constant is the exact antiderivative
`(e^(2 d b) - e^(2 d a)) / (2 d)` in division-free integral form; the
`s.re = 0` case reads `b - a`, the sigma-line evaluation constant used by
the `PW_R` end of the vertical chain.

Design record: docs/proofs/1381_l2_export_and_lemma_a.md.
-/

namespace ConnesWeilRH
namespace Source
namespace C1CompactLogL2Export

open MeasureTheory
open scoped ContDiff
open CCM25Concrete.CompactLogConvolution
open CC20YoshidaConvolution.CompactLogTest

/-- Squared L2 norm of a compact log test. -/
noncomputable def compactLogL2sq (f : CompactLogTest) : ℝ :=
  ∫ x : ℝ, ‖f.test x‖ ^ 2

/-- Window Cauchy-Schwarz by the discriminant argument (power form). -/
theorem intervalIntegral_cauchySchwarz {u v : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hu : ContinuousOn u (Set.uIcc a b)) (hv : ContinuousOn v (Set.uIcc a b)) :
    (∫ x : ℝ in a..b, u x * v x ∂volume) ^ 2 ≤
      (∫ x : ℝ in a..b, u x ^ 2 ∂volume) *
        (∫ x : ℝ in a..b, v x ^ 2 ∂volume) := by
  have huC : ContinuousOn (fun x : ℝ => u x ^ 2) (Set.uIcc a b) := hu.pow 2
  have hvC : ContinuousOn (fun x : ℝ => v x ^ 2) (Set.uIcc a b) := hv.pow 2
  have huvC : ContinuousOn (fun x : ℝ => u x * v x) (Set.uIcc a b) := hu.mul hv
  have hA : 0 ≤ ∫ x : ℝ in a..b, v x ^ 2 ∂volume :=
    intervalIntegral.integral_nonneg hab fun x _ => sq_nonneg (v x)
  have hC : 0 ≤ ∫ x : ℝ in a..b, u x ^ 2 ∂volume :=
    intervalIntegral.integral_nonneg hab fun x _ => sq_nonneg (u x)
  have hexpand : ∀ t : ℝ, ∫ x : ℝ in a..b, (u x + t * v x) ^ 2 ∂volume
      = (∫ x : ℝ in a..b, u x ^ 2 ∂volume)
        + (2 * t) * (∫ x : ℝ in a..b, u x * v x ∂volume)
        + (t * t) * (∫ x : ℝ in a..b, v x ^ 2 ∂volume) := by
    intro t
    have h1 : IntervalIntegrable (fun x : ℝ => u x ^ 2) volume a b :=
      huC.intervalIntegrable
    have h2 : IntervalIntegrable (fun x : ℝ => (2 * t) * (u x * v x)) volume a b :=
      (huvC.intervalIntegrable).const_mul _
    have h3 : IntervalIntegrable (fun x : ℝ => t * t * (v x ^ 2)) volume a b :=
      (hvC.intervalIntegrable).const_mul _
    have hsum : IntervalIntegrable
        (fun x : ℝ => u x ^ 2 + (2 * t) * (u x * v x)) volume a b :=
      h1.add h2
    have h4 : (fun x : ℝ => (u x + t * v x) ^ 2)
        = fun x : ℝ => u x ^ 2 + (2 * t) * (u x * v x) + t * t * (v x ^ 2) := by
      funext x
      ring
    rw [h4, intervalIntegral.integral_add hsum h3,
      intervalIntegral.integral_add h1 h2, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  have hnonneg : ∀ t : ℝ, 0 ≤ (∫ x : ℝ in a..b, u x ^ 2 ∂volume)
      + (2 * t) * (∫ x : ℝ in a..b, u x * v x ∂volume)
      + t * t * (∫ x : ℝ in a..b, v x ^ 2 ∂volume) := by
    intro t
    have h0 : (0 : ℝ) ≤ ∫ x : ℝ in a..b, (u x + t * v x) ^ 2 ∂volume :=
      intervalIntegral.integral_nonneg hab fun x _ => sq_nonneg _
    rw [hexpand t] at h0
    exact h0
  by_cases hAz : (∫ x : ℝ in a..b, v x ^ 2 ∂volume) = 0
  · have hB0 : (∫ x : ℝ in a..b, u x * v x ∂volume) = 0 := by
      by_contra hB
      have h1 := hnonneg (-((∫ x : ℝ in a..b, u x ^ 2 ∂volume) + 1)
        / (∫ x : ℝ in a..b, u x * v x ∂volume))
      rw [hAz] at h1
      simp only [mul_zero, add_zero] at h1
      -- h1 : 0 ≤ C + (2 * -((C+1)/B)) * B, a contradiction with C ≥ 0
      have h2 : (2 * (-((∫ x : ℝ in a..b, u x ^ 2 ∂volume) + 1)
          / (∫ x : ℝ in a..b, u x * v x ∂volume)))
          * (∫ x : ℝ in a..b, u x * v x ∂volume)
          = -((2 : ℝ) * ((∫ x : ℝ in a..b, u x ^ 2 ∂volume) + 1)) := by
        field_simp
      rw [h2] at h1
      linarith
    rw [hB0, hAz]
    simp
  · -- hAz : ¬(A = 0), which is `A ≠ 0` by definition
    have hApos : 0 < (∫ x : ℝ in a..b, v x ^ 2 ∂volume) :=
      lt_of_le_of_ne hA (Ne.symm hAz)
    have h1 := hnonneg (-((∫ x : ℝ in a..b, u x * v x ∂volume)
      / (∫ x : ℝ in a..b, v x ^ 2 ∂volume)))
    -- h1 : 0 ≤ (C + (2*T)*B) + (T*T)*A with T = -B/A; rewrite the FULL
    -- spliced shape (the leading C term groups with 2*T*B, so the h2
    -- pattern must include it) down to C - B^2/A.
    have h2 : (((∫ x : ℝ in a..b, u x ^ 2 ∂volume)
        + 2 * (-((∫ x : ℝ in a..b, u x * v x ∂volume)
          / (∫ x : ℝ in a..b, v x ^ 2 ∂volume)))
          * (∫ x : ℝ in a..b, u x * v x ∂volume))
        + (-((∫ x : ℝ in a..b, u x * v x ∂volume)
          / (∫ x : ℝ in a..b, v x ^ 2 ∂volume)))
          * (-((∫ x : ℝ in a..b, u x * v x ∂volume)
            / (∫ x : ℝ in a..b, v x ^ 2 ∂volume)))
          * (∫ x : ℝ in a..b, v x ^ 2 ∂volume))
      = (∫ x : ℝ in a..b, u x ^ 2 ∂volume)
        - (∫ x : ℝ in a..b, u x * v x ∂volume) ^ 2
          / (∫ x : ℝ in a..b, v x ^ 2 ∂volume) := by
      field_simp
      ring
    rw [h2] at h1
    have hBC : (∫ x : ℝ in a..b, v x ^ 2 ∂volume)
        * ((∫ x : ℝ in a..b, u x * v x ∂volume) ^ 2
          / (∫ x : ℝ in a..b, v x ^ 2 ∂volume))
        ≤ (∫ x : ℝ in a..b, v x ^ 2 ∂volume)
          * (∫ x : ℝ in a..b, u x ^ 2 ∂volume) :=
      mul_le_mul_of_nonneg_left (sub_nonneg.mp h1) hApos.le
    have hcan : (∫ x : ℝ in a..b, v x ^ 2 ∂volume)
        * ((∫ x : ℝ in a..b, u x * v x ∂volume) ^ 2
          / (∫ x : ℝ in a..b, v x ^ 2 ∂volume))
        = (∫ x : ℝ in a..b, u x * v x ∂volume) ^ 2 := by
      field_simp
    rw [hcan] at hBC
    linarith [mul_comm (∫ x : ℝ in a..b, u x ^ 2 ∂volume)
      (∫ x : ℝ in a..b, v x ^ 2 ∂volume)]

/-- The 1377 Lemma A bound: the Laplace evaluation is Cauchy-Schwarz-bounded
by the exact window antiderivative times the L2 norm. -/
theorem laplaceAt_sq_le (f : CompactLogTest) {a b : ℝ} (hab : a < b)
    (hsupp : Function.support f.test ⊆ Set.Ioo a b) (s : ℂ) :
    ‖laplaceAt f s‖ ^ 2 ≤
      (∫ x : ℝ in a..b, Real.exp (2 * s.re * x) ∂volume) * compactLogL2sq f := by
  -- step 1: triangle bound with the pointwise weight
  have htri : ‖laplaceAt f s‖ ≤
      ∫ x : ℝ, Real.exp (s.re * x) * ‖f.test x‖ ∂volume := by
    unfold laplaceAt
    have h0 : ‖∫ x : ℝ, ((exponentialWeight f s).test : ℝ → ℂ) x ∂volume‖
        ≤ ∫ x : ℝ, ‖((exponentialWeight f s).test : ℝ → ℂ) x‖ ∂volume :=
      MeasureTheory.norm_integral_le_integral_norm
        (f := fun x : ℝ => ((exponentialWeight f s).test x : ℂ))
    refine h0.trans ?_
    refine le_of_eq ?_
    refine MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall fun x => ?_)
    beta_reduce
    rw [exponentialWeight_apply, Complex.norm_mul, Complex.norm_exp]
    congr 1
    rw [Complex.mul_re]
    simp
  -- step 2: trim to the window
  have hout : ∀ x : ℝ, x ∉ Set.Ioo a b → ‖f.test x‖ = 0 := by
    intro x hx
    have hx0 : f.test x = 0 := by
      by_contra hnz
      exact hx (hsupp hnz)
    exact norm_eq_zero.mpr hx0
  have htrim : ∫ x : ℝ, Real.exp (s.re * x) * ‖f.test x‖ ∂volume
      = ∫ x : ℝ in a..b, Real.exp (s.re * x) * ‖f.test x‖ ∂volume := by
    rw [intervalIntegral.integral_of_le hab.le,
      ← MeasureTheory.integral_indicator measurableSet_Ioc]
    refine MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ Set.Ioc a b
    · simp [hx]
    · -- Ioc is left-open right-closed: a < x ∧ x ≤ b
      have hx' : x ∉ Set.Ioo a b := fun hxc => hx ⟨hxc.1, le_of_lt hxc.2⟩
      rw [Set.indicator_of_notMem hx]
      beta_reduce
      rw [hout x hx', mul_zero]
  -- step 3: Cauchy-Schwarz on the window and constant shaping
  have huC : ContinuousOn (fun x : ℝ => Real.exp (s.re * x)) (Set.uIcc a b) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
  have hvC : ContinuousOn (fun x : ℝ => ‖f.test x‖) (Set.uIcc a b) :=
    (f.test.smooth ⊤).continuous.norm.continuousOn
  have hcs := intervalIntegral_cauchySchwarz hab.le huC hvC
  have hsq : ∫ x : ℝ in a..b, Real.exp (s.re * x) ^ 2 ∂volume
      = ∫ x : ℝ in a..b, Real.exp (2 * s.re * x) ∂volume :=
    intervalIntegral.integral_congr_ae
      (Filter.Eventually.of_forall fun x _ => by
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring)
  have hl2 : ∫ x : ℝ in a..b, ‖f.test x‖ ^ 2 ∂volume
      = compactLogL2sq f := by
    unfold compactLogL2sq
    rw [intervalIntegral.integral_of_le hab.le,
      ← MeasureTheory.integral_indicator measurableSet_Ioc]
    refine MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ Set.Ioc a b
    · simp [hx]
    · -- Ioc is left-open right-closed: a < x ∧ x ≤ b
      have hx' : x ∉ Set.Ioo a b := fun hxc => hx ⟨hxc.1, le_of_lt hxc.2⟩
      rw [Set.indicator_of_notMem hx]
      beta_reduce
      rw [hout x hx']
      norm_num
  -- step 4: assemble
  have hsq2 : ‖laplaceAt f s‖ ^ 2
      ≤ (∫ x : ℝ in a..b, Real.exp (s.re * x) * ‖f.test x‖ ∂volume) ^ 2 := by
    have hint : 0 ≤ ∫ x : ℝ in a..b, Real.exp (s.re * x) * ‖f.test x‖ ∂volume :=
      intervalIntegral.integral_nonneg hab.le fun x _ =>
        mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
    nlinarith [htri, hint, norm_nonneg (laplaceAt f s)]
  calc ‖laplaceAt f s‖ ^ 2
      ≤ (∫ x : ℝ in a..b, Real.exp (s.re * x) * ‖f.test x‖ ∂volume) ^ 2 := hsq2
    _ ≤ (∫ x : ℝ in a..b, Real.exp (s.re * x) ^ 2 ∂volume)
        * (∫ x : ℝ in a..b, ‖f.test x‖ ^ 2 ∂volume) := hcs
    _ ≤ (∫ x : ℝ in a..b, Real.exp (2 * s.re * x) ∂volume) * compactLogL2sq f := by
      rw [hsq, hl2]

end C1CompactLogL2Export
end Source
end ConnesWeilRH
