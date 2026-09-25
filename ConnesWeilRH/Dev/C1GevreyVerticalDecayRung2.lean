/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/
import Mathlib
import ConnesWeilRH.Dev.C1GevreyVerticalDecay

/-!
# Gevrey window — brick 2, rung 2: two integration by parts, explicit constants

Rung 1 (`C1GevreyVerticalDecay`) landed the `1 / |w|` run.  This module lands
rung 2: the second integration by parts, boundary terms killed by
`gevreyDeriv k (±1) = 0` (brick 1), gives

* `laplace_abs_le_rung2`:
  `|∫_{-1}^{1} phi_k(u) e^{w u} du|
    ≤ e^{|Re w|} * (532 k² + 398 k) * e^{-k} / |w|²`;
* `laplace_abs_le_rung2_vertical`: at `w = a t I` the strip factor is `1`,
  so the bound is `(532 k² + 398 k) e^{-k} / (a |t|)²`.

Constant provenance (all checked against 40-dps numerics in the record
script): the outer pieces `[5/6, 1]`, `[-1, -5/6]` carry the EXACT total
variation `2160 k / 121 * e^{-36 k / 11}` — the split point `5/6` is the
largest rational `≤ 1` where `phi''` has a fixed sign for ALL `k ≥ 1`
(condition `s² + 4 s u² ≤ 2 k u²` with `s = 1 - u²`); the middle `|u| ≤ 5/6`
is bounded pointwise by `e^{-k} (22 k + 195 k + 319 k²)` (the exponential
cap is `e^{-k}`, attained at `u = 0`, NOT the edge value `e^{-36 k / 11}`).
Rungs `n ≥ 3` and the optimized-`n` sqrt law stay priced remainder.
-/

open Real Set Filter Topology MeasureTheory

private lemma sq_lt_one_of_abs_lt_one {u : ℝ} (h : |u| < 1) : u ^ 2 < 1 := by
  obtain ⟨h2, h3⟩ := abs_lt.mp h
  nlinarith [h2, h3]

/-- The interior second-derivative formula of `gevreyInner k`, extended by
`0`. -/
noncomputable def gevreyDeriv2 (k u : ℝ) : ℝ :=
  if |u| < 1 then
    Real.exp (-k / (1 - u ^ 2)) *
      (-2 * k / (1 - u ^ 2) ^ 2 + 4 * k ^ 2 * u ^ 2 / (1 - u ^ 2) ^ 4
        - 8 * k * u ^ 2 / (1 - u ^ 2) ^ 3)
  else 0

lemma gevreyDeriv2_of_abs_lt (k u : ℝ) (h : |u| < 1) :
    gevreyDeriv2 k u =
      Real.exp (-k / (1 - u ^ 2)) *
      (-2 * k / (1 - u ^ 2) ^ 2 + 4 * k ^ 2 * u ^ 2 / (1 - u ^ 2) ^ 4
        - 8 * k * u ^ 2 / (1 - u ^ 2) ^ 3) := by
  simp only [gevreyDeriv2, if_pos h]

lemma gevreyDeriv2_of_one_le_abs (k u : ℝ) (h : 1 ≤ |u|) :
    gevreyDeriv2 k u = 0 := by
  simp only [gevreyDeriv2, if_neg (not_lt.mpr h)]

lemma gevreyDeriv2_even (k u : ℝ) : gevreyDeriv2 k (-u) = gevreyDeriv2 k u := by
  rcases lt_or_ge (abs u) 1 with h | h
  · rw [gevreyDeriv2_of_abs_lt k (-u) (by rw [abs_neg]; exact h),
      gevreyDeriv2_of_abs_lt k u h]
    ring
  · rw [gevreyDeriv2_of_one_le_abs k (-u) (by rwa [abs_neg]),
      gevreyDeriv2_of_one_le_abs k u h]

/-- The chain rule: on the interior, `gevreyDeriv k` has derivative
`gevreyDeriv2 k`. -/
lemma gevreyDeriv_hasDerivAt_of_abs_lt (k u : ℝ) (hk : 0 < k) (h : |u| < 1) :
    HasDerivAt (gevreyDeriv k) (gevreyDeriv2 k u) u := by
  have hu2 : u ^ 2 < 1 := sq_lt_one_of_abs_lt_one h
  have hs : (0 : ℝ) < 1 - u ^ 2 := by linarith
  have hne : (1 : ℝ) - u ^ 2 ≠ 0 := ne_of_gt hs
  -- base: d/dv (1 - v^2) = -2 u at u
  have hsq : HasDerivAt (fun v : ℝ => (1 : ℝ) - v ^ 2) (-2 * u) u := by
    have h2 : HasDerivAt (fun v : ℝ => v * v) ((1 : ℝ) * u + u * 1) u :=
      HasDerivAt.mul (hasDerivAt_id u) (hasDerivAt_id u)
    rw [show ((1 : ℝ) * u + u * 1) = 2 * u from by ring] at h2
    have h3 : (fun v : ℝ => v * v) = fun v : ℝ => v ^ 2 := by funext v; ring
    rw [h3] at h2
    have h4 : HasDerivAt (fun v : ℝ => (1 : ℝ) - v ^ 2) ((0 : ℝ) - 2 * u) u :=
      HasDerivAt.sub (hasDerivAt_const u (1 : ℝ)) h2
    rwa [show ((0 : ℝ) - 2 * u) = -2 * u from by ring] at h4
  -- A(v) = -k / (1 - v^2),  A'(u) = -2 k u / (1 - u^2)^2
  have hA0 : HasDerivAt (fun v : ℝ => -k / (1 - v ^ 2))
      ((0 * (1 - u ^ 2) - -k * (-2 * u)) / (1 - u ^ 2) ^ 2) u :=
    HasDerivAt.div (hasDerivAt_const u (-k)) hsq hne
  have hAval : ((0 : ℝ) * (1 - u ^ 2) - -k * (-2 * u)) / (1 - u ^ 2) ^ 2
      = -2 * k * u / (1 - u ^ 2) ^ 2 := by
    ring
  rw [hAval] at hA0
  -- A''(u): d/dv of (-2 k v / (1 - v^2)^2)
  have hsq2 : HasDerivAt (fun v : ℝ => (1 - v ^ 2) * (1 - v ^ 2))
      ((-2 * u) * (1 - u ^ 2) + (1 - u ^ 2) * (-2 * u)) u := HasDerivAt.mul hsq hsq
  have hfe2 : (fun v : ℝ => (1 - v ^ 2) * (1 - v ^ 2))
      = fun v : ℝ => (1 - v ^ 2) ^ 2 := by
    funext v; ring
  rw [hfe2] at hsq2
  have hA20 : HasDerivAt (fun v : ℝ => -2 * k * v / (1 - v ^ 2) ^ 2)
      ((((-2 * k) * 1) * (1 - u ^ 2) ^ 2 - (-2 * k * u) *
        ((-2 * u) * (1 - u ^ 2) + (1 - u ^ 2) * (-2 * u)))
        / ((1 - u ^ 2) ^ 2) ^ 2) u :=
    HasDerivAt.div ((hasDerivAt_id u).const_mul (-2 * k)) hsq2 (pow_ne_zero 2 hne)
  have hA2val : ((((-2 * k) * 1) * (1 - u ^ 2) ^ 2 - (-2 * k * u) *
        ((-2 * u) * (1 - u ^ 2) + (1 - u ^ 2) * (-2 * u)))
        / ((1 - u ^ 2) ^ 2) ^ 2)
      = -2 * k / (1 - u ^ 2) ^ 2 - 8 * k * u ^ 2 / (1 - u ^ 2) ^ 3 := by
    field_simp
    ring
  rw [hA2val] at hA20
  -- (e^A)' = e^A * A'
  have hE1 : HasDerivAt (fun v : ℝ => Real.exp (-k / (1 - v ^ 2)))
      (Real.exp (-k / (1 - u ^ 2)) * (-2 * k * u / (1 - u ^ 2) ^ 2)) u := by
    simpa [Function.comp] using
      HasDerivAt.comp u (Real.hasDerivAt_exp (-k / (1 - u ^ 2))) hA0
  -- (e^A * A')' = e^A * (A'^2 + A'');  absorb the beta-applications by ascription
  have hmul : HasDerivAt (fun v : ℝ =>
        Real.exp (-k / (1 - v ^ 2)) * (-2 * k * v / (1 - v ^ 2) ^ 2))
      ((Real.exp (-k / (1 - u ^ 2)) * (-2 * k * u / (1 - u ^ 2) ^ 2)) *
          (-2 * k * u / (1 - u ^ 2) ^ 2)
        + Real.exp (-k / (1 - u ^ 2)) *
          (-2 * k / (1 - u ^ 2) ^ 2 - 8 * k * u ^ 2 / (1 - u ^ 2) ^ 3)) u :=
    HasDerivAt.mul hE1 hA20
  have hval2 : (Real.exp (-k / (1 - u ^ 2)) * (-2 * k * u / (1 - u ^ 2) ^ 2)) *
        (-2 * k * u / (1 - u ^ 2) ^ 2)
      + Real.exp (-k / (1 - u ^ 2)) *
        (-2 * k / (1 - u ^ 2) ^ 2 - 8 * k * u ^ 2 / (1 - u ^ 2) ^ 3)
      = Real.exp (-k / (1 - u ^ 2)) *
        (-2 * k / (1 - u ^ 2) ^ 2 + 4 * k ^ 2 * u ^ 2 / (1 - u ^ 2) ^ 4
          - 8 * k * u ^ 2 / (1 - u ^ 2) ^ 3) := by
    field_simp
    ring
  rw [hval2] at hmul
  -- rewrite the function into the brick-1 closed form and conclude by glue
  have hfe : (fun v : ℝ =>
        Real.exp (-k / (1 - v ^ 2)) * (-2 * k * v / (1 - v ^ 2) ^ 2))
      = fun v : ℝ =>
        Real.exp (-k / (1 - v ^ 2)) * (-k * (2 * v / (1 - v ^ 2) ^ 2)) := by
    funext v; ring
  rw [hfe] at hmul
  rw [gevreyDeriv2_of_abs_lt k u h]
  have hop : {v : ℝ | |v| < 1} ∈ 𝓝 u :=
    (isOpen_lt continuous_abs continuous_one).mem_nhds h
  have hev : (fun v : ℝ => gevreyDeriv k v) =ᶠ[𝓝 u]
      (fun v : ℝ => Real.exp (-k / (1 - v ^ 2)) * (-k * (2 * v / (1 - v ^ 2) ^ 2))) := by
    filter_upwards [hop] with v hv
    exact gevreyDeriv_of_abs_lt k v hv
  exact hmul.congr_of_eventuallyEq hev

/-- Master quartic-type bound for the second derivative (continuity glue). -/
lemma abs_gevreyDeriv2_le_quartic (k : ℝ) (hk : 0 < k) (u : ℝ) :
    |gevreyDeriv2 k u| ≤
      6 ^ 6 * (k ^ 5)⁻¹ *
        (2 * (1 - u ^ 2) ^ 4 + 4 * k * u ^ 2 * (1 - u ^ 2) ^ 2
          + 8 * u ^ 2 * |1 - u ^ 2| ^ 3) := by
  rcases lt_or_ge (abs u) 1 with h | h
  · have hu2 : u ^ 2 < 1 := sq_lt_one_of_abs_lt_one h
    have ht : 0 < 1 - u ^ 2 := by linarith
    have habs : |gevreyDeriv2 k u|
        = Real.exp (-k / (1 - u ^ 2)) *
          |(-2 * k / (1 - u ^ 2) ^ 2 + 4 * k ^ 2 * u ^ 2 / (1 - u ^ 2) ^ 4
            - 8 * k * u ^ 2 / (1 - u ^ 2) ^ 3)| := by
      rw [gevreyDeriv2_of_abs_lt k u h]
      simp only [abs_mul, abs_of_pos (Real.exp_pos _)]
    have htri : |(-2 * k / (1 - u ^ 2) ^ 2 + 4 * k ^ 2 * u ^ 2 / (1 - u ^ 2) ^ 4
          - 8 * k * u ^ 2 / (1 - u ^ 2) ^ 3)|
        ≤ 2 * k / (1 - u ^ 2) ^ 2 + 4 * k ^ 2 * u ^ 2 / (1 - u ^ 2) ^ 4
          + 8 * k * u ^ 2 / (1 - u ^ 2) ^ 3 := by
      have h1 : |(-2 * k / (1 - u ^ 2) ^ 2 + 4 * k ^ 2 * u ^ 2 / (1 - u ^ 2) ^ 4
            - 8 * k * u ^ 2 / (1 - u ^ 2) ^ 3)|
          ≤ |-2 * k / (1 - u ^ 2) ^ 2| + |4 * k ^ 2 * u ^ 2 / (1 - u ^ 2) ^ 4
            - 8 * k * u ^ 2 / (1 - u ^ 2) ^ 3| := by
        have h := abs_add_le (-2 * k / (1 - u ^ 2) ^ 2)
          (4 * k ^ 2 * u ^ 2 / (1 - u ^ 2) ^ 4 - 8 * k * u ^ 2 / (1 - u ^ 2) ^ 3)
        rwa [show (-2 * k / (1 - u ^ 2) ^ 2 + (4 * k ^ 2 * u ^ 2 / (1 - u ^ 2) ^ 4
              - 8 * k * u ^ 2 / (1 - u ^ 2) ^ 3))
            = -2 * k / (1 - u ^ 2) ^ 2 + 4 * k ^ 2 * u ^ 2 / (1 - u ^ 2) ^ 4
              - 8 * k * u ^ 2 / (1 - u ^ 2) ^ 3 from by ring] at h
      have h2 : |4 * k ^ 2 * u ^ 2 / (1 - u ^ 2) ^ 4
          - 8 * k * u ^ 2 / (1 - u ^ 2) ^ 3|
          ≤ |4 * k ^ 2 * u ^ 2 / (1 - u ^ 2) ^ 4|
            + |8 * k * u ^ 2 / (1 - u ^ 2) ^ 3| := by
        have h := abs_add_le (4 * k ^ 2 * u ^ 2 / (1 - u ^ 2) ^ 4)
          (-8 * k * u ^ 2 / (1 - u ^ 2) ^ 3)
        have hneg : (-8 : ℝ) * k * u ^ 2 / (1 - u ^ 2) ^ 3
            = -(8 * k * u ^ 2 / (1 - u ^ 2) ^ 3) := by ring
        rw [show (4 * k ^ 2 * u ^ 2 / (1 - u ^ 2) ^ 4
              + -8 * k * u ^ 2 / (1 - u ^ 2) ^ 3)
            = 4 * k ^ 2 * u ^ 2 / (1 - u ^ 2) ^ 4
              - 8 * k * u ^ 2 / (1 - u ^ 2) ^ 3 from by ring,
          hneg, abs_neg] at h
        exact h
      have ha1 : |-2 * k / (1 - u ^ 2) ^ 2| = 2 * k / (1 - u ^ 2) ^ 2 := by
        have hsign : (-2 : ℝ) * k / (1 - u ^ 2) ^ 2
            = -(2 * k / (1 - u ^ 2) ^ 2) := by ring
        rw [hsign, abs_neg]
        exact abs_of_nonneg (div_nonneg (by linarith) (pow_nonneg ht.le 2))
      have ha2 : |4 * k ^ 2 * u ^ 2 / (1 - u ^ 2) ^ 4|
          = 4 * k ^ 2 * u ^ 2 / (1 - u ^ 2) ^ 4 :=
        abs_of_nonneg (div_nonneg
          (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg k)) (sq_nonneg u))
          (pow_nonneg ht.le 4))
      have ha3 : |8 * k * u ^ 2 / (1 - u ^ 2) ^ 3| = 8 * k * u ^ 2 / (1 - u ^ 2) ^ 3 :=
        abs_of_nonneg (div_nonneg
          (mul_nonneg (by linarith) (sq_nonneg u)) (pow_nonneg ht.le 3))
      linarith
    have hstep : Real.exp (-k / (1 - u ^ 2))
        = (Real.exp (-k / (6 * (1 - u ^ 2)))) ^ 6 := by
      have h6 : (-k / (1 - u ^ 2)) = ((6 : ℕ) : ℝ) * (-k / (6 * (1 - u ^ 2))) := by
        norm_num
        field_simp
      rw [h6, Real.exp_nat_mul]
    have hle : Real.exp (-k / (6 * (1 - u ^ 2))) ≤ 6 * (1 - u ^ 2) / k :=
      exp_neg_div_le_div k hk _ (by linarith)
    calc |gevreyDeriv2 k u|
        = Real.exp (-k / (1 - u ^ 2)) *
          |(-2 * k / (1 - u ^ 2) ^ 2 + 4 * k ^ 2 * u ^ 2 / (1 - u ^ 2) ^ 4
            - 8 * k * u ^ 2 / (1 - u ^ 2) ^ 3)| := habs
      _ ≤ Real.exp (-k / (1 - u ^ 2)) * (2 * k / (1 - u ^ 2) ^ 2
            + 4 * k ^ 2 * u ^ 2 / (1 - u ^ 2) ^ 4
            + 8 * k * u ^ 2 / (1 - u ^ 2) ^ 3) := by
          exact mul_le_mul_of_nonneg_left htri (Real.exp_nonneg _)
      _ = (Real.exp (-k / (6 * (1 - u ^ 2)))) ^ 6 * (2 * k / (1 - u ^ 2) ^ 2
            + 4 * k ^ 2 * u ^ 2 / (1 - u ^ 2) ^ 4
            + 8 * k * u ^ 2 / (1 - u ^ 2) ^ 3) := by
          rw [hstep]
      _ ≤ (6 * (1 - u ^ 2) / k) ^ 6 * (2 * k / (1 - u ^ 2) ^ 2
            + 4 * k ^ 2 * u ^ 2 / (1 - u ^ 2) ^ 4
            + 8 * k * u ^ 2 / (1 - u ^ 2) ^ 3) := by
          exact mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ (Real.exp_nonneg _) hle 6) (by positivity)
      _ = 6 ^ 6 * (k ^ 5)⁻¹ *
            (2 * (1 - u ^ 2) ^ 4 + 4 * k * u ^ 2 * (1 - u ^ 2) ^ 2
              + 8 * u ^ 2 * |1 - u ^ 2| ^ 3) := by
          rw [abs_of_pos ht]
          field_simp
  · have hk5 : (0 : ℝ) ≤ (k ^ 5)⁻¹ := inv_nonneg.mpr (pow_nonneg hk.le 5)
    rw [gevreyDeriv2_of_one_le_abs k u h, abs_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) hk5) (by positivity)

lemma continuous_gevreyDeriv2 (k : ℝ) (hk : 0 < k) : Continuous (gevreyDeriv2 k) := by
  rw [continuous_iff_continuousAt]
  intro u
  rcases lt_trichotomy (abs u) 1 with h | h | h
  · have hden : ContinuousAt (fun v : ℝ => 1 - v ^ 2) u := by fun_prop
    have hu2 : u ^ 2 < 1 := sq_lt_one_of_abs_lt_one h
    have hne : (1 : ℝ) - u ^ 2 ≠ 0 := by linarith
    have h3a : ContinuousAt (fun v : ℝ => -2 * k / (1 - v ^ 2) ^ 2) u :=
      ContinuousAt.div continuousAt_const (hden.pow 2)
        (pow_ne_zero 2 hne)
    have h3b : ContinuousAt (fun v : ℝ => 4 * k ^ 2 * v ^ 2 / (1 - v ^ 2) ^ 4) u :=
      ContinuousAt.div (by fun_prop) (hden.pow 4) (pow_ne_zero 4 hne)
    have h3c : ContinuousAt (fun v : ℝ => 8 * k * v ^ 2 / (1 - v ^ 2) ^ 3) u :=
      ContinuousAt.div (by fun_prop) (hden.pow 3) (pow_ne_zero 3 hne)
    have h3 : ContinuousAt (fun v : ℝ =>
        (-2 * k / (1 - v ^ 2) ^ 2 + 4 * k ^ 2 * v ^ 2 / (1 - v ^ 2) ^ 4
          - 8 * k * v ^ 2 / (1 - v ^ 2) ^ 3)) u := (h3a.add h3b).sub h3c
    have h2 : ContinuousAt (fun v : ℝ => Real.exp (-k / (1 - v ^ 2))) u :=
      Real.continuous_exp.continuousAt.comp
        (continuousAt_const.div hden hne)
    have hform : ContinuousAt (fun v : ℝ =>
        Real.exp (-k / (1 - v ^ 2)) *
        (-2 * k / (1 - v ^ 2) ^ 2 + 4 * k ^ 2 * v ^ 2 / (1 - v ^ 2) ^ 4
          - 8 * k * v ^ 2 / (1 - v ^ 2) ^ 3)) u :=
      h2.mul h3
    have hev : (fun v : ℝ => gevreyDeriv2 k v) =ᶠ[𝓝 u] (fun v : ℝ =>
        Real.exp (-k / (1 - v ^ 2)) *
        (-2 * k / (1 - v ^ 2) ^ 2 + 4 * k ^ 2 * v ^ 2 / (1 - v ^ 2) ^ 4
          - 8 * k * v ^ 2 / (1 - v ^ 2) ^ 3)) := by
      have hop : {v : ℝ | |v| < 1} ∈ 𝓝 u :=
        (isOpen_lt continuous_abs continuous_one).mem_nhds h
      filter_upwards [hop] with v hv
      exact gevreyDeriv2_of_abs_lt k v hv
    rw [ContinuousAt, gevreyDeriv2_of_abs_lt k u h]
    exact hform.congr' hev.symm
  · have hu2 : u ^ 2 = 1 := by
      have hsq := sq_abs u
      rw [h] at hsq
      linarith
    have hz : Tendsto (fun v : ℝ => 6 ^ 6 * (k ^ 5)⁻¹ *
        (2 * (1 - v ^ 2) ^ 4 + 4 * k * v ^ 2 * (1 - v ^ 2) ^ 2
          + 8 * v ^ 2 * |1 - v ^ 2| ^ 3)) (𝓝 u) (𝓝 0) := by
      have hc4 : Continuous (fun v : ℝ => 6 ^ 6 * (k ^ 5)⁻¹ *
        (2 * (1 - v ^ 2) ^ 4 + 4 * k * v ^ 2 * (1 - v ^ 2) ^ 2
          + 8 * v ^ 2 * |1 - v ^ 2| ^ 3)) := by
        fun_prop
      have h1 := hc4.tendsto u
      rw [hu2] at h1
      simpa using h1
    have hzero : gevreyDeriv2 k u = 0 := gevreyDeriv2_of_one_le_abs k u h.ge
    rw [ContinuousAt, hzero]
    have hneg : Tendsto (fun v : ℝ => -(6 ^ 6 * (k ^ 5)⁻¹ *
        (2 * (1 - v ^ 2) ^ 4 + 4 * k * v ^ 2 * (1 - v ^ 2) ^ 2
          + 8 * v ^ 2 * |1 - v ^ 2| ^ 3))) (𝓝 u) (𝓝 0) := by
      simpa using hz.neg
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hneg hz
      (Filter.Eventually.of_forall fun v =>
        (abs_le.mp (abs_gevreyDeriv2_le_quartic k hk v)).1)
      (Filter.Eventually.of_forall fun v =>
        (abs_le.mp (abs_gevreyDeriv2_le_quartic k hk v)).2)
  · have hopen : {v : ℝ | 1 < |v|} ∈ 𝓝 u :=
      (isOpen_lt continuous_const continuous_abs).mem_nhds h
    have hev : (fun v : ℝ => gevreyDeriv2 k v) =ᶠ[𝓝 u] (fun _ : ℝ => (0 : ℝ)) := by
      filter_upwards [hopen] with v hv
      exact gevreyDeriv2_of_one_le_abs k v (le_of_lt hv)
    have hzero : gevreyDeriv2 k u = 0 := gevreyDeriv2_of_one_le_abs k u h.le
    rw [ContinuousAt, hzero]
    exact tendsto_const_nhds.congr' hev.symm

lemma intervalIntegrable_gevreyDeriv2 (k : ℝ) (hk : 0 < k) (a b : ℝ) :
    IntervalIntegrable (gevreyDeriv2 k) volume a b :=
  (continuous_gevreyDeriv2 k hk).continuousOn.intervalIntegrable (μ := volume)

/-- On `[5/6, 1]` the second derivative is nonnegative: the sign condition
`s² + 4 s u² ≤ 2 k u²` holds on the whole arc for every `k ≥ 1`. -/
lemma gevreyDeriv2_nonneg_of_mem_Icc_right (k : ℝ) (hk : 1 ≤ k) (u : ℝ)
    (h : u ∈ Icc ((5 : ℝ) / 6) 1) : 0 ≤ gevreyDeriv2 k u := by
  obtain ⟨hlow, hhigh⟩ := h
  by_cases h1 : u = 1
  · subst h1
    rw [gevreyDeriv2_of_one_le_abs k 1 abs_one.ge]
  · have hu1 : u < 1 := lt_of_le_of_ne hhigh h1
    have ha : |u| < 1 := abs_lt.mpr ⟨by linarith, hu1⟩
    have hsq5 : (25 : ℝ) / 36 ≤ u ^ 2 := by nlinarith
    have hu2lt : u ^ 2 < 1 := by nlinarith [hlow, hu1]
    have hupp : (0 : ℝ) < 1 - u ^ 2 := by linarith
    have hs36 : (1 : ℝ) - u ^ 2 ≤ 11 / 36 := by linarith
    have hs36b : (11 : ℝ) / 36 ≤ u ^ 2 := by linarith
    have hp1 : (1 - u ^ 2) ^ 2 ≤ (11 / 36) * u ^ 2 := by
      have hstep : ((11 : ℝ) / 36) * (11 / 36) ≤ (11 / 36) * u ^ 2 :=
        mul_le_mul_of_nonneg_left hs36b (by norm_num)
      calc (1 - u ^ 2) ^ 2 ≤ (11 / 36) ^ 2 := pow_le_pow_left₀ hupp.le hs36 2
        _ = (11 / 36) * (11 / 36) := by ring
        _ ≤ (11 / 36) * u ^ 2 := hstep
    have hp2 : 4 * (1 - u ^ 2) * u ^ 2 ≤ (44 / 36) * u ^ 2 := by
      have hb : (4 : ℝ) * (1 - u ^ 2) ≤ 44 / 36 := by linarith
      exact mul_le_mul_of_nonneg_right hb (sq_nonneg u)
    have hkey : (1 - u ^ 2) ^ 2 + 4 * (1 - u ^ 2) * u ^ 2 ≤ 2 * k * u ^ 2 := by
      have h55 : (55 : ℝ) / 36 ≤ 2 * k := by linarith
      calc (1 - u ^ 2) ^ 2 + 4 * (1 - u ^ 2) * u ^ 2
          ≤ (11 / 36) * u ^ 2 + (44 / 36) * u ^ 2 := by linarith [hp1, hp2]
        _ ≤ 2 * k * u ^ 2 := by
            have h5 := mul_le_mul_of_nonneg_right h55 (sq_nonneg u)
            rwa [show ((55 : ℝ) / 36) * u ^ 2
              = (11 / 36) * u ^ 2 + (44 / 36) * u ^ 2 from by ring] at h5
    have hbrac : (0 : ℝ) ≤ -2 * k * (1 - u ^ 2) ^ 2 + 4 * k ^ 2 * u ^ 2
        - 8 * k * u ^ 2 * (1 - u ^ 2) := by
      have hm := mul_le_mul_of_nonneg_left hkey (by linarith : (0 : ℝ) ≤ 2 * k)
      rw [show ((2 : ℝ) * k * ((1 - u ^ 2) ^ 2 + 4 * (1 - u ^ 2) * u ^ 2)
          = 2 * k * (1 - u ^ 2) ^ 2 + 8 * k * (1 - u ^ 2) * u ^ 2) from by ring,
        show ((2 : ℝ) * k * (2 * k * u ^ 2) = 4 * k ^ 2 * u ^ 2) from by ring] at hm
      linarith
    have hs4pos : (0 : ℝ) < (1 - u ^ 2) ^ 4 := pow_pos hupp 4
    have hBpos : 0 ≤ -2 * k / (1 - u ^ 2) ^ 2 + 4 * k ^ 2 * u ^ 2 / (1 - u ^ 2) ^ 4
        - 8 * k * u ^ 2 / (1 - u ^ 2) ^ 3 := by
      have hB4 : (-2 * k / (1 - u ^ 2) ^ 2 + 4 * k ^ 2 * u ^ 2 / (1 - u ^ 2) ^ 4
            - 8 * k * u ^ 2 / (1 - u ^ 2) ^ 3) * (1 - u ^ 2) ^ 4
          = -2 * k * (1 - u ^ 2) ^ 2 + 4 * k ^ 2 * u ^ 2
            - 8 * k * u ^ 2 * (1 - u ^ 2) := by
        field_simp
      have hprod0 : (0 : ℝ) ≤ (-2 * k / (1 - u ^ 2) ^ 2
            + 4 * k ^ 2 * u ^ 2 / (1 - u ^ 2) ^ 4
            - 8 * k * u ^ 2 / (1 - u ^ 2) ^ 3) * (1 - u ^ 2) ^ 4 := by
        rw [hB4]
        exact hbrac
      have hrepr : (-2 * k / (1 - u ^ 2) ^ 2 + 4 * k ^ 2 * u ^ 2 / (1 - u ^ 2) ^ 4
            - 8 * k * u ^ 2 / (1 - u ^ 2) ^ 3) * (1 - u ^ 2) ^ 4 / (1 - u ^ 2) ^ 4
          = -2 * k / (1 - u ^ 2) ^ 2 + 4 * k ^ 2 * u ^ 2 / (1 - u ^ 2) ^ 4
            - 8 * k * u ^ 2 / (1 - u ^ 2) ^ 3 := by
        field_simp
      rw [← hrepr]
      exact div_nonneg hprod0 hs4pos.le
    rw [gevreyDeriv2_of_abs_lt k u ha]
    exact mul_nonneg (Real.exp_nonneg _) hBpos

/-- On `[-1, -5/6]` the second derivative is nonnegative (evenness). -/
lemma gevreyDeriv2_nonneg_of_mem_Icc_left (k : ℝ) (hk : 1 ≤ k) (u : ℝ)
    (h : u ∈ Icc (-1 : ℝ) (-(5 : ℝ) / 6)) : 0 ≤ gevreyDeriv2 k u := by
  obtain ⟨hlow, hhigh⟩ := h
  rw [← gevreyDeriv2_even k u]
  exact gevreyDeriv2_nonneg_of_mem_Icc_right k hk (-u) ⟨by linarith, by linarith⟩

/-- Exact total variation on the right outer piece. -/
lemma integral_abs_gevreyDeriv2_outer_right (k : ℝ) (hk : 1 ≤ k) :
    ∫ u in ((5 : ℝ) / 6)..1, |gevreyDeriv2 k u|
      = 2160 * k / 121 * Real.exp (-36 * k / 11) := by
  have hkn : (0 : ℝ) < k := by linarith
  have hcongr : ∫ u in ((5 : ℝ) / 6)..1, |gevreyDeriv2 k u|
      = ∫ u in ((5 : ℝ) / 6)..1, gevreyDeriv2 k u := by
    refine intervalIntegral.integral_congr (fun u hu => ?_)
    simp only [mem_uIcc] at hu
    rcases hu with h | h
    · rw [abs_of_nonneg (gevreyDeriv2_nonneg_of_mem_Icc_right k hk u ⟨h.1, h.2⟩)]
    · have hueq : u = 1 := le_antisymm (by linarith) h.1
      subst hueq
      rw [gevreyDeriv2_of_one_le_abs k 1 abs_one.ge, abs_zero]
  have hint : IntervalIntegrable (gevreyDeriv2 k) volume ((5 : ℝ) / 6) 1 :=
    intervalIntegrable_gevreyDeriv2 k hkn _ _
  have hcont : ContinuousOn (gevreyDeriv k) (Icc ((5 : ℝ) / 6) 1) :=
    (continuous_gevreyDeriv k hkn).continuousOn
  have hderiv : ∀ x ∈ Ioo ((5 : ℝ) / 6) 1,
      HasDerivAt (gevreyDeriv k) (gevreyDeriv2 k x) x := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := hx
    have hx' : |x| < 1 := abs_lt.mpr ⟨by linarith, by linarith⟩
    exact gevreyDeriv_hasDerivAt_of_abs_lt k x hkn hx'
  have hftc : ∫ u in ((5 : ℝ) / 6)..1, gevreyDeriv2 k u
      = gevreyDeriv k 1 - gevreyDeriv k ((5 : ℝ) / 6) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num) hcont hderiv hint
  have hv1 : gevreyDeriv k 1 = 0 := gevreyDeriv_of_one_le_abs k 1 abs_one.ge
  have hv2 : gevreyDeriv k ((5 : ℝ) / 6) = -2160 * k / 121 * Real.exp (-36 * k / 11) := by
    have hab : |(5 : ℝ) / 6| < 1 := by norm_num
    have hexp : Real.exp (-k / (1 - (5 / 6 : ℝ) ^ 2)) = Real.exp (-36 * k / 11) := by
      refine congrArg Real.exp ?_
      field_simp
      ring
    have hbr : -k * (2 * (5 / 6 : ℝ) / (1 - (5 / 6 : ℝ) ^ 2) ^ 2)
        = -2160 * k / 121 := by
      have hr : (2 * (5 / 6 : ℝ) / (1 - (5 / 6 : ℝ) ^ 2) ^ 2) = 2160 / 121 := by
        norm_num
      rw [hr]
      ring
    rw [gevreyDeriv_of_abs_lt k (5 / 6) hab, hexp, hbr]
    ring
  rw [hcongr, hftc, hv1, hv2]
  ring

/-- Exact total variation on the left outer piece. -/
lemma integral_abs_gevreyDeriv2_outer_left (k : ℝ) (hk : 1 ≤ k) :
    ∫ u in (-1 : ℝ)..(-(5 : ℝ) / 6), |gevreyDeriv2 k u|
      = 2160 * k / 121 * Real.exp (-36 * k / 11) := by
  have hkn : (0 : ℝ) < k := by linarith
  have hcongr : ∫ u in (-1 : ℝ)..(-(5 : ℝ) / 6), |gevreyDeriv2 k u|
      = ∫ u in (-1 : ℝ)..(-(5 : ℝ) / 6), gevreyDeriv2 k u := by
    refine intervalIntegral.integral_congr (fun u hu => ?_)
    simp only [mem_uIcc] at hu
    rcases hu with h | h
    · rw [abs_of_nonneg (gevreyDeriv2_nonneg_of_mem_Icc_left k hk u ⟨h.1, h.2⟩)]
    · have hueq : u = -1 := le_antisymm h.2 (by linarith)
      subst hueq
      rw [gevreyDeriv2_of_one_le_abs k (-1) (by simp), abs_zero]
  have hint : IntervalIntegrable (gevreyDeriv2 k) volume (-1 : ℝ) (-(5 : ℝ) / 6) :=
    intervalIntegrable_gevreyDeriv2 k hkn _ _
  have hcont : ContinuousOn (gevreyDeriv k) (Icc (-1 : ℝ) (-(5 : ℝ) / 6)) :=
    (continuous_gevreyDeriv k hkn).continuousOn
  have hderiv : ∀ x ∈ Ioo (-1 : ℝ) (-(5 : ℝ) / 6),
      HasDerivAt (gevreyDeriv k) (gevreyDeriv2 k x) x := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := hx
    have hx' : |x| < 1 := abs_lt.mpr ⟨by linarith, by linarith⟩
    exact gevreyDeriv_hasDerivAt_of_abs_lt k x hkn hx'
  have hftc : ∫ u in (-1 : ℝ)..(-(5 : ℝ) / 6), gevreyDeriv2 k u
      = gevreyDeriv k (-(5 : ℝ) / 6) - gevreyDeriv k (-1) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num) hcont hderiv hint
  have hv1 : gevreyDeriv k (-1) = 0 := gevreyDeriv_of_one_le_abs k (-1) (by simp)
  have hv2 : gevreyDeriv k (-(5 : ℝ) / 6) = 2160 * k / 121 * Real.exp (-36 * k / 11) := by
    have hab : |-(5 : ℝ) / 6| < 1 := by norm_num
    have hexp : Real.exp (-k / (1 - (-(5 : ℝ) / 6) ^ 2)) = Real.exp (-36 * k / 11) := by
      refine congrArg Real.exp ?_
      field_simp
      ring
    have hbr : -k * (2 * (-(5 : ℝ) / 6) / (1 - (-(5 : ℝ) / 6) ^ 2) ^ 2)
        = 2160 * k / 121 := by
      have hr : (2 * (-(5 : ℝ) / 6) / (1 - (-(5 : ℝ) / 6) ^ 2) ^ 2) = -2160 / 121 := by
        norm_num
      rw [hr]
      ring
    rw [gevreyDeriv_of_abs_lt k (-(5 : ℝ) / 6) hab, hexp, hbr]
    ring
  rw [hcongr, hftc, hv2, hv1]
  ring

/-- Pointwise middle bound: the exponential cap is `e^{-k}` (attained at
`u = 0`), not the edge value. -/
lemma abs_gevreyDeriv2_le_mid (k : ℝ) (hk : 1 ≤ k) (u : ℝ) (hu : |u| ≤ 5 / 6) :
    |gevreyDeriv2 k u| ≤ Real.exp (-k) * (22 * k + 195 * k + 319 * k ^ 2) := by
  have hk' : (0 : ℝ) < k := by linarith
  have h1 : |u| < 1 := lt_of_le_of_lt hu (by norm_num)
  have hu2 : u ^ 2 < 1 := sq_lt_one_of_abs_lt_one h1
  have ht : 0 < 1 - u ^ 2 := by linarith
  have hsq5 : u ^ 2 ≤ 25 / 36 := by
    obtain ⟨hlo, hhi⟩ := abs_le.mp hu
    nlinarith [hlo, hhi]
  have hs36 : (11 : ℝ) / 36 ≤ 1 - u ^ 2 := by linarith
  have habs : |gevreyDeriv2 k u|
      = Real.exp (-k / (1 - u ^ 2)) *
        |(-2 * k / (1 - u ^ 2) ^ 2 + 4 * k ^ 2 * u ^ 2 / (1 - u ^ 2) ^ 4
          - 8 * k * u ^ 2 / (1 - u ^ 2) ^ 3)| := by
    rw [gevreyDeriv2_of_abs_lt k u h1]
    simp only [abs_mul, abs_of_pos (Real.exp_pos _)]
  have htri : |(-2 * k / (1 - u ^ 2) ^ 2 + 4 * k ^ 2 * u ^ 2 / (1 - u ^ 2) ^ 4
        - 8 * k * u ^ 2 / (1 - u ^ 2) ^ 3)|
      ≤ 2 * k / (1 - u ^ 2) ^ 2 + 4 * k ^ 2 * u ^ 2 / (1 - u ^ 2) ^ 4
        + 8 * k * u ^ 2 / (1 - u ^ 2) ^ 3 := by
    have h1 : |(-2 * k / (1 - u ^ 2) ^ 2 + 4 * k ^ 2 * u ^ 2 / (1 - u ^ 2) ^ 4
          - 8 * k * u ^ 2 / (1 - u ^ 2) ^ 3)|
        ≤ |-2 * k / (1 - u ^ 2) ^ 2| + |4 * k ^ 2 * u ^ 2 / (1 - u ^ 2) ^ 4
          - 8 * k * u ^ 2 / (1 - u ^ 2) ^ 3| := by
      have h := abs_add_le (-2 * k / (1 - u ^ 2) ^ 2)
        (4 * k ^ 2 * u ^ 2 / (1 - u ^ 2) ^ 4 - 8 * k * u ^ 2 / (1 - u ^ 2) ^ 3)
      rwa [show (-2 * k / (1 - u ^ 2) ^ 2 + (4 * k ^ 2 * u ^ 2 / (1 - u ^ 2) ^ 4
            - 8 * k * u ^ 2 / (1 - u ^ 2) ^ 3))
          = -2 * k / (1 - u ^ 2) ^ 2 + 4 * k ^ 2 * u ^ 2 / (1 - u ^ 2) ^ 4
            - 8 * k * u ^ 2 / (1 - u ^ 2) ^ 3 from by ring] at h
    have h2 : |4 * k ^ 2 * u ^ 2 / (1 - u ^ 2) ^ 4
        - 8 * k * u ^ 2 / (1 - u ^ 2) ^ 3|
        ≤ |4 * k ^ 2 * u ^ 2 / (1 - u ^ 2) ^ 4|
          + |8 * k * u ^ 2 / (1 - u ^ 2) ^ 3| := by
      have h := abs_add_le (4 * k ^ 2 * u ^ 2 / (1 - u ^ 2) ^ 4)
        (-8 * k * u ^ 2 / (1 - u ^ 2) ^ 3)
      have hneg : (-8 : ℝ) * k * u ^ 2 / (1 - u ^ 2) ^ 3
          = -(8 * k * u ^ 2 / (1 - u ^ 2) ^ 3) := by ring
      rw [show (4 * k ^ 2 * u ^ 2 / (1 - u ^ 2) ^ 4
            + -8 * k * u ^ 2 / (1 - u ^ 2) ^ 3)
          = 4 * k ^ 2 * u ^ 2 / (1 - u ^ 2) ^ 4
            - 8 * k * u ^ 2 / (1 - u ^ 2) ^ 3 from by ring,
        hneg, abs_neg] at h
      exact h
    have ha1 : |-2 * k / (1 - u ^ 2) ^ 2| = 2 * k / (1 - u ^ 2) ^ 2 := by
      have hsign : (-2 : ℝ) * k / (1 - u ^ 2) ^ 2
          = -(2 * k / (1 - u ^ 2) ^ 2) := by ring
      rw [hsign, abs_neg]
      exact abs_of_nonneg (div_nonneg (by linarith) (pow_nonneg ht.le 2))
    have ha2 : |4 * k ^ 2 * u ^ 2 / (1 - u ^ 2) ^ 4|
        = 4 * k ^ 2 * u ^ 2 / (1 - u ^ 2) ^ 4 :=
      abs_of_nonneg (div_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg k)) (sq_nonneg u))
        (pow_nonneg ht.le 4))
    have ha3 : |8 * k * u ^ 2 / (1 - u ^ 2) ^ 3| = 8 * k * u ^ 2 / (1 - u ^ 2) ^ 3 :=
      abs_of_nonneg (div_nonneg
        (mul_nonneg (by linarith) (sq_nonneg u)) (pow_nonneg ht.le 3))
    linarith
  have hexp : Real.exp (-k / (1 - u ^ 2)) ≤ Real.exp (-k) := by
    refine Real.exp_le_exp.mpr ?_
    have h2 : (1 : ℝ) - u ^ 2 ≤ 1 := by linarith [sq_nonneg u]
    have h3 : k * (1 - u ^ 2) ≤ k * 1 := mul_le_mul_of_nonneg_left h2 hk'.le
    rw [mul_one] at h3
    have h4 : (-k / (1 - u ^ 2)) ≤ -k := by
      rw [div_le_iff₀ ht]
      linarith
    linarith
  have hterm1 : 2 * k / (1 - u ^ 2) ^ 2 ≤ 22 * k := by
    have h22 : (2 : ℝ) ≤ 22 * (1 - u ^ 2) ^ 2 := by
      have h3611 : (2 : ℝ) ≤ 22 * (11 / 36) ^ 2 := by norm_num
      calc (2 : ℝ) ≤ 22 * (11 / 36) ^ 2 := h3611
        _ ≤ 22 * (1 - u ^ 2) ^ 2 := by
            refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
            exact pow_le_pow_left₀ (by norm_num) hs36 2
    have h2 : (2 : ℝ) * k ≤ 22 * k * (1 - u ^ 2) ^ 2 := by
      calc 2 * k = k * 2 := by ring
        _ ≤ k * (22 * (1 - u ^ 2) ^ 2) := mul_le_mul_of_nonneg_left h22 hk'.le
        _ = 22 * k * (1 - u ^ 2) ^ 2 := by ring
    rw [div_le_iff₀ (pow_pos ht 2)]
    exact h2
  have hterm2 : 4 * k ^ 2 * u ^ 2 / (1 - u ^ 2) ^ 4 ≤ 319 * k ^ 2 := by
    have hstep1 : (4 : ℝ) * u ^ 2 ≤ 4 * (25 / 36) :=
      mul_le_mul_of_nonneg_left hsq5 (by norm_num)
    have hstep2 : (4 : ℝ) * (25 / 36) ≤ 319 * (11 / 36) ^ 4 := by norm_num
    have hstep3 : (319 : ℝ) * (11 / 36) ^ 4 ≤ 319 * (1 - u ^ 2) ^ 4 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) hs36 4) (by norm_num)
    have htot : (4 : ℝ) * u ^ 2 ≤ 319 * (1 - u ^ 2) ^ 4 :=
      le_trans (le_trans hstep1 hstep2) hstep3
    have hksq : (4 : ℝ) * k ^ 2 * u ^ 2 ≤ k ^ 2 * (319 * (1 - u ^ 2) ^ 4) := by
      calc 4 * k ^ 2 * u ^ 2 = k ^ 2 * (4 * u ^ 2) := by ring
        _ ≤ k ^ 2 * (319 * (1 - u ^ 2) ^ 4) :=
            mul_le_mul_of_nonneg_left htot (sq_nonneg k)
    rw [div_le_iff₀ (pow_pos ht 4)]
    linarith [hksq]
  have hterm3 : 8 * k * u ^ 2 / (1 - u ^ 2) ^ 3 ≤ 195 * k := by
    have hstep1 : (8 : ℝ) * u ^ 2 ≤ 8 * (25 / 36) :=
      mul_le_mul_of_nonneg_left hsq5 (by norm_num)
    have hstep2 : (8 : ℝ) * (25 / 36) ≤ 195 * (11 / 36) ^ 3 := by norm_num
    have hstep3 : (195 : ℝ) * (11 / 36) ^ 3 ≤ 195 * (1 - u ^ 2) ^ 3 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) hs36 3) (by norm_num)
    have htot : (8 : ℝ) * u ^ 2 ≤ 195 * (1 - u ^ 2) ^ 3 :=
      le_trans (le_trans hstep1 hstep2) hstep3
    rw [div_le_iff₀ (pow_pos ht 3)]
    calc 8 * k * u ^ 2 = k * (8 * u ^ 2) := by ring
      _ ≤ k * (195 * (1 - u ^ 2) ^ 3) := mul_le_mul_of_nonneg_left htot hk'.le
      _ = 195 * k * (1 - u ^ 2) ^ 3 := by ring
  calc |gevreyDeriv2 k u|
      = Real.exp (-k / (1 - u ^ 2)) *
        |(-2 * k / (1 - u ^ 2) ^ 2 + 4 * k ^ 2 * u ^ 2 / (1 - u ^ 2) ^ 4
          - 8 * k * u ^ 2 / (1 - u ^ 2) ^ 3)| := habs
    _ ≤ Real.exp (-k / (1 - u ^ 2)) * (2 * k / (1 - u ^ 2) ^ 2
          + 4 * k ^ 2 * u ^ 2 / (1 - u ^ 2) ^ 4
          + 8 * k * u ^ 2 / (1 - u ^ 2) ^ 3) := by
        exact mul_le_mul_of_nonneg_left htri (Real.exp_nonneg _)
    _ ≤ Real.exp (-k) * (22 * k + 195 * k + 319 * k ^ 2) := by
        have hS : (2 * k / (1 - u ^ 2) ^ 2 + 4 * k ^ 2 * u ^ 2 / (1 - u ^ 2) ^ 4
            + 8 * k * u ^ 2 / (1 - u ^ 2) ^ 3)
            ≤ 22 * k + 195 * k + 319 * k ^ 2 := by
          linarith
        exact mul_le_mul hexp hS (by positivity) (Real.exp_nonneg _)

/-- Total `L¹` mass of the second derivative. -/
lemma integral_abs_gevreyDeriv2_le (k : ℝ) (hk : 1 ≤ k) :
    ∫ u in (-1 : ℝ)..1, |gevreyDeriv2 k u|
      ≤ Real.exp (-k) * (532 * k ^ 2 + 398 * k) := by
  have hk' : (0 : ℝ) < k := by linarith
  have hc : ∀ a b : ℝ, IntervalIntegrable (fun u => |gevreyDeriv2 k u|) volume a b :=
    fun a b => (continuous_gevreyDeriv2 k hk').abs.intervalIntegrable (μ := volume) a b
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc (-1) (-(5 : ℝ) / 6))
      (hc (-(5 : ℝ) / 6) 1),
    ← intervalIntegral.integral_add_adjacent_intervals (hc (-(5 : ℝ) / 6) ((5 : ℝ) / 6))
      (hc ((5 : ℝ) / 6) 1),
    integral_abs_gevreyDeriv2_outer_left k hk, integral_abs_gevreyDeriv2_outer_right k hk]
  set C2 : ℝ := Real.exp (-k) * (22 * k + 195 * k + 319 * k ^ 2) with hC2def
  have hcst : IntervalIntegrable (fun _ : ℝ => C2) volume (-(5 : ℝ) / 6) ((5 : ℝ) / 6) :=
    (continuous_const : Continuous (fun _ : ℝ => C2)).intervalIntegrable (μ := volume) _ _
  have hmid := intervalIntegral.integral_mono_on
    (by norm_num : (-(5 : ℝ) / 6) ≤ (5 : ℝ) / 6)
    (hc (-(5 : ℝ) / 6) ((5 : ℝ) / 6))
    hcst
    (fun x hx => by
      simp only [mem_Icc] at hx
      rw [hC2def]
      exact abs_gevreyDeriv2_le_mid k hk x (abs_le.mpr ⟨by linarith, by linarith⟩))
  have hconstval : ∫ u in (-(5 : ℝ) / 6)..((5 : ℝ) / 6), C2 = C2 * (5 / 3) := by
    rw [intervalIntegral.integral_const]
    ring
  rw [hconstval] at hmid
  have hAB : Real.exp (-36 * k / 11) ≤ Real.exp (-k) := by
    refine Real.exp_le_exp.mpr ?_
    linarith
  have hout : 2160 * k / 121 * Real.exp (-36 * k / 11)
      + 2160 * k / 121 * Real.exp (-36 * k / 11) ≤ 36 * k * Real.exp (-k) := by
    have h2 : 4320 * k / 121 ≤ 36 * k := by
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 121)]
      linarith
    have h3 : 2160 * k / 121 * Real.exp (-36 * k / 11)
        + 2160 * k / 121 * Real.exp (-36 * k / 11)
        = 4320 * k / 121 * Real.exp (-36 * k / 11) := by ring
    rw [h3]
    have h4 : 4320 * k / 121 * Real.exp (-36 * k / 11)
        ≤ 4320 * k / 121 * Real.exp (-k) :=
      mul_le_mul_of_nonneg_left hAB (by positivity)
    have h5 : 4320 * k / 121 * Real.exp (-k) ≤ 36 * k * Real.exp (-k) :=
      mul_le_mul_of_nonneg_right h2 (Real.exp_nonneg _)
    linarith
  have hm : C2 * (5 / 3) ≤ Real.exp (-k) * (362 * k + 532 * k ^ 2) := by
    rw [hC2def, mul_assoc]
    have hlin : (22 * k + 195 * k + 319 * k ^ 2) * (5 / 3)
        ≤ 362 * k + 532 * k ^ 2 := by
      nlinarith [hk'.le, sq_nonneg k]
    exact mul_le_mul_of_nonneg_left hlin (Real.exp_nonneg _)
  linarith

/-- Rung 2 of the vertical-decay ladder: two integration by parts with
explicit constants. -/
theorem laplace_abs_le_rung2 (k : ℝ) (hk : 1 ≤ k) (w : ℂ) (hw : w ≠ 0) :
    ‖∫ u in (-1 : ℝ)..(1 : ℝ), (gevreyInner k u : ℂ) * Complex.exp (w * (u : ℂ))‖
        ≤ Real.exp |w.re| * ((532 * k ^ 2 + 398 * k) * Real.exp (-k)) / ‖w‖ ^ 2 := by
  have hk' : (0 : ℝ) < k := by linarith
  have hcontF : ContinuousOn (fun u : ℝ => (gevreyInner k u : ℂ)) (uIcc (-1 : ℝ) 1) :=
    Continuous.continuousOn
      (Complex.continuous_ofReal.comp (continuous_gevreyInner k hk'))
  have hcontG : ContinuousOn (fun u : ℝ => (gevreyDeriv k u : ℂ)) (uIcc (-1 : ℝ) 1) :=
    Continuous.continuousOn
      (Complex.continuous_ofReal.comp (continuous_gevreyDeriv k hk'))
  have hcontD : ContinuousOn (fun u : ℝ => (gevreyDeriv2 k u : ℂ)) (uIcc (-1 : ℝ) 1) :=
    Continuous.continuousOn
      (Complex.continuous_ofReal.comp (continuous_gevreyDeriv2 k hk'))
  have hcontV : ContinuousOn (fun u : ℝ => Complex.exp (w * (u : ℂ)) / w)
      (uIcc (-1 : ℝ) 1) :=
    Continuous.continuousOn
      (Continuous.div (by fun_prop) continuous_const fun _ => hw)
  have hid : ∀ x : ℝ, HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := fun _ =>
    Complex.ofRealCLM.hasDerivAt
  have hvv' : ∀ x ∈ Ioo (min (-1 : ℝ) 1) (max (-1 : ℝ) 1),
      HasDerivAt (fun u : ℝ => Complex.exp (w * (u : ℂ)) / w)
        (Complex.exp (w * (x : ℂ))) x := by
    intro x _
    have h2 := ((hid x).const_mul w).cexp
    have h3 : Complex.exp (w * (x : ℂ)) * w / w = Complex.exp (w * (x : ℂ)) := by
      field_simp
    simpa [h3] using h2.div_const w
  have hu1' : ∀ x ∈ Ioo (min (-1 : ℝ) 1) (max (-1 : ℝ) 1),
      HasDerivAt (fun u : ℝ => (gevreyInner k u : ℂ)) ((gevreyDeriv k x : ℝ) : ℂ) x := by
    intro x hx
    simp only [mem_Ioo, min_eq_left (by norm_num : (-1 : ℝ) ≤ 1),
      max_eq_right (by norm_num : (-1 : ℝ) ≤ 1)] at hx
    obtain ⟨hx1, hx2⟩ := hx
    have hx' : |x| < 1 := abs_lt.mpr ⟨by linarith, by linarith⟩
    exact hasDerivAt_complex_gevreyInner k x hx'
  have hu2' : ∀ x ∈ Ioo (min (-1 : ℝ) 1) (max (-1 : ℝ) 1),
      HasDerivAt (fun u : ℝ => (gevreyDeriv k u : ℂ)) ((gevreyDeriv2 k x : ℝ) : ℂ) x := by
    intro x hx
    simp only [mem_Ioo, min_eq_left (by norm_num : (-1 : ℝ) ≤ 1),
      max_eq_right (by norm_num : (-1 : ℝ) ≤ 1)] at hx
    obtain ⟨hx1, hx2⟩ := hx
    have hx' : |x| < 1 := abs_lt.mpr ⟨by linarith, by linarith⟩
    have hd := gevreyDeriv_hasDerivAt_of_abs_lt k x hk' hx'
    have hof : HasDerivAt (fun v : ℝ => (v : ℂ)) 1 (gevreyDeriv k x) :=
      Complex.ofRealCLM.hasDerivAt
    have hcomp := hof.scomp x hd
    simpa [Function.comp] using hcomp
  have hintG : IntervalIntegrable (fun u : ℝ => (gevreyInner k u : ℂ)) volume (-1 : ℝ) 1 :=
    hcontF.intervalIntegrable (μ := volume)
  have hintD : IntervalIntegrable (fun u : ℝ => (gevreyDeriv k u : ℂ)) volume (-1 : ℝ) 1 :=
    hcontG.intervalIntegrable (μ := volume)
  have hintD2 : IntervalIntegrable (fun u : ℝ => (gevreyDeriv2 k u : ℂ)) volume (-1 : ℝ) 1 :=
    hcontD.intervalIntegrable (μ := volume)
  have hintVe : IntervalIntegrable (fun u : ℝ => Complex.exp (w * (u : ℂ)))
      volume (-1 : ℝ) 1 :=
    (by fun_prop : Continuous (fun u : ℝ => Complex.exp (w * (u : ℂ)))).intervalIntegrable
      (-1 : ℝ) 1
  -- first integration by parts
  have hIBP1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := (-1 : ℝ)) (b := (1 : ℝ))
    (u := fun u : ℝ => (gevreyInner k u : ℂ))
    (v := fun u : ℝ => Complex.exp (w * (u : ℂ)) / w)
    (u' := fun x : ℝ => ((gevreyDeriv k x : ℝ) : ℂ))
    (v' := fun u : ℝ => Complex.exp (w * (u : ℂ)))
    hcontF hcontV hu1' hvv' hintD hintVe
  have hb1 : (gevreyInner k 1 : ℂ) = 0 := by
    simp [gevreyInner_of_one_le_abs k 1 abs_one.ge]
  have hb2 : (gevreyInner k (-1) : ℂ) = 0 := by
    simp [gevreyInner_of_one_le_abs k (-1) (by simp)]
  have hprod : (fun u : ℝ =>
        ((gevreyDeriv k u : ℝ) : ℂ) * (Complex.exp (w * (u : ℂ)) / w))
      = fun u : ℝ => (1 / w) * (((gevreyDeriv k u : ℝ) : ℂ) * Complex.exp (w * (u : ℂ))) := by
    funext u
    field_simp
  simp only [hb1, hb2, zero_mul, zero_sub, neg_zero, hprod,
    intervalIntegral.integral_const_mul] at hIBP1
  -- second integration by parts
  have hIBP2 := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := (-1 : ℝ)) (b := (1 : ℝ))
    (u := fun u : ℝ => (gevreyDeriv k u : ℂ))
    (v := fun u : ℝ => Complex.exp (w * (u : ℂ)) / w)
    (u' := fun x : ℝ => ((gevreyDeriv2 k x : ℝ) : ℂ))
    (v' := fun u : ℝ => Complex.exp (w * (u : ℂ)))
    hcontG hcontV hu2' hvv' hintD2 hintVe
  have gb1 : ((gevreyDeriv k 1 : ℝ) : ℂ) = 0 := by
    rw [gevreyDeriv_of_one_le_abs k 1 abs_one.ge]
    exact Complex.ofReal_zero
  have gb2 : ((gevreyDeriv k (-1) : ℝ) : ℂ) = 0 := by
    rw [gevreyDeriv_of_one_le_abs k (-1) (by simp)]
    exact Complex.ofReal_zero
  have hprod2 : (fun u : ℝ =>
        ((gevreyDeriv2 k u : ℝ) : ℂ) * (Complex.exp (w * (u : ℂ)) / w))
      = fun u : ℝ => (1 / w) * (((gevreyDeriv2 k u : ℝ) : ℂ) * Complex.exp (w * (u : ℂ))) := by
    funext u
    field_simp
  simp only [gb1, gb2, zero_mul, zero_sub, neg_zero, hprod2,
    intervalIntegral.integral_const_mul] at hIBP2
  -- combine the two steps
  rw [hIBP1, hIBP2]
  have hnorm1 : ‖((1 / w : ℂ))‖ = 1 / ‖w‖ := by
    rw [norm_div, norm_one]
  simp only [norm_neg, norm_mul, hnorm1]
  -- pointwise exponential strip bound
  have hre : ∀ x ∈ Icc (-1 : ℝ) 1, (w * (x : ℂ)).re ≤ |w.re| := by
    intro x hx
    simp only [mem_Icc] at hx
    have hx1 : |x| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    have hmain : w.re * x ≤ |w.re * x| := le_abs_self _
    have hrest : |w.re * x| ≤ |w.re| := by
      rw [abs_mul]
      exact le_trans (mul_le_mul_of_nonneg_left hx1 (abs_nonneg w.re)) (by simp)
    exact le_trans hmain hrest
  have hinner : ‖∫ u in (-1 : ℝ)..(1 : ℝ),
        ((gevreyDeriv2 k u : ℝ) : ℂ) * Complex.exp (w * (u : ℂ))‖
      ≤ Real.exp |w.re| * ∫ u in (-1 : ℝ)..(1 : ℝ), |gevreyDeriv2 k u| := by
    have hcprod : Continuous (fun u : ℝ =>
        ((gevreyDeriv2 k u : ℝ) : ℂ) * Complex.exp (w * (u : ℂ))) :=
      (Complex.continuous_ofReal.comp (continuous_gevreyDeriv2 k hk')).mul (by fun_prop)
    have hfx : ∀ x ∈ Icc (-1 : ℝ) 1,
        ‖((gevreyDeriv2 k x : ℝ) : ℂ) * Complex.exp (w * (x : ℂ))‖
          ≤ |gevreyDeriv2 k x| * Real.exp |w.re| := by
      intro x hx
      rw [norm_mul, Complex.norm_exp]
      have h5 : ‖((gevreyDeriv2 k x : ℝ) : ℂ)‖ = |gevreyDeriv2 k x| := by norm_cast
      rw [h5]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hre x hx))
        (abs_nonneg _)
    calc ‖∫ u in (-1 : ℝ)..(1 : ℝ),
          ((gevreyDeriv2 k u : ℝ) : ℂ) * Complex.exp (w * (u : ℂ))‖
        ≤ ∫ u in (-1 : ℝ)..(1 : ℝ),
          ‖((gevreyDeriv2 k u : ℝ) : ℂ) * Complex.exp (w * (u : ℂ))‖ :=
        intervalIntegral.norm_integral_le_integral_norm (by norm_num)
      _ ≤ ∫ u in (-1 : ℝ)..(1 : ℝ), |gevreyDeriv2 k u| * Real.exp |w.re| := by
          refine intervalIntegral.integral_mono_on (by norm_num)
            ((hcprod.norm).intervalIntegrable (-1 : ℝ) 1)
            (((continuous_gevreyDeriv2 k hk').abs.mul
              continuous_const).intervalIntegrable (-1 : ℝ) 1)
            (fun x hx => ?_)
          simp only [mem_Icc] at hx
          exact hfx x hx
      _ = Real.exp |w.re| * ∫ u in (-1 : ℝ)..(1 : ℝ), |gevreyDeriv2 k u| := by
          rw [intervalIntegral.integral_mul_const]
          exact mul_comm _ _
  have hwne : (0 : ℝ) < ‖w‖ := norm_pos_iff.mpr hw
  have hJ2 := integral_abs_gevreyDeriv2_le k hk
  calc (1 / ‖w‖) * ((1 / ‖w‖) * ‖∫ u in (-1 : ℝ)..(1 : ℝ),
        ((gevreyDeriv2 k u : ℝ) : ℂ) * Complex.exp (w * (u : ℂ))‖)
      ≤ (1 / ‖w‖) * ((1 / ‖w‖) *
          (Real.exp |w.re| * ∫ u in (-1 : ℝ)..(1 : ℝ), |gevreyDeriv2 k u|)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hinner (div_nonneg zero_le_one (norm_nonneg w)))
        (div_nonneg zero_le_one (norm_nonneg w))
    _ ≤ (1 / ‖w‖) * ((1 / ‖w‖) *
          (Real.exp |w.re| * (Real.exp (-k) * (532 * k ^ 2 + 398 * k)))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hJ2 (Real.exp_nonneg _))
          (div_nonneg zero_le_one (norm_nonneg w)))
        (div_nonneg zero_le_one (norm_nonneg w))
    _ = Real.exp |w.re| * ((532 * k ^ 2 + 398 * k) * Real.exp (-k)) / ‖w‖ ^ 2 := by
      field_simp

/-- The pipeline form: at the pure-imaginary argument `a * t * I` the strip
factor is exactly `1`. -/
theorem laplace_abs_le_rung2_vertical (k a t : ℝ) (hk : 1 ≤ k) (ha : 0 < a)
    (ht : t ≠ 0) :
    ‖∫ u in (-1 : ℝ)..(1 : ℝ),
        (gevreyInner k u : ℂ) * Complex.exp ((a * t * Complex.I) * (u : ℂ))‖
        ≤ (532 * k ^ 2 + 398 * k) * Real.exp (-k) / (a * |t|) ^ 2 := by
  have hnorm : ‖(a * t * Complex.I : ℂ)‖ = a * |t| := by
    have h1 : ‖(a * t * Complex.I : ℂ)‖
        = ‖((a : ℝ) : ℂ) * ((t : ℝ) : ℂ)‖ * ‖(Complex.I : ℂ)‖ := norm_mul _ _
    have h2 : ‖((a : ℝ) : ℂ) * ((t : ℝ) : ℂ)‖ = |a| * |t| := by
      have h3 : ‖((a : ℝ) : ℂ)‖ = |a| := by norm_cast
      have h4 : ‖((t : ℝ) : ℂ)‖ = |t| := by norm_cast
      rw [norm_mul, h3, h4]
    rw [h1, h2, Complex.norm_I, abs_of_pos ha, mul_one]
  have hne : (a * t * Complex.I : ℂ) ≠ 0 := by
    intro hc
    have hpos : (0 : ℝ) < a * |t| := mul_pos ha (abs_pos.mpr ht)
    have h0 : ‖(a * t * Complex.I : ℂ)‖ = 0 := by rw [hc, norm_zero]
    rw [hnorm] at h0
    exact absurd h0 (by linarith [hpos])
  have hmain := laplace_abs_le_rung2 k hk (a * t * Complex.I) hne
  have hre0 : ((a * t * Complex.I : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.I_re]
  rw [hre0, abs_zero, Real.exp_zero, one_mul, hnorm] at hmain
  exact hmain
