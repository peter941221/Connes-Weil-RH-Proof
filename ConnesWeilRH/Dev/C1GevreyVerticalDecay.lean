/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/
import Mathlib
import ConnesWeilRH.Dev.C1GevreyWindow

/-!
# Gevrey window — brick 2, rung 1: vertical Laplace decay with explicit constants

Record 1982 prices the deterministic route's one real-analysis brick as
`|L_phi(a (sigma + i t))| <= C * exp (-c * sqrt (k |t|))` with EXPLICIT `C, c`;
record 1983 confirms the saddle law `log |L_phi(i t)| ~ -sqrt(k a t)` at 80
digits and rules that the constants need only be VALID, not sharp.

This module lands rung 1 of the integration-by-parts ladder:

* the piecewise derivative `gevreyDeriv` of the window, continuous everywhere
  (the glue at `|u| = 1` is a squeeze through `C * (1 - u ^ 2) ^ 4`, fed by
  `exp (-k / t) = (exp (-k / (6 t))) ^ 6` against brick 1's master bound);
* its exact `L ^ 1` mass: the window is monotone on each half, so each outer
  piece carries the exact total variation `exp (-4 * k / 3)`, and the middle
  piece is bounded by `(16 * k / 9) * exp (-k)`;
* the ladder step: one integration by parts kills the boundary terms by the
  brick-1 flatness, giving
  `|∫_{-1}^{1} phi_k(u) e^{w u} du|
    ≤ e^{|Re w|} * (2 * exp(-4k/3) + (16k/9) * exp(-k)) / |w|`;
* the vertical specialization at `w = a * t * I`: the strip factor is exactly
  `1`, so the bound is `(2 * exp(-4k/3) + (16k/9) * exp(-k)) / (a * |t|)`.

Rungs `n ≥ 2` (the optimized-`n` sqrt law of record 1982) are the priced
remainder of brick 2; nothing here claims them.
-/

open Real Set Filter Topology MeasureTheory

private lemma sq_lt_one_of_abs_lt_one {u : ℝ} (h : |u| < 1) : u ^ 2 < 1 := by
  obtain ⟨h2, h3⟩ := abs_lt.mp h
  nlinarith [h2, h3]

/-- The interior derivative formula of `gevreyInner k`, extended by `0`. -/
noncomputable def gevreyDeriv (k u : ℝ) : ℝ :=
  if |u| < 1 then Real.exp (-k / (1 - u ^ 2)) * (-k * (2 * u / (1 - u ^ 2) ^ 2)) else 0

lemma gevreyDeriv_of_abs_lt (k u : ℝ) (h : |u| < 1) :
    gevreyDeriv k u = Real.exp (-k / (1 - u ^ 2)) * (-k * (2 * u / (1 - u ^ 2) ^ 2)) := by
  simp only [gevreyDeriv, if_pos h]

lemma gevreyDeriv_of_one_le_abs (k u : ℝ) (h : 1 ≤ |u|) :
    gevreyDeriv k u = 0 := by
  simp only [gevreyDeriv, if_neg (not_lt.mpr h)]

/-- Master bound: the derivative magnitude dies like `(1 - u ^ 2) ^ 4`.
The sixth power against brick 1's `exp (-k / t) ≤ t / k` gives `t ^ 4`. -/
lemma abs_gevreyDeriv_le_quartic (k : ℝ) (hk : 0 < k) (u : ℝ) :
    |gevreyDeriv k u| ≤ 2 * 6 ^ 6 * (k ^ 5)⁻¹ * (1 - u ^ 2) ^ 4 := by
  rcases lt_or_ge (abs u) 1 with h | h
  · obtain ⟨h2, h3⟩ := abs_lt.mp h
    have hu2 : u ^ 2 < 1 := sq_lt_one_of_abs_lt_one h
    have ht : 0 < 1 - u ^ 2 := by linarith
    have habs : |gevreyDeriv k u|
        = Real.exp (-k / (1 - u ^ 2)) * (k * (2 * |u|) / (1 - u ^ 2) ^ 2) := by
      rw [gevreyDeriv_of_abs_lt k u h]
      simp only [abs_mul, abs_div, abs_neg, abs_pow, abs_of_pos (Real.exp_pos _),
        abs_of_pos hk, abs_of_nonneg ht.le, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      norm_num
      ring
    have hstep : Real.exp (-k / (1 - u ^ 2))
        = (Real.exp (-k / (6 * (1 - u ^ 2)))) ^ 6 := by
      have h6 : (-k / (1 - u ^ 2)) = ((6 : ℕ) : ℝ) * (-k / (6 * (1 - u ^ 2))) := by
        norm_num
        field_simp
      rw [h6, Real.exp_nat_mul]
    have hle : Real.exp (-k / (6 * (1 - u ^ 2))) ≤ 6 * (1 - u ^ 2) / k :=
      exp_neg_div_le_div k hk _ (by linarith)
    have hub : |u| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    have h22 : k * (2 * |u|) ≤ k * 2 := mul_le_mul_of_nonneg_left
      (by linarith : 2 * |u| ≤ 2) hk.le
    calc |gevreyDeriv k u|
        = Real.exp (-k / (1 - u ^ 2)) * (k * (2 * |u|) / (1 - u ^ 2) ^ 2) := habs
      _ = (Real.exp (-k / (6 * (1 - u ^ 2)))) ^ 6 * (k * (2 * |u|) / (1 - u ^ 2) ^ 2) := by
          rw [hstep]
      _ ≤ (6 * (1 - u ^ 2) / k) ^ 6 * (k * 2 / (1 - u ^ 2) ^ 2) := by
          refine mul_le_mul ?_ ?_ (by positivity) (by positivity)
          · exact pow_le_pow_left₀ (Real.exp_nonneg _) hle 6
          · refine div_le_div_iff₀ (by positivity) (by positivity) |>.mpr ?_
            exact mul_le_mul_of_nonneg_right h22 (by positivity)
      _ = 2 * 6 ^ 6 * (k ^ 5)⁻¹ * (1 - u ^ 2) ^ 4 := by
          field_simp
  · rw [gevreyDeriv_of_one_le_abs k u h, abs_zero]
    positivity

lemma continuous_gevreyDeriv (k : ℝ) (hk : 0 < k) : Continuous (gevreyDeriv k) := by
  rw [continuous_iff_continuousAt]
  intro u
  rcases lt_trichotomy (abs u) 1 with h | h | h
  · have hden : ContinuousAt (fun v : ℝ => 1 - v ^ 2) u := by fun_prop
    have hu2 : u ^ 2 < 1 := sq_lt_one_of_abs_lt_one h
    have hne : (1 : ℝ) - u ^ 2 ≠ 0 := by linarith
    have hck : ContinuousAt (fun _ : ℝ => (-k : ℝ)) u := continuousAt_const
    have h1 : ContinuousAt (fun v : ℝ => -k / (1 - v ^ 2)) u := hck.div hden hne
    have h2 : ContinuousAt (fun v : ℝ => Real.exp (-k / (1 - v ^ 2))) u :=
      Real.continuous_exp.continuousAt.comp h1
    have h3 : ContinuousAt (fun v : ℝ => 2 * v / (1 - v ^ 2) ^ 2) u := by
      refine ContinuousAt.div (by fun_prop) (hden.pow 2) ?_
      exact pow_ne_zero 2 hne
    have hform : ContinuousAt (fun v : ℝ =>
        Real.exp (-k / (1 - v ^ 2)) * (-k * (2 * v / (1 - v ^ 2) ^ 2))) u :=
      h2.mul (hck.mul h3)
    have hev : (fun v : ℝ => gevreyDeriv k v)
        =ᶠ[𝓝 u] (fun v : ℝ => Real.exp (-k / (1 - v ^ 2)) * (-k * (2 * v / (1 - v ^ 2) ^ 2))) := by
      have hop : {v : ℝ | |v| < 1} ∈ 𝓝 u := (isOpen_lt continuous_abs continuous_one).mem_nhds h
      filter_upwards [hop] with v hv
      exact gevreyDeriv_of_abs_lt k v hv
    rw [ContinuousAt, gevreyDeriv_of_abs_lt k u h]
    exact hform.congr' hev.symm
  · have hu2 : u ^ 2 = 1 := by
      have hsq := sq_abs u
      rw [h] at hsq
      linarith
    have hz : Tendsto (fun v : ℝ => 2 * 6 ^ 6 * (k ^ 5)⁻¹ * (1 - v ^ 2) ^ 4) (𝓝 u) (𝓝 0) := by
      have hc4 : Continuous (fun v : ℝ => 2 * 6 ^ 6 * (k ^ 5)⁻¹ * (1 - v ^ 2) ^ 4) := by
        fun_prop
      have h1 := hc4.tendsto u
      rw [hu2] at h1
      simpa using h1
    have hzero : gevreyDeriv k u = 0 := gevreyDeriv_of_one_le_abs k u h.ge
    rw [ContinuousAt, hzero]
    have hneg : Tendsto
        (fun v : ℝ => -(2 * 6 ^ 6 * (k ^ 5)⁻¹ * (1 - v ^ 2) ^ 4)) (𝓝 u) (𝓝 0) := by
      simpa using hz.neg
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hneg hz
      (Filter.Eventually.of_forall fun v =>
        (abs_le.mp (abs_gevreyDeriv_le_quartic k hk v)).1)
      (Filter.Eventually.of_forall fun v =>
        (abs_le.mp (abs_gevreyDeriv_le_quartic k hk v)).2)
  · have hopen : {v : ℝ | 1 < |v|} ∈ 𝓝 u := (isOpen_lt continuous_const continuous_abs).mem_nhds h
    have hev : (fun v : ℝ => gevreyDeriv k v) =ᶠ[𝓝 u] (fun _ : ℝ => (0 : ℝ)) := by
      filter_upwards [hopen] with v hv
      exact gevreyDeriv_of_one_le_abs k v (le_of_lt hv)
    have hzero : gevreyDeriv k u = 0 := gevreyDeriv_of_one_le_abs k u h.le
    rw [ContinuousAt, hzero]
    exact tendsto_const_nhds.congr' hev.symm

lemma intervalIntegrable_gevreyDeriv (k : ℝ) (hk : 0 < k) (a b : ℝ) :
    IntervalIntegrable (gevreyDeriv k) volume a b :=
  (continuous_gevreyDeriv k hk).continuousOn.intervalIntegrable (μ := volume)

/-- The derivative is nonpositive on the right half of the window. -/
lemma gevreyDeriv_nonpos_of_mem_Icc (k : ℝ) (hk : 0 < k) (u : ℝ) (h : u ∈ Icc (1 / 2 : ℝ) 1) :
    gevreyDeriv k u ≤ 0 := by
  obtain ⟨hlow, hhigh⟩ := h
  by_cases h1 : u = 1
  · subst h1
    exact (gevreyDeriv_of_one_le_abs k 1 abs_one.ge).le
  · have hu1 : u < 1 := lt_of_le_of_ne hhigh h1
    have ha : |u| < 1 := abs_lt.mpr ⟨by linarith, hu1⟩
    have hden : (0 : ℝ) < 1 - u ^ 2 := by
      have hu2 : u ^ 2 < 1 := sq_lt_one_of_abs_lt_one ha
      linarith
    have hdiv : 0 ≤ 2 * u / (1 - u ^ 2) ^ 2 :=
      div_nonneg (by linarith) (by positivity)
    have hprod : 0 ≤ k * (2 * u / (1 - u ^ 2) ^ 2) := mul_nonneg hk.le hdiv
    rw [gevreyDeriv_of_abs_lt k u ha, neg_mul]
    have hneg : -(k * (2 * u / (1 - u ^ 2) ^ 2)) ≤ 0 := by linarith
    have h1 : Real.exp (-k / (1 - u ^ 2)) * -(k * (2 * u / (1 - u ^ 2) ^ 2))
        ≤ Real.exp (-k / (1 - u ^ 2)) * 0 :=
      mul_le_mul_of_nonneg_left hneg (Real.exp_nonneg _)
    simpa using h1

/-- The derivative is nonnegative on the left half of the window. -/
lemma gevreyDeriv_nonneg_of_mem_Icc (k : ℝ) (hk : 0 < k) (u : ℝ)
    (h : u ∈ Icc (-1 : ℝ) (-1 / 2)) :
    0 ≤ gevreyDeriv k u := by
  obtain ⟨hlow, hhigh⟩ := h
  by_cases h1 : u = -1
  · subst h1
    exact (gevreyDeriv_of_one_le_abs k (-1) (by simp)).symm.le
  · have hu1 : -1 < u := lt_of_le_of_ne hlow (Ne.symm h1)
    have ha : |u| < 1 := abs_lt.mpr ⟨hu1, by linarith⟩
    have hden : (0 : ℝ) < 1 - u ^ 2 := by
      have hu2 : u ^ 2 < 1 := sq_lt_one_of_abs_lt_one ha
      linarith
    have hdiv : 2 * u / (1 - u ^ 2) ^ 2 ≤ 0 := by
      refine (div_le_iff₀ (by positivity)).mpr ?_
      linarith
    have hprod0 : k * (2 * u / (1 - u ^ 2) ^ 2) ≤ 0 := by
      have htmp := mul_le_mul_of_nonneg_left hdiv hk.le
      rwa [mul_zero] at htmp
    have hneg2 : 0 ≤ -(k * (2 * u / (1 - u ^ 2) ^ 2)) := by linarith
    rw [gevreyDeriv_of_abs_lt k u ha, neg_mul]
    exact mul_nonneg (Real.exp_nonneg _) hneg2

lemma integral_abs_gevreyDeriv_half_right (k : ℝ) (hk : 1 ≤ k) :
    ∫ u in ((1 : ℝ) / 2)..1, |gevreyDeriv k u| = Real.exp (-4 * k / 3) := by
  have hkn : (0 : ℝ) < k := by linarith
  have hcongr : ∫ u in ((1 : ℝ) / 2)..1, |gevreyDeriv k u|
      = ∫ u in ((1 : ℝ) / 2)..1, -gevreyDeriv k u := by
    refine intervalIntegral.integral_congr (fun u hu => ?_)
    simp only [mem_uIcc] at hu
    rcases hu with h | h
    · rw [abs_of_nonpos (gevreyDeriv_nonpos_of_mem_Icc k hkn u ⟨h.1, h.2⟩)]
    · have hueq : u = 1 := le_antisymm (by linarith) h.1
      subst hueq
      rw [gevreyDeriv_of_one_le_abs k 1 abs_one.ge, abs_zero]
      ring
  have hint : IntervalIntegrable (gevreyDeriv k) volume ((1 : ℝ) / 2) 1 :=
    intervalIntegrable_gevreyDeriv k hkn _ _
  have hcont : ContinuousOn (gevreyInner k) (Icc ((1 : ℝ) / 2) 1) :=
    (continuous_gevreyInner k hkn).continuousOn
  have hderiv : ∀ x ∈ Ioo ((1 : ℝ) / 2) 1, HasDerivAt (gevreyInner k) (gevreyDeriv k x) x := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := hx
    have hx' : |x| < 1 := abs_lt.mpr ⟨by linarith, by linarith⟩
    rw [gevreyDeriv_of_abs_lt k x hx']
    exact gevreyInner_hasDerivAt_of_abs_lt k x hx'
  have hftc : ∫ u in ((1 : ℝ) / 2)..1, gevreyDeriv k u
      = gevreyInner k 1 - gevreyInner k (1 / 2) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num) hcont hderiv hint
  have hv1 : gevreyInner k 1 = 0 := gevreyInner_of_one_le_abs k 1 abs_one.ge
  have hv2 : gevreyInner k (1 / 2) = Real.exp (-4 * k / 3) := by
    rw [gevreyInner_of_abs_lt k (1 / 2) (by norm_num)]
    refine congrArg Real.exp ?_
    field_simp
    ring
  rw [hcongr]
  have hc1 : (fun u => -gevreyDeriv k u) = fun u => (-1 : ℝ) * gevreyDeriv k u := by
    funext u
    ring
  rw [hc1, intervalIntegral.integral_const_mul, hftc, hv1, hv2]
  ring

lemma integral_abs_gevreyDeriv_half_left (k : ℝ) (hk : 1 ≤ k) :
    ∫ u in (-1 : ℝ)..(-(1 : ℝ) / 2), |gevreyDeriv k u| = Real.exp (-4 * k / 3) := by
  have hkn : (0 : ℝ) < k := by linarith
  have hcongr : ∫ u in (-1 : ℝ)..(-(1 : ℝ) / 2), |gevreyDeriv k u|
      = ∫ u in (-1 : ℝ)..(-(1 : ℝ) / 2), gevreyDeriv k u := by
    refine intervalIntegral.integral_congr (fun u hu => ?_)
    simp only [mem_uIcc] at hu
    rcases hu with h | h
    · rw [abs_of_nonneg (gevreyDeriv_nonneg_of_mem_Icc k hkn u ⟨h.1, h.2⟩)]
    · have hueq : u = -1 := le_antisymm h.2 (by linarith)
      subst hueq
      rw [gevreyDeriv_of_one_le_abs k (-1) (by simp), abs_zero]
  have hint : IntervalIntegrable (gevreyDeriv k) volume (-1 : ℝ) (-(1 : ℝ) / 2) :=
    intervalIntegrable_gevreyDeriv k hkn _ _
  have hcont : ContinuousOn (gevreyInner k) (Icc (-1 : ℝ) (-(1 : ℝ) / 2)) :=
    (continuous_gevreyInner k hkn).continuousOn
  have hderiv : ∀ x ∈ Ioo (-1 : ℝ) (-(1 : ℝ) / 2),
      HasDerivAt (gevreyInner k) (gevreyDeriv k x) x := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := hx
    have hx' : |x| < 1 := abs_lt.mpr ⟨by linarith, by linarith⟩
    rw [gevreyDeriv_of_abs_lt k x hx']
    exact gevreyInner_hasDerivAt_of_abs_lt k x hx'
  have hftc : ∫ u in (-1 : ℝ)..(-(1 : ℝ) / 2), gevreyDeriv k u
      = gevreyInner k (-(1 : ℝ) / 2) - gevreyInner k (-1) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num) hcont hderiv hint
  have hv1 : gevreyInner k (-1) = 0 := gevreyInner_of_one_le_abs k (-1) (by simp)
  have hv2 : gevreyInner k (-(1 : ℝ) / 2) = Real.exp (-4 * k / 3) := by
    rw [gevreyInner_of_abs_lt k (-(1 : ℝ) / 2) (by norm_num)]
    refine congrArg Real.exp ?_
    field_simp
    ring
  rw [hcongr, hftc, hv2, hv1]
  ring

lemma abs_gevreyDeriv_le_mid (k : ℝ) (hk : 1 ≤ k) (u : ℝ) (hu : |u| ≤ 1 / 2) :
    |gevreyDeriv k u| ≤ 16 * k / 9 * Real.exp (-k) := by
  have hk' : (0 : ℝ) < k := by linarith
  have h1 : |u| < 1 := lt_of_le_of_lt hu (by norm_num)
  have hu2 : u ^ 2 < 1 := sq_lt_one_of_abs_lt_one h1
  have ht : 0 < 1 - u ^ 2 := by linarith
  have habs : |gevreyDeriv k u|
      = Real.exp (-k / (1 - u ^ 2)) * (k * (2 * |u|) / (1 - u ^ 2) ^ 2) := by
    rw [gevreyDeriv_of_abs_lt k u h1]
    simp only [abs_mul, abs_div, abs_neg, abs_pow, abs_of_pos (Real.exp_pos _),
      abs_of_pos hk', abs_of_nonneg ht.le, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
    ring
  have hexp : Real.exp (-k / (1 - u ^ 2)) ≤ Real.exp (-k) := by
    refine Real.exp_le_exp.mpr ?_
    have h2 : (1 : ℝ) - u ^ 2 ≤ 1 := by linarith [sq_nonneg u]
    have h3 : k * (1 - u ^ 2) ≤ k * 1 := mul_le_mul_of_nonneg_left h2 hk'.le
    rw [mul_one] at h3
    have h4 : (-k / (1 - u ^ 2)) ≤ -k := by
      rw [div_le_iff₀ ht]
      linarith
    linarith
  have hsq : u ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
    obtain ⟨hlo, hhi⟩ := abs_le.mp hu
    nlinarith [hlo, hhi]
  have h34 : (3 / 4 : ℝ) ≤ 1 - u ^ 2 := by nlinarith [hsq]
  have h43 : (3 / 4 : ℝ) ^ 2 ≤ (1 - u ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) h34 2
  have e1 : (2 * |u|) / (1 - u ^ 2) ^ 2 ≤ 16 / 9 := by
    refine (div_le_iff₀ (by positivity)).mpr ?_
    have h1' : 2 * |u| ≤ 1 := by linarith
    have h2' : (1 : ℝ) ≤ (16 / 9) * (1 - u ^ 2) ^ 2 := by
      have h916 : (3 / 4 : ℝ) ^ 2 = 9 / 16 := by norm_num
      calc (1 : ℝ) = (16 / 9) * (9 / 16) := by norm_num
        _ = (16 / 9) * (3 / 4 : ℝ) ^ 2 := by rw [h916]
        _ ≤ (16 / 9) * (1 - u ^ 2) ^ 2 := mul_le_mul_of_nonneg_left h43 (by positivity)
    linarith
  have hdiv : k * (2 * |u|) / (1 - u ^ 2) ^ 2 ≤ 16 * k / 9 := by
    have hk2 : k * ((2 * |u|) / (1 - u ^ 2) ^ 2) ≤ k * (16 / 9) :=
      mul_le_mul_of_nonneg_left e1 hk'.le
    calc k * (2 * |u|) / (1 - u ^ 2) ^ 2
        = k * ((2 * |u|) / (1 - u ^ 2) ^ 2) := by ring
      _ ≤ k * (16 / 9) := hk2
      _ = 16 * k / 9 := by ring
  calc |gevreyDeriv k u|
      = Real.exp (-k / (1 - u ^ 2)) * (k * (2 * |u|) / (1 - u ^ 2) ^ 2) := habs
    _ ≤ Real.exp (-k) * (16 * k / 9) := mul_le_mul hexp hdiv (by positivity) (by positivity)
    _ = 16 * k / 9 * Real.exp (-k) := mul_comm _ _

lemma integral_abs_gevreyDeriv_le (k : ℝ) (hk : 1 ≤ k) :
    ∫ u in (-1 : ℝ)..1, |gevreyDeriv k u|
      ≤ 2 * Real.exp (-4 * k / 3) + 16 * k / 9 * Real.exp (-k) := by
  have hk' : (0 : ℝ) < k := by linarith
  have hc : ∀ a b : ℝ, IntervalIntegrable (fun u => |gevreyDeriv k u|) volume a b :=
    fun a b => (continuous_gevreyDeriv k hk').abs.intervalIntegrable (μ := volume) a b
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc (-1) (-(1 : ℝ) / 2))
      (hc (-(1 : ℝ) / 2) 1),
    ← intervalIntegral.integral_add_adjacent_intervals (hc (-(1 : ℝ) / 2) (1 / 2))
      (hc (1 / 2) 1),
    integral_abs_gevreyDeriv_half_left k hk, integral_abs_gevreyDeriv_half_right k hk]
  have hcst : IntervalIntegrable (fun _ : ℝ => 16 * k / 9 * Real.exp (-k)) volume
      (-(1 : ℝ) / 2) (1 / 2) :=
    (continuous_const : Continuous (fun _ : ℝ => 16 * k / 9 * Real.exp (-k))).intervalIntegrable
      (μ := volume) _ _
  have hmid := intervalIntegral.integral_mono_on (by norm_num : (-1 : ℝ) / 2 ≤ 1 / 2)
    (hc (-(1 : ℝ) / 2) (1 / 2))
    hcst
    (fun x hx => by
      simp only [mem_Icc] at hx
      exact abs_gevreyDeriv_le_mid k hk x (abs_le.mpr ⟨by linarith, by linarith⟩))
  have hconstval : ∫ u in (-(1 : ℝ) / 2)..(1 / 2), (16 * k / 9 * Real.exp (-k))
      = 16 * k / 9 * Real.exp (-k) := by
    rw [intervalIntegral.integral_const]
    norm_num
  rw [hconstval] at hmid
  linarith

/-- The complex-valued window carries the coerced derivative inside the strip. -/
lemma hasDerivAt_complex_gevreyInner (k u : ℝ) (h : |u| < 1) :
    HasDerivAt (fun v : ℝ => (gevreyInner k v : ℂ)) ((gevreyDeriv k u : ℝ) : ℂ) u := by
  have hR := gevreyInner_hasDerivAt_of_abs_lt k u h
  have hof : HasDerivAt (fun v : ℝ => (v : ℂ)) 1 (gevreyInner k u) :=
    Complex.ofRealCLM.hasDerivAt
  have hcomp := hof.scomp u hR
  rw [gevreyDeriv_of_abs_lt k u h]
  simpa [Function.comp] using hcomp

/-- Rung 1 of the vertical-decay ladder: one integration by parts with
explicit constants. -/
theorem laplace_abs_le (k : ℝ) (hk : 1 ≤ k) (w : ℂ) (hw : w ≠ 0) :
    ‖∫ u in (-1 : ℝ)..(1 : ℝ), (gevreyInner k u : ℂ) * Complex.exp (w * (u : ℂ))‖
        ≤ Real.exp |w.re| * (2 * Real.exp (-4 * k / 3) + 16 * k / 9 * Real.exp (-k)) / ‖w‖ := by
  have hk' : (0 : ℝ) < k := by linarith
  have hcontF : ContinuousOn (fun u : ℝ => (gevreyInner k u : ℂ)) (uIcc (-1 : ℝ) 1) :=
    Continuous.continuousOn
      (Complex.continuous_ofReal.comp (continuous_gevreyInner k hk'))
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
  have hu' : ∀ x ∈ Ioo (min (-1 : ℝ) 1) (max (-1 : ℝ) 1),
      HasDerivAt (fun u : ℝ => (gevreyInner k u : ℂ)) ((gevreyDeriv k x : ℝ) : ℂ) x := by
    intro x hx
    simp only [mem_Ioo, min_eq_left (by norm_num : (-1 : ℝ) ≤ 1),
      max_eq_right (by norm_num : (-1 : ℝ) ≤ 1)] at hx
    exact hasDerivAt_complex_gevreyInner k x (abs_lt.mpr ⟨by linarith, by linarith⟩)
  have hintG : IntervalIntegrable
      (fun x : ℝ => ((gevreyDeriv k x : ℝ) : ℂ)) volume (-1 : ℝ) 1 :=
    ContinuousOn.intervalIntegrable (μ := volume)
      (Continuous.continuousOn
        (Complex.continuous_ofReal.comp (continuous_gevreyDeriv k hk')))
  have hintV : IntervalIntegrable (fun u : ℝ => Complex.exp (w * (u : ℂ)))
      volume (-1 : ℝ) 1 :=
    Continuous.intervalIntegrable (μ := volume) (by fun_prop) _ _
  have step : ∫ u in (-1 : ℝ)..(1 : ℝ), (gevreyInner k u : ℂ) * Complex.exp (w * (u : ℂ))
      = -(1 : ℂ) / w * ∫ u in (-1 : ℝ)..(1 : ℝ),
          ((gevreyDeriv k u : ℝ) : ℂ) * Complex.exp (w * (u : ℂ)) := by
    have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      (a := (-1 : ℝ)) (b := (1 : ℝ))
      (u := fun u : ℝ => (gevreyInner k u : ℂ))
      (v := fun u : ℝ => Complex.exp (w * (u : ℂ)) / w)
      (u' := fun x : ℝ => ((gevreyDeriv k x : ℝ) : ℂ))
      (v' := fun u : ℝ => Complex.exp (w * (u : ℂ)))
      hcontF hcontV hu' hvv' hintG hintV
    have hb1 : (gevreyInner k 1 : ℂ) = 0 := by
      simp [gevreyInner_of_one_le_abs k 1 abs_one.ge]
    have hb2 : (gevreyInner k (-1) : ℂ) = 0 := by
      simp [gevreyInner_of_one_le_abs k (-1) (by simp)]
    have hprod : (fun u : ℝ =>
          ((gevreyDeriv k u : ℝ) : ℂ) * (Complex.exp (w * (u : ℂ)) / w))
        = fun u : ℝ => (1 / w) * (((gevreyDeriv k u : ℝ) : ℂ) * Complex.exp (w * (u : ℂ))) := by
      funext u
      field_simp
    simp only [hb1, hb2, zero_mul, zero_sub, hprod,
      intervalIntegral.integral_const_mul] at hIBP
    rw [hIBP]
    ring
  have hwn : (0 : ℝ) < ‖w‖ := by
    rcases lt_or_eq_of_le (norm_nonneg w) with h | h
    · exact h
    · exact absurd (norm_eq_zero.mp h.symm) hw
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
        ((gevreyDeriv k u : ℝ) : ℂ) * Complex.exp (w * (u : ℂ))‖
      ≤ Real.exp |w.re| * ∫ u in (-1 : ℝ)..(1 : ℝ), |gevreyDeriv k u| := by
    have hcprod : Continuous (fun u : ℝ =>
        ((gevreyDeriv k u : ℝ) : ℂ) * Complex.exp (w * (u : ℂ))) :=
      (Complex.continuous_ofReal.comp (continuous_gevreyDeriv k hk')).mul (by fun_prop)
    have hint2 : IntervalIntegrable
        (fun u : ℝ => ‖((gevreyDeriv k u : ℝ) : ℂ) * Complex.exp (w * (u : ℂ))‖)
        volume (-1 : ℝ) 1 := hcprod.norm.intervalIntegrable (μ := volume) _ _
    have hint3 : IntervalIntegrable
        (fun u : ℝ => Real.exp |w.re| * |gevreyDeriv k u|) volume (-1 : ℝ) 1 :=
      (continuous_const.mul (continuous_gevreyDeriv k hk').abs).intervalIntegrable
        (μ := volume) _ _
    have hab : (-1 : ℝ) ≤ 1 := by norm_num
    refine le_trans (intervalIntegral.norm_integral_le_integral_norm hab) ?_
    refine le_trans (intervalIntegral.integral_mono_on (by norm_num) hint2 hint3 ?_) ?_
    · intro x hx
      rw [norm_mul, Complex.norm_exp]
      have h5 : ‖((gevreyDeriv k x : ℝ) : ℂ)‖ = |gevreyDeriv k x| := by norm_cast
      rw [h5]
      refine le_trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hre x hx))
        (by positivity)) ?_
      rw [mul_comm]
    · rw [intervalIntegral.integral_const_mul]
  calc ‖∫ u in (-1 : ℝ)..(1 : ℝ), (gevreyInner k u : ℂ) * Complex.exp (w * (u : ℂ))‖
      = ‖-(1 : ℂ) / w * ∫ u in (-1 : ℝ)..(1 : ℝ),
            ((gevreyDeriv k u : ℝ) : ℂ) * Complex.exp (w * (u : ℂ))‖ := by rw [step]
    _ = (1 / ‖w‖) * ‖∫ u in (-1 : ℝ)..(1 : ℝ),
            ((gevreyDeriv k u : ℝ) : ℂ) * Complex.exp (w * (u : ℂ))‖ := by
        have hinv : ‖(-(1 : ℂ)) / w‖ = 1 / ‖w‖ := by
          rw [norm_div, norm_neg, norm_one]
        rw [norm_mul, hinv]
    _ ≤ (1 / ‖w‖) * (Real.exp |w.re| * ∫ u in (-1 : ℝ)..(1 : ℝ), |gevreyDeriv k u|) :=
        mul_le_mul_of_nonneg_left hinner (by positivity)
    _ ≤ (1 / ‖w‖) * (Real.exp |w.re| *
            (2 * Real.exp (-4 * k / 3) + 16 * k / 9 * Real.exp (-k))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (integral_abs_gevreyDeriv_le k hk) (by positivity))
          (by positivity)
    _ = Real.exp |w.re| * (2 * Real.exp (-4 * k / 3) + 16 * k / 9 * Real.exp (-k)) / ‖w‖ := by
        ring

/-- The pipeline form: at the pure-imaginary argument `a * t * I` the strip
factor is exactly `1`. -/
theorem laplace_abs_le_vertical (k a t : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ht : t ≠ 0) :
    ‖∫ u in (-1 : ℝ)..(1 : ℝ), (gevreyInner k u : ℂ) * Complex.exp ((a * t * Complex.I) * (u : ℂ))‖
        ≤ (2 * Real.exp (-4 * k / 3) + 16 * k / 9 * Real.exp (-k)) / (a * |t|) := by
  have hnorm : ‖(a * t * Complex.I : ℂ)‖ = a * |t| := by
    have h1 : ‖(a * t * Complex.I : ℂ)‖
        = ‖((a : ℝ) : ℂ) * ((t : ℝ) : ℂ)‖ * ‖(Complex.I : ℂ)‖ := norm_mul _ _
    have h2 : ‖((a : ℝ) : ℂ) * ((t : ℝ) : ℂ)‖ = |a| * |t| := by
      have h3 : ‖((a : ℝ) : ℂ)‖ = |a| := by norm_cast
      have h4 : ‖((t : ℝ) : ℂ)‖ = |t| := by norm_cast
      rw [norm_mul, h3, h4]
    rw [h1, h2, Complex.norm_I, abs_of_pos ha, mul_one]
  have hw : (a * t * Complex.I : ℂ) ≠ 0 := by
    intro h0
    have h2 : ‖(a * t * Complex.I : ℂ)‖ = 0 := by rw [h0, norm_zero]
    rw [hnorm] at h2
    have h3 : |t| = 0 := mul_left_cancel₀ (Ne.symm ha.ne) (by rw [h2, mul_zero])
    exact ht (abs_eq_zero.mp h3)
  have hre : ((a * t * Complex.I : ℂ)).re = 0 := by
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hmain := laplace_abs_le k hk (a * t * Complex.I) hw
  rw [hre] at hmain
  simp only [abs_zero, Real.exp_zero, hnorm, one_mul] at hmain
  exact hmain
