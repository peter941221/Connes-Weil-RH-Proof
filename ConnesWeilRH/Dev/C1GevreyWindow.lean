/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/
import Mathlib

/-!
# Gevrey flat window — brick 1, first layer (records 1983-1985)

The deterministic construction of records 1982-1983 needs the measured
family as a Lean object: the flat window `exp (-k / (1 - u ^ 2))` on
`|u| < 1`, extended by `0`.  This module lands the first layer of brick 1:

* the computable definition (exp and div only), its support and evenness;
* the master decay bound `exp (-k / t) ≤ t / k`;
* continuity everywhere (the glue at `|u| = 1` is a `squeeze_zero`);
* differentiability everywhere, with the boundary derivative `0` proved by
  a `‖w‖⁻¹ * exp (-k / (6 |w|))` squeeze at the glue;
* the interior derivative formula.

The full `ContDiff ℝ ∞` ladder (all orders vanish at the glue, each order
by the same `x ^ n * exp (-x)` argument) is the priced remainder of brick
1; nothing here uses it.
-/

open Real Set Filter Topology

/-- Inner profile `exp (-k / (1 - u ^ 2))` on `|u| < 1`, `0` outside. -/
noncomputable def gevreyInner (k : ℝ) (u : ℝ) : ℝ :=
  if |u| < 1 then Real.exp (-k / (1 - u ^ 2)) else 0

/-- The flat window in the position variable: `gevreyInner k (x / a)`. -/
noncomputable def gevreyWindow (k a : ℝ) (x : ℝ) := gevreyInner k (x / a)

lemma gevreyInner_of_abs_lt (k u : ℝ) (h : |u| < 1) :
    gevreyInner k u = Real.exp (-k / (1 - u ^ 2)) := by
  simp only [gevreyInner, if_pos h]

lemma gevreyInner_of_one_le_abs (k u : ℝ) (h : 1 ≤ |u|) :
    gevreyInner k u = 0 := by
  simp only [gevreyInner, if_neg (not_lt.mpr h)]

@[simp] lemma gevreyInner_neg (k u : ℝ) : gevreyInner k (-u) = gevreyInner k u := by
  simp only [gevreyInner, abs_neg, neg_sq]

lemma gevreyWindow_of_abs_lt (k a x : ℝ) (h : |x / a| < 1) :
    gevreyWindow k a x = Real.exp (-k / (1 - (x / a) ^ 2)) :=
  gevreyInner_of_abs_lt k (x / a) h

lemma gevreyInner_support (k : ℝ) :
    Function.support (gevreyInner k) ⊆ Ioo (-1 : ℝ) 1 := by
  intro u hu
  by_cases h : |u| < 1
  · exact abs_lt.mp h
  · have h1 : gevreyInner k u = 0 :=
      gevreyInner_of_one_le_abs k u (not_lt.mp h)
    exact absurd h1 (by simpa using hu)

lemma hnn_gevreyInner (k u : ℝ) : 0 ≤ gevreyInner k u := by
  by_cases h : |u| < 1
  · rw [gevreyInner_of_abs_lt k u h]
    exact le_of_lt (Real.exp_pos _)
  · rw [gevreyInner_of_one_le_abs k u (not_lt.mp h)]

/-- Master decay bound: `exp (-k / t) ≤ t / k` for `k, t > 0`. -/
lemma exp_neg_div_le_div (k : ℝ) (hk : 0 < k) (t : ℝ) (ht : 0 < t) :
    Real.exp (-k / t) ≤ t / k := by
  rw [neg_div]
  have h2 : k / t + 1 ≤ Real.exp (k / t) := Real.add_one_le_exp _
  calc Real.exp (-(k / t)) = (Real.exp (k / t))⁻¹ := Real.exp_neg _
    _ ≤ (k / t + 1)⁻¹ := (inv_le_inv₀ (Real.exp_pos _) (by positivity)).mpr h2
    _ = t / (k + t) := by
        have hpos : (0:ℝ) < k + t := by positivity
        field_simp [ht.ne', hpos.ne']
    _ ≤ t / k := by
        rw [div_le_div_iff₀ (by positivity) hk]
        nlinarith

lemma abs_gevreyInner_le (k : ℝ) (hk : 0 < k) (u : ℝ) :
    |gevreyInner k u| ≤ |1 - u ^ 2| / k := by
  rcases lt_or_ge (abs u) 1 with h | h
  · have hu2 : 0 < 1 - u ^ 2 := by nlinarith [abs_lt.1 h]
    rw [gevreyInner_of_abs_lt k u h, abs_of_pos (Real.exp_pos _),
      abs_of_pos hu2]
    exact exp_neg_div_le_div k hk _ hu2
  · rw [gevreyInner_of_one_le_abs k u h, abs_zero]
    positivity

lemma gevreyInner_hasDerivAt_of_abs_lt (k u : ℝ) (h : |u| < 1) :
    HasDerivAt (gevreyInner k)
      (Real.exp (-k / (1 - u ^ 2)) * (-k * (2 * u / (1 - u ^ 2) ^ 2))) u := by
  have hg : HasDerivAt (fun v : ℝ => 1 - v ^ 2) (-2 * u) u := by
    have h1 : HasDerivAt (fun v : ℝ => v ^ 2) (2 * u) u := by
      simpa using hasDerivAt_pow 2 u
    have h2 : HasDerivAt (fun v : ℝ => (1:ℝ) - v ^ 2) ((0:ℝ) - 2 * u) u :=
      HasDerivAt.sub (hasDerivAt_const u (1:ℝ)) h1
    simpa using h2
  have hne : (1:ℝ) - u ^ 2 ≠ 0 := by
    have hu2 : u ^ 2 < 1 := by nlinarith [abs_lt.1 h]
    linarith
  have hinv : HasDerivAt (fun v : ℝ => (1 - v ^ 2)⁻¹)
      (2 * u / (1 - u ^ 2) ^ 2) u := by
    simpa using hg.inv hne
  have h2 : HasDerivAt (fun v : ℝ => -k * ((1 - v ^ 2)⁻¹))
      (-k * (2 * u / (1 - u ^ 2) ^ 2)) u :=
    HasDerivAt.const_mul (-k) hinv
  have hev : gevreyInner k =ᶠ[𝓝 u] fun v => Real.exp (-k * ((1 - v ^ 2)⁻¹)) :=
    Filter.eventuallyEq_of_mem
      ((isOpen_lt continuous_abs continuous_const).mem_nhds h)
      fun v hv => by
        have hv2 : |v| < 1 := hv
        rw [gevreyInner_of_abs_lt k v hv2, div_eq_inv_mul, mul_comm]
  exact hev.hasDerivAt_iff.2 h2.exp

lemma gevreyInner_hasDerivAt_of_one_lt_abs (k u : ℝ) (h : 1 < |u|) :
    HasDerivAt (gevreyInner k) 0 u := by
  have hev : gevreyInner k =ᶠ[𝓝 u] fun _ => (0:ℝ) :=
    Filter.eventuallyEq_of_mem
      ((isOpen_lt continuous_const continuous_abs).mem_nhds h)
      fun v hv => gevreyInner_of_one_le_abs k v (le_of_lt hv)
  exact hev.hasDerivAt_iff.2 (hasDerivAt_const u (0:ℝ))

/-- The glue is flat: the boundary derivative is `0`. -/
lemma gevreyInner_hasDerivAt_abs_one (k : ℝ) (hk : 0 < k) (u : ℝ)
    (h : |u| = 1) : HasDerivAt (gevreyInner k) 0 u := by
  have hf0 : gevreyInner k u = 0 := gevreyInner_of_one_le_abs k u (le_of_eq h.symm)
  have g0 : Tendsto (fun w : ℝ => if w = 0 then (0:ℝ)
      else 6 / k * Real.exp (-k / (6 * |w|))) (𝓝 0) (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro eps hpe
    have hk6 : (0:ℝ) < 6 / k := by positivity
    have hq0 : (0:ℝ) < min (eps * k / 6) 1 := lt_min (by positivity) zero_lt_one
    have hc1 : (1:ℝ) ≤ max 1 (-(Real.log (min (eps * k / 6) 1))) :=
      le_max_left _ _
    have hclog : -(Real.log (min (eps * k / 6) 1)) ≤
        max 1 (-(Real.log (min (eps * k / 6) 1))) := le_max_right _ _
    have hx : (0:ℝ) < k / (6 * max 1 (-(Real.log (min (eps * k / 6) 1)))) := by
      positivity
    have hmem : {w : ℝ | |w| < k / (6 * max 1 (-(Real.log (min (eps * k / 6) 1))))}
        ∈ 𝓝 (0:ℝ) := by
      refine mem_nhds_iff.mpr ⟨Ioo _ _, fun w hw => abs_lt.mpr (mem_Ioo.mp hw),
        isOpen_Ioo, ⟨by linarith, hx⟩⟩
    filter_upwards [hmem] with w hw
    by_cases hw0 : w = 0
    · simpa [hw0] using hpe
    · have hwpos : (0:ℝ) < |w| := abs_pos.mpr hw0
      have hkey : max 1 (-(Real.log (min (eps * k / 6) 1))) < k / (6 * |w|) := by
        rw [lt_div_iff₀ (by positivity : (0:ℝ) < 6 * |w|)]
        have h1 : |w| * (6 * max 1 (-(Real.log (min (eps * k / 6) 1)))) < k := by
          calc |w| * (6 * max 1 (-(Real.log (min (eps * k / 6) 1)))) <
              k / (6 * max 1 (-(Real.log (min (eps * k / 6) 1)))) *
                (6 * max 1 (-(Real.log (min (eps * k / 6) 1)))) :=
                mul_lt_mul_of_pos_right hw (by positivity)
            _ = k := by field_simp
        nlinarith
      have hexp : Real.exp (-k / (6 * |w|)) < min (eps * k / 6) 1 := by
        have h1 : -k / (6 * |w|) < -max 1 (-(Real.log (min (eps * k / 6) 1))) := by
          rw [neg_div]
          linarith
        have h2 : Real.exp (-k / (6 * |w|)) < Real.exp (-max 1
            (-(Real.log (min (eps * k / 6) 1)))) := Real.exp_lt_exp.mpr h1
        refine lt_of_lt_of_le h2 ?_
        have h3 : Real.exp (-max 1 (-(Real.log (min (eps * k / 6) 1)))) ≤
            Real.exp (Real.log (min (eps * k / 6) 1)) := by
          refine Real.exp_le_exp.mpr ?_
          linarith
        rwa [Real.exp_log hq0] at h3
      have hgt : (0:ℝ) < 6 / k * Real.exp (-k / (6 * |w|)) :=
        mul_pos hk6 (Real.exp_pos _)
      rw [Real.dist_eq, sub_zero, if_neg hw0, abs_of_pos hgt]
      calc (6:ℝ) / k * Real.exp (-k / (6 * |w|))
          < 6 / k * min (eps * k / 6) 1 := mul_lt_mul_of_pos_left hexp hk6
        _ ≤ eps := by
            have h2 : (6:ℝ) / k * (eps * k / 6) = eps := by field_simp
            calc (6:ℝ) / k * min (eps * k / 6) 1
                  ≤ (6:ℝ) / k * (eps * k / 6) :=
                  mul_le_mul_of_nonneg_left (min_le_left _ _) hk6.le
              _ = eps := h2
  have key : ∀ w : ℝ, ‖w‖⁻¹ * ‖gevreyInner k (u + w)‖
      ≤ (if w = 0 then (0:ℝ) else 6 / k * Real.exp (-k / (6 * |w|))) := by
    intro w
    by_cases hw : w = 0
    · subst hw
      simp [hf0]
    · rw [if_neg hw]
      by_cases hy : |u + w| < 1
      · have hy0 : 0 < 1 - (u + w) ^ 2 := by nlinarith [abs_lt.1 hy]
        have hdle : 1 - (u + w) ^ 2 ≤ 3 * |w| := by
          rcases le_or_gt 0 u with hup | hup
          · rw [abs_of_nonneg hup] at h
            rw [h]
            have hwneg : w < 0 := by linarith [abs_lt.1 hy]
            have hwle : w - 1 ≤ 0 := by linarith
            rw [abs_of_neg hwneg]
            nlinarith
          · rw [abs_of_neg hup] at h
            have h2 : u = -1 := by linarith
            rw [h2]
            have hwpos : 0 < w := by linarith [abs_lt.1 hy]
            rw [abs_of_pos hwpos]
            nlinarith
        have h3w : (0:ℝ) < 3 * |w| := by positivity
        have hstep : Real.exp (-k / (1 - (u + w) ^ 2))
            ≤ Real.exp (-k / (3 * |w|)) := by
          refine Real.exp_le_exp.mpr ?_
          have h2 : k / (3 * |w|) ≤ k / (1 - (u + w) ^ 2) := by
            rw [div_le_div_iff₀ h3w hy0]
            exact mul_le_mul_of_nonneg_left hdle hk.le
          rw [neg_div, neg_div]
          exact neg_le_neg h2
        have h3s : Real.exp (-k / (3 * |w|))
            = Real.exp (-k / (6 * |w|)) * Real.exp (-k / (6 * |w|)) := by
          rw [← Real.exp_add]
          congr 1
          ring
        have hYb : Real.exp (-k / (6 * |w|)) ≤ 6 * |w| / k :=
          exp_neg_div_le_div k hk _ (by positivity)
        simp only [gevreyInner_of_abs_lt k (u + w) hy, Real.norm_eq_abs,
          abs_of_pos (Real.exp_pos _)]
        calc |w|⁻¹ * Real.exp (-k / (1 - (u + w) ^ 2))
            ≤ |w|⁻¹ * (Real.exp (-k / (6 * |w|)) * Real.exp (-k / (6 * |w|))) :=
              mul_le_mul_of_nonneg_left (le_trans hstep (le_of_eq h3s))
                (inv_nonneg.2 (abs_nonneg w))
          _ = |w|⁻¹ * Real.exp (-k / (6 * |w|)) * Real.exp (-k / (6 * |w|)) := by
              ring
          _ ≤ 6 / k * Real.exp (-k / (6 * |w|)) := by
              refine mul_le_mul_of_nonneg_right ?_ (Real.exp_nonneg _)
              have hmul := mul_le_mul_of_nonneg_left hYb
                (inv_nonneg.2 (abs_nonneg w))
              have hdiv : |w|⁻¹ * (6 * |w| / k) = 6 / k := by
                field_simp
              exact le_trans hmul hdiv.le
      · rw [gevreyInner_of_one_le_abs k (u + w) (not_lt.mp hy), norm_zero,
          mul_zero]
        exact mul_nonneg (div_nonneg (by positivity) hk.le)
          (Real.exp_nonneg _)
  have hmain : Tendsto (fun w : ℝ => ‖w‖⁻¹ * ‖gevreyInner k (u + w)‖)
      (𝓝 0) (𝓝 0) :=
    squeeze_zero (fun w => mul_nonneg (inv_nonneg.2 (norm_nonneg w))
      (norm_nonneg _)) key g0
  have hsub : Tendsto (fun x' : ℝ => ‖x' - u‖⁻¹ * ‖gevreyInner k x'‖)
      (𝓝 u) (𝓝 0) := by
    have hsub' : Tendsto (fun x' : ℝ => x' - u) (𝓝 u) (𝓝 0) := by
      have h : Tendsto (fun x' : ℝ => x' - u) (𝓝 u) (𝓝 (u - u)) :=
        ((continuous_id.sub continuous_const).continuousAt (x := u)).tendsto
      rw [sub_self] at h
      exact h
    refine hmain.comp hsub' |>.congr' ?_
    filter_upwards with x'
    simp
  rw [hasDerivAt_iff_tendsto, hf0]
  simpa only [sub_zero, smul_zero] using hsub

/-- Continuity everywhere: each point already carries a `HasDerivAt`. -/
lemma continuous_gevreyInner (k : ℝ) (hk : 0 < k) :
    Continuous (gevreyInner k) := by
  rw [continuous_iff_continuousAt]
  intro u
  rcases lt_trichotomy (abs u) 1 with h | h | h
  · exact (gevreyInner_hasDerivAt_of_abs_lt k u h).continuousAt
  · exact (gevreyInner_hasDerivAt_abs_one k hk u h).continuousAt
  · exact (gevreyInner_hasDerivAt_of_one_lt_abs k u h).continuousAt

lemma differentiable_gevreyInner (k : ℝ) (hk : 0 < k) :
    Differentiable ℝ (gevreyInner k) := by
  intro u
  rcases lt_trichotomy (abs u) 1 with h | h | h
  · exact (gevreyInner_hasDerivAt_of_abs_lt k u h).differentiableAt
  · exact (gevreyInner_hasDerivAt_abs_one k hk u h).differentiableAt
  · exact (gevreyInner_hasDerivAt_of_one_lt_abs k u h).differentiableAt
