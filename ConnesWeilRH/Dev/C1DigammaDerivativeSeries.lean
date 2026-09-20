/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license.
-/

import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.Convex
import ConnesWeilRH.Dev.C1XiCenterTwoGamma

/-!
# The differentiated reciprocal-series engine for the annular phase

This is the formal analytic core behind the uniform `psi'` estimate in the
1734 paper page.  It differentiates the half-anchor reciprocal series on the
open half-plane `Re z > 1/4`; the remaining identification with the
derivative of `Complex.digamma` is kept as a separate readback step.
-/

namespace ConnesWeilRH
namespace Dev

open Complex

private def quarterHalfPlane : Set ℂ := {z | (1 / 4 : ℝ) < z.re}

private theorem quarterHalfPlane_isOpen : IsOpen quarterHalfPlane := by
  exact isOpen_lt continuous_const continuous_re

private theorem quarterHalfPlane_isPreconnected :
    IsPreconnected quarterHalfPlane := by
  exact (convex_halfSpace_re_gt (1 / 4 : ℝ)).isPreconnected

private theorem quarter_series_summable :
    Summable (fun n : ℕ => ((n : ℝ) + 1 / 4)⁻¹ ^ (2 : ℕ)) := by
  have hpow : Summable (fun n : ℕ => ((n : ℝ) ^ (2 : ℕ))⁻¹) :=
    (Real.summable_nat_pow_inv (p := 2)).mpr (by norm_num)
  have htail0 : Summable (fun n : ℕ => ((n : ℝ) + 1)⁻¹ ^ (2 : ℕ)) := by
    simpa [Nat.cast_add, one_div, pow_two] using
      (summable_nat_add_iff (f := fun n : ℕ => ((n : ℝ) ^ (2 : ℕ))⁻¹) 1).mpr hpow
  have htail : Summable (fun n : ℕ =>
      (16 : ℝ) * ((n : ℝ) + 1)⁻¹ ^ (2 : ℕ)) := htail0.mul_left 16
  apply htail.of_norm_bounded_eventually_nat
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hden : (n : ℝ) + 1 ≤ 4 * ((n : ℝ) + 1 / 4) := by nlinarith
  have hpos : 0 < (n : ℝ) + 1 / 4 := by positivity
  have hdiv : ((n : ℝ) + 1) / 4 ≤ (n : ℝ) + 1 / 4 := by
    exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 4)).2 (by
      simpa [mul_comm] using hden)
  have hinv : ((n : ℝ) + 1 / 4)⁻¹ ≤ (4 : ℝ) * ((n : ℝ) + 1)⁻¹ := by
    calc
      ((n : ℝ) + 1 / 4)⁻¹ ≤ (((n : ℝ) + 1) / 4)⁻¹ := by
        have ha : 0 < (n : ℝ) + 1 / 4 := hpos
        have hb : 0 < ((n : ℝ) + 1) / 4 := by positivity
        exact (inv_le_inv₀ ha hb).2 hdiv
      _ = (4 : ℝ) * ((n : ℝ) + 1)⁻¹ := by field_simp
  have hnonneg : 0 ≤ ((n : ℝ) + 1 / 4)⁻¹ := le_of_lt (inv_pos.mpr hpos)
  have hnonneg' : 0 ≤ ((n : ℝ) + 1)⁻¹ := by positivity
  have hnonneg4 : 0 ≤ (4 : ℝ) * ((n : ℝ) + 1)⁻¹ := by positivity
  have hsq := (sq_le_sq₀ hnonneg hnonneg4).mpr hinv
  rw [norm_pow, Real.norm_eq_abs, abs_of_nonneg hnonneg]
  calc
    ((n : ℝ) + 1 / 4)⁻¹ ^ 2 ≤
        (4 * ((n : ℝ) + 1)⁻¹) ^ 2 := hsq
    _ = (16 : ℝ) * ((n : ℝ) + 1)⁻¹ ^ 2 := by
      field_simp
      norm_num

private theorem quarter_series_deriv_bound
    {z : ℂ} (hz : z ∈ quarterHalfPlane) (n : ℕ) :
    ‖(z + (n : ℂ))⁻¹ ^ (2 : ℕ)‖ ≤
      ((n : ℝ) + 1 / 4)⁻¹ ^ (2 : ℕ) := by
  have hreal : (1 / 4 : ℝ) < z.re := hz
  have hpos : 0 < (n : ℝ) + 1 / 4 := by positivity
  have hnorm : (n : ℝ) + 1 / 4 ≤ ‖z + (n : ℂ)‖ := by
    have hre : (n : ℝ) + 1 / 4 < (z + (n : ℂ)).re := by
      norm_num [Complex.add_re]
      linarith
    exact hre.le.trans (le_trans (le_abs_self _) (Complex.abs_re_le_norm _))
  rw [norm_pow, norm_inv]
  have hnz : 0 < ‖z + (n : ℂ)‖ := lt_of_lt_of_le hpos hnorm
  have hinv : ‖z + (n : ℂ)‖⁻¹ ≤ ((n : ℝ) + 1 / 4)⁻¹ :=
    (inv_le_inv₀ hnz hpos).2 hnorm
  have hna : 0 ≤ ‖z + (n : ℂ)‖⁻¹ := le_of_lt (inv_pos.mpr hnz)
  have hnb : 0 ≤ ((n : ℝ) + 1 / 4)⁻¹ := le_of_lt (inv_pos.mpr hpos)
  exact (sq_le_sq₀ hna hnb).mpr hinv

theorem hasDerivAt_halfAnchorReciprocalSeries_of_re_ge_quarter
    {z : ℂ} (hz : z ∈ quarterHalfPlane) :
    HasDerivAt
      (fun w : ℂ => ∑' n : ℕ,
        (((n : ℂ) + (1 / 2 : ℂ))⁻¹ - (w + (n : ℂ))⁻¹))
      (∑' n : ℕ, (z + (n : ℂ))⁻¹ ^ (2 : ℕ)) z := by
  let g : ℕ → ℂ → ℂ := fun n w =>
    ((n : ℂ) + (1 / 2 : ℂ))⁻¹ - (w + (n : ℂ))⁻¹
  let g' : ℕ → ℂ → ℂ := fun n w => (w + (n : ℂ))⁻¹ ^ (2 : ℕ)
  have hbase : Summable (fun n : ℕ =>
      ((n : ℂ) + (1 / 2 : ℂ))⁻¹ - ((n : ℂ) + (1 : ℂ))⁻¹) := by
    simpa using
      (Source.C1XiCenterTwoGamma.summable_halfAnchorGaussReciprocalSeries
        (z := (1 : ℂ)) (by norm_num))
  have hderiv : ∀ n w, w ∈ quarterHalfPlane → HasDerivAt (g n) (g' n w) w := by
    intro n w hw
    have hne : w + (n : ℂ) ≠ 0 := by
      intro h
      have : 0 < (n : ℝ) + 1 / 4 := by positivity
      have hre : (w + (n : ℂ)).re = (n : ℝ) + w.re := by
        simp
        ring
      rw [h, Complex.zero_re] at hre
      have hw' : (1 / 4 : ℝ) < w.re := hw
      have hn' : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      nlinarith
    have hi := (hasDerivAt_id w).add_const (n : ℂ)
    have hinv := hi.inv hne
    have hterm :=
      (hasDerivAt_const w (((n : ℂ) + (1 / 2 : ℂ))⁻¹)).sub hinv
    convert hterm using 1
    · change (w + (n : ℂ))⁻¹ ^ 2 = 0 - -1 / (w + (n : ℂ)) ^ 2
      simp [div_eq_mul_inv, inv_pow]
  have hbound : ∀ n w, w ∈ quarterHalfPlane → ‖(g' n w)‖ ≤
      ((n : ℝ) + 1 / 4)⁻¹ ^ (2 : ℕ) := by
    intro n w hw
    exact quarter_series_deriv_bound hw n
  have hpoint : (1 : ℂ) ∈ quarterHalfPlane := by norm_num [quarterHalfPlane]
  have hsum := hasDerivAt_tsum_of_isPreconnected
    (u := fun n : ℕ => ((n : ℝ) + 1 / 4)⁻¹ ^ (2 : ℕ))
    (g := g) (g' := g') quarter_series_summable quarterHalfPlane_isOpen
    quarterHalfPlane_isPreconnected hderiv hbound hpoint
    (by simpa [g, add_comm] using hbase) hz
  dsimp [g, g'] at hsum
  change HasDerivAt
    (fun w : ℂ => ∑' n : ℕ,
      (((n : ℂ) + (1 / 2 : ℂ))⁻¹ - (w + (n : ℂ))⁻¹))
    (∑' n : ℕ, (z + (n : ℂ))⁻¹ ^ (2 : ℕ)) z at hsum
  exact hsum

end Dev
end ConnesWeilRH
