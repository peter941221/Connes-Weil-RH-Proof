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
open Filter
open scoped Topology

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

private theorem quarter_series_reciprocal_difference_hasSum :
    HasSum (fun n : ℕ =>
      ((n : ℝ) + 1 / 4)⁻¹ - ((n : ℝ) + 1 + 1 / 4)⁻¹) 4 := by
  have hnonneg : ∀ n : ℕ,
      0 ≤ ((n : ℝ) + 1 / 4)⁻¹ - ((n : ℝ) + 1 + 1 / 4)⁻¹ := by
    intro n
    have h₁ : 0 < (n : ℝ) + 1 / 4 := by positivity
    have h₂ : 0 < (n : ℝ) + 1 + 1 / 4 := by positivity
    have hle : (n : ℝ) + 1 / 4 ≤ (n : ℝ) + 1 + 1 / 4 := by linarith
    exact sub_nonneg.mpr ((inv_le_inv₀ h₂ h₁).2 hle)
  have hpartial : ∀ N : ℕ,
      (∑ n ∈ Finset.range N,
        (((n : ℝ) + 1 / 4)⁻¹ - ((n : ℝ) + 1 + 1 / 4)⁻¹)) =
        4 - ((N : ℝ) + 1 / 4)⁻¹ := by
    intro N
    induction N with
    | zero => norm_num
    | succ N ih =>
        rw [Finset.sum_range_succ, ih]
        have hcast : ((N.succ : ℕ) : ℝ) + 1 / 4 =
            (N : ℝ) + 1 + 1 / 4 := by
          push_cast
          ring
        rw [hcast]
        ring
  have hzero : Tendsto (fun N : ℕ => ((N : ℝ) + 1 / 4)⁻¹)
      atTop (𝓝 (0 : ℝ)) := by
    exact tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right atTop (1 / 4 : ℝ)
        tendsto_natCast_atTop_atTop)
  apply (hasSum_iff_tendsto_nat_of_nonneg hnonneg 4).mpr
  have hlim : Tendsto (fun N : ℕ =>
      ∑ n ∈ Finset.range N,
        (((n : ℝ) + 1 / 4)⁻¹ - ((n : ℝ) + 1 + 1 / 4)⁻¹))
      atTop (𝓝 (4 : ℝ)) := by
    have heq : (fun N : ℕ =>
        ∑ n ∈ Finset.range N,
          (((n : ℝ) + 1 / 4)⁻¹ - ((n : ℝ) + 1 + 1 / 4)⁻¹)) =
        (fun N : ℕ => 4 - ((N : ℝ) + 1 / 4)⁻¹) := by
      funext N
      exact hpartial N
    rw [heq]
    have hc : Tendsto (fun _ : ℕ => (4 : ℝ)) atTop (𝓝 (4 : ℝ)) :=
      tendsto_const_nhds
    simpa using hc.sub hzero
  exact hlim

private theorem quarter_series_tail_bound :
    ∑' n : ℕ, ((n : ℝ) + 1 + 1 / 4)⁻¹ ^ (2 : ℕ) ≤ 4 := by
  have hd := quarter_series_reciprocal_difference_hasSum.summable
  have hcomp : ∀ n : ℕ,
      ((n : ℝ) + 1 + 1 / 4)⁻¹ ^ (2 : ℕ) ≤
        ((n : ℝ) + 1 / 4)⁻¹ - ((n : ℝ) + 1 + 1 / 4)⁻¹ := by
    intro n
    have h₁ : 0 < (n : ℝ) + 1 / 4 := by positivity
    have h₂ : 0 < (n : ℝ) + 1 + 1 / 4 := by positivity
    have hle : (n : ℝ) + 1 / 4 ≤ (n : ℝ) + 1 + 1 / 4 := by linarith
    have hinv : ((n : ℝ) + 1 + 1 / 4)⁻¹ ≤
        ((n : ℝ) + 1 / 4)⁻¹ := (inv_le_inv₀ h₂ h₁).2 hle
    have hdiff : ((n : ℝ) + 1 / 4)⁻¹ - ((n : ℝ) + 1 + 1 / 4)⁻¹ =
        ((n : ℝ) + 1 / 4)⁻¹ * ((n : ℝ) + 1 + 1 / 4)⁻¹ := by
      field_simp
      ring
    rw [hdiff]
    simpa [pow_two] using
      (mul_le_mul_of_nonneg_right hinv (inv_nonneg.mpr h₂.le))
  have htailSummable : Summable (fun n : ℕ =>
      ((n : ℝ) + 1 + 1 / 4)⁻¹ ^ (2 : ℕ)) :=
    hd.of_nonneg_of_le (fun n => by positivity) hcomp
  exact (htailSummable.tsum_le_tsum hcomp hd).trans_eq
    quarter_series_reciprocal_difference_hasSum.tsum_eq

theorem quarter_series_tsum_le_twenty :
    ∑' n : ℕ, ((n : ℝ) + 1 / 4)⁻¹ ^ (2 : ℕ) ≤ 20 := by
  have hsplit := quarter_series_summable.sum_add_tsum_nat_add 1
  have htail : ∑' n : ℕ, ((n : ℝ) + 1 + 1 / 4)⁻¹ ^ (2 : ℕ) ≤ 4 :=
    quarter_series_tail_bound
  have hsum :
      ∑' n : ℕ, ((n : ℝ) + 1 / 4)⁻¹ ^ (2 : ℕ) =
        ((0 : ℝ) + 1 / 4)⁻¹ ^ (2 : ℕ) +
          ∑' n : ℕ, ((n : ℝ) + 1 + 1 / 4)⁻¹ ^ (2 : ℕ) := by
    simpa [Finset.sum_range_succ, add_comm, add_left_comm, add_assoc] using hsplit.symm
  rw [hsum]
  have hzero : ((0 : ℝ) + 1 / 4)⁻¹ ^ (2 : ℕ) = 16 := by norm_num
  rw [hzero]
  linarith

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

theorem hasDerivAt_digamma_of_re_ge_quarter
    {z : ℂ} (hz : z ∈ quarterHalfPlane) :
    HasDerivAt Complex.digamma
      (∑' n : ℕ, (z + (n : ℂ))⁻¹ ^ (2 : ℕ)) z := by
  have hseries := hasDerivAt_halfAnchorReciprocalSeries_of_re_ge_quarter hz
  have heq :
      (fun w : ℂ => Complex.digamma w - Complex.digamma (1 / 2 : ℂ)) =ᶠ[𝓝 z]
        (fun w : ℂ => ∑' n : ℕ,
          (((n : ℂ) + (1 / 2 : ℂ))⁻¹ - (w + (n : ℂ))⁻¹)) := by
    filter_upwards [quarterHalfPlane_isOpen.mem_nhds hz] with w hw
    have hwpos : 0 < w.re := lt_trans (by norm_num) hw
    simpa only [add_comm] using
      (Source.C1XiCenterTwoGamma.halfAnchorGaussReciprocalSeries_eq_digamma_sub_half_of_pos
        hwpos).symm
  have hminus := hseries.congr_of_eventuallyEq heq
  have hfull := hminus.add_const (Complex.digamma (1 / 2 : ℂ))
  simpa [sub_add_cancel] using hfull

private theorem quarter_series_cubic_summable :
    Summable (fun n : ℕ => ((n : ℝ) + 1 / 4)⁻¹ ^ (3 : ℕ)) := by
  refine (quarter_series_summable.mul_left 4).of_nonneg_of_le
    (fun n => by positivity) ?_
  intro n
  have hn : 0 < (n : ℝ) + 1 / 4 := by positivity
  have hinv : ((n : ℝ) + 1 / 4)⁻¹ ≤ (4 : ℝ) := by
    calc
      ((n : ℝ) + 1 / 4)⁻¹ ≤ (1 / 4 : ℝ)⁻¹ := by
        exact (inv_le_inv₀ hn (by norm_num)).2 (by nlinarith)
      _ = 4 := by norm_num
  calc
    ((n : ℝ) + 1 / 4)⁻¹ ^ (3 : ℕ) =
        ((n : ℝ) + 1 / 4)⁻¹ ^ (2 : ℕ) *
          ((n : ℝ) + 1 / 4)⁻¹ := by ring
    _ ≤ ((n : ℝ) + 1 / 4)⁻¹ ^ (2 : ℕ) * 4 := by
      exact mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = 4 * ((n : ℝ) + 1 / 4)⁻¹ ^ (2 : ℕ) := by ring

theorem hasDerivAt_digamma_deriv_of_re_ge_quarter
    {z : ℂ} (hz : z ∈ quarterHalfPlane) :
    HasDerivAt (deriv Complex.digamma)
      (∑' n : ℕ, (-2 : ℂ) * (z + (n : ℂ))⁻¹ ^ (3 : ℕ)) z := by
  let g : ℕ → ℂ → ℂ := fun n w => (w + (n : ℂ))⁻¹ ^ (2 : ℕ)
  let g' : ℕ → ℂ → ℂ := fun n w =>
    (-2 : ℂ) * (w + (n : ℂ))⁻¹ ^ (3 : ℕ)
  have hbase : Summable (fun n : ℕ => g n (1 : ℂ)) := by
    apply Summable.of_norm
    have hreal : Summable (fun n : ℕ => ((n : ℝ) + 1)⁻¹ ^ (2 : ℕ)) := by
      refine quarter_series_summable.of_nonneg_of_le
        (fun n => by positivity) ?_
      intro n
      have h₁ : 0 < (n : ℝ) + 1 := by positivity
      have h₂ : 0 < (n : ℝ) + 1 / 4 := by positivity
      exact (sq_le_sq₀ (inv_nonneg.mpr h₁.le) (inv_nonneg.mpr h₂.le)).mpr
        ((inv_le_inv₀ h₁ h₂).2 (by linarith))
    have hcomplex := summable_ofReal.mpr hreal
    refine hcomplex.norm.congr ?_
    intro n
    simp [g, add_comm, norm_pow, norm_inv, Complex.normSq]
  have hderiv : ∀ n w, w ∈ quarterHalfPlane → HasDerivAt (g n) (g' n w) w := by
    intro n w hw
    have hne : w + (n : ℂ) ≠ 0 := by
      intro h
      have hre : (w + (n : ℂ)).re = (n : ℝ) + w.re := by simp; ring
      rw [h, Complex.zero_re] at hre
      have hw' : (1 / 4 : ℝ) < w.re := hw
      nlinarith [show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n]
    have hi := (hasDerivAt_id w).add_const (n : ℂ)
    have hinv := hi.inv hne
    have hpow := hinv.pow 2
    convert hpow using 1
    simp [Function.comp_def, id_eq, g, g', inv_pow, mul_assoc,
      mul_left_comm, mul_comm]
    field_simp [hne] <;> ring
  have hbound : ∀ n w, w ∈ quarterHalfPlane → ‖g' n w‖ ≤
      2 * ((n : ℝ) + 1 / 4)⁻¹ ^ (3 : ℕ) := by
    intro n w hw
    dsimp [g']
    calc
      ‖(-2 : ℂ) * (w + (n : ℂ))⁻¹ ^ (3 : ℕ)‖ =
          2 * ‖(w + (n : ℂ))⁻¹ ^ (3 : ℕ)‖ := by
            rw [norm_mul, norm_neg, norm_ofNat]
      _ ≤ 2 * ((n : ℝ) + 1 / 4)⁻¹ ^ (3 : ℕ) := by
        gcongr
        rw [norm_pow, norm_inv]
        have hreal : (1 / 4 : ℝ) < w.re := hw
        have hnorm : (n : ℝ) + 1 / 4 ≤ ‖w + (n : ℂ)‖ := by
          have hre : (n : ℝ) + 1 / 4 < (w + (n : ℂ)).re := by
            simp [Complex.add_re]
            linarith
          exact hre.le.trans (le_trans (le_abs_self _) (Complex.abs_re_le_norm _))
        have hne : w + (n : ℂ) ≠ 0 := by
          intro h
          have hre : (w + (n : ℂ)).re = (n : ℝ) + w.re := by simp; ring
          rw [h, Complex.zero_re] at hre
          have hreal : (1 / 4 : ℝ) < w.re := hw
          nlinarith [show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n]
        have hnormpos : 0 < ‖w + (n : ℂ)‖ := norm_pos_iff.mpr hne
        have hrealpos : 0 < (n : ℝ) + 1 / 4 := by positivity
        have hinvle : ‖w + (n : ℂ)‖⁻¹ ≤
            ((n : ℝ) + 1 / 4)⁻¹ :=
          (inv_le_inv₀ hnormpos hrealpos).2 hnorm
        exact pow_le_pow_left₀ (by positivity) hinvle 3
  have hpoint : (1 : ℂ) ∈ quarterHalfPlane := by norm_num [quarterHalfPlane]
  have hsum := hasDerivAt_tsum_of_isPreconnected
    (u := fun n : ℕ => 2 * ((n : ℝ) + 1 / 4)⁻¹ ^ (3 : ℕ))
    (g := g) (g' := g') (quarter_series_cubic_summable.mul_left 2)
    quarterHalfPlane_isOpen quarterHalfPlane_isPreconnected hderiv hbound
    hpoint hbase hz
  have heq : (fun w : ℂ => deriv Complex.digamma w) =ᶠ[𝓝 z]
      (fun w : ℂ => ∑' n : ℕ, g n w) := by
    filter_upwards [quarterHalfPlane_isOpen.mem_nhds hz] with w hw
    rw [(hasDerivAt_digamma_of_re_ge_quarter hw).deriv]
  have hsum' := hsum.congr_of_eventuallyEq heq
  dsimp [g, g'] at hsum'
  simpa [mul_assoc, mul_left_comm, mul_comm] using hsum'

theorem norm_digamma_deriv_le_twenty
    {z : ℂ} (hz : z ∈ quarterHalfPlane) :
    ‖deriv Complex.digamma z‖ ≤ 20 := by
  have hsum : Summable (fun n : ℕ =>
      ‖(z + (n : ℂ))⁻¹ ^ (2 : ℕ)‖) :=
    quarter_series_summable.of_nonneg_of_le
      (fun n => norm_nonneg _)
      (fun n => quarter_series_deriv_bound hz n)
  have hnorm : ‖∑' n : ℕ, (z + (n : ℂ))⁻¹ ^ (2 : ℕ)‖ ≤
      ∑' n : ℕ, ((n : ℝ) + 1 / 4)⁻¹ ^ (2 : ℕ) := by
    exact (norm_tsum_le_tsum_norm hsum).trans
      (hsum.tsum_le_tsum (fun n => quarter_series_deriv_bound hz n)
        quarter_series_summable)
  rw [(hasDerivAt_digamma_of_re_ge_quarter hz).deriv]
  exact hnorm.trans quarter_series_tsum_le_twenty

theorem summable_digamma_canonical_series_of_re_ge_quarter
    {z : ℂ} (hz : z ∈ quarterHalfPlane) :
    Summable (fun n : ℕ =>
      ((n : ℂ) + 1)⁻¹ - ((n : ℂ) + z)⁻¹) := by
  have hanchor : Summable (fun n : ℕ =>
      ((n : ℂ) + (1 / 2 : ℂ))⁻¹ - ((n : ℂ) + (1 : ℂ))⁻¹) := by
    simpa using
      (Source.C1XiCenterTwoGamma.summable_halfAnchorGaussReciprocalSeries
        (z := (1 : ℂ)) (by norm_num))
  have hzpos : 0 < z.re := lt_trans (by norm_num) hz
  have hzseries :=
    Source.C1XiCenterTwoGamma.summable_halfAnchorGaussReciprocalSeries
      (z := z) hzpos
  have hsum := hanchor.neg.add hzseries
  refine hsum.congr ?_
  intro n
  ring

theorem summable_norm_digamma_canonical_series_of_re_ge_quarter
    {z : ℂ} (hz : z ∈ quarterHalfPlane) :
    Summable (fun n : ℕ => ‖((n : ℂ) + 1)⁻¹ - ((n : ℂ) + z)⁻¹‖) :=
  (summable_digamma_canonical_series_of_re_ge_quarter hz).norm

end Dev
end ConnesWeilRH
