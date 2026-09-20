/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import ConnesWeilRH.Dev.C1XiCenterTwoGamma

/-!
# The digamma vertical-line bound (record 1734, the Lemma-B face)

Record 1734 section 2 prices the annular phase by LINEAR growth of the
digamma function on the half-plane `Re w ≥ 1/4`.  No Stirling machine is
needed: the committed phase is only ever evaluated on the vertical line,
where every reciprocal-series term depends on `w` through `Re w` alone.

This leaf lands that face formally, from three committed inputs:

1. the reciprocal-series anchor
   `Source.C1XiCenterTwoGamma.halfAnchorGaussReciprocalSeries_eq_digamma_sub_half`,
2. the recurrence `Complex.digamma_apply_add_one`
   (`digamma (s+1) = digamma s + s⁻¹`),
3. the elementary inequality `(n + 3/2) ≤ (6/5) · (n + 5/4)` — equivalent to
   `n ≥ 0` — which prices each series term by the telescoping half-anchor
   difference, whose total is `2` (the real face of
   `halfAnchorShiftReciprocalSeries_eq_two`, proved here directly).

Result: for `1/4 ≤ w.re`,
`‖digamma w‖ ≤ (‖digamma (1/2)‖ + 4 + 6/5) + (12/5) · ‖w‖`,
with `‖digamma (1/2)‖ = 2 log 2 + |γ_E|` on paper
(`Complex.digamma_one_half`), kept abstract here since only finiteness of
the constant matters downstream.

No carrier object, no root convolution, and no sign is touched here.
-/

namespace ConnesWeilRH
namespace Dev

open MeasureTheory
open Filter
open scoped Real

section DigammaLine

/-- The telescoping half-anchor difference is nonnegative. -/
private theorem real_halfAnchorShift_nonneg (n : ℕ) :
    (0:ℝ) ≤ ((n:ℝ)+1/2)⁻¹ - ((n:ℝ)+3/2)⁻¹ := by
  have hEq : ((n:ℝ)+1/2)⁻¹ - ((n:ℝ)+3/2)⁻¹
      = (1:ℝ)/(((n:ℝ)+1/2) * ((n:ℝ)+3/2)) := by
    field_simp
    ring
  rw [hEq]
  positivity

/-- The scaled telescoping half-anchor series has sum `2 * c`. -/
private theorem real_scaled_halfAnchorShift_hasSum (c : ℝ) (hc : 0 ≤ c) :
    HasSum (fun n : ℕ => (((n:ℝ)+1/2)⁻¹ - ((n:ℝ)+3/2)⁻¹) * c) (2 * c) := by
  have key : ∀ N : ℕ, (∑ i ∈ Finset.range N,
      (((i:ℝ)+1/2)⁻¹ - ((i:ℝ)+3/2)⁻¹)) = (1/2:ℝ)⁻¹ - ((N:ℝ)+1/2)⁻¹ := by
    intro N
    induction N with
    | zero => norm_num
    | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      have hshift : (((N+1:ℕ):ℝ)+1/2) = ((N:ℝ)+3/2) := by
        push_cast
        ring
      rw [hshift]
      ring
  have hz : Tendsto (fun N : ℕ => ((N:ℝ)+1/2)⁻¹) atTop
      (nhds (0:ℝ)) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right atTop (1/2:ℝ)
        tendsto_natCast_atTop_atTop)
  have hps : ∀ N : ℕ, (∑ i ∈ Finset.range N,
      (((i:ℝ)+1/2)⁻¹ - ((i:ℝ)+3/2)⁻¹) * c)
      = ((1/2:ℝ)⁻¹ - ((N:ℝ)+1/2)⁻¹) * c := by
    intro N
    rw [← Finset.sum_mul, key N]
  have hlimc : Tendsto (fun N : ℕ => ∑ i ∈ Finset.range N,
      (((i:ℝ)+1/2)⁻¹ - ((i:ℝ)+3/2)⁻¹) * c) atTop (nhds ((2:ℝ) * c)) := by
    have heq : (fun N : ℕ => ∑ i ∈ Finset.range N,
        (((i:ℝ)+1/2)⁻¹ - ((i:ℝ)+3/2)⁻¹) * c)
        = fun N : ℕ => ((1/2:ℝ)⁻¹ - ((N:ℝ)+1/2)⁻¹) * c := by
      funext N
      exact hps N
    have hfix : ((1:ℝ)/2)⁻¹ = (2:ℝ) := by norm_num
    have h2 : Tendsto (fun N : ℕ => (2:ℝ) - ((N:ℝ)+1/2)⁻¹) atTop
        (nhds (2:ℝ)) := by
      have h1 : Tendsto (fun _ : ℕ => ((1:ℝ)/2)⁻¹) atTop
          (nhds (((1:ℝ)/2)⁻¹)) := tendsto_const_nhds
      have h3 := h1.sub hz
      simp only [sub_zero] at h3
      rwa [hfix] at h3
    rw [heq, hfix]
    exact h2.mul_const c
  exact (hasSum_iff_tendsto_nat_of_nonneg
    (fun n => mul_nonneg (real_halfAnchorShift_nonneg n) hc) (2 * c)).mpr hlimc

/-- One series term of `ψ(w)` is priced by the telescoping difference:
`|(n+1/2)⁻¹ - (n+w+1)⁻¹| ≤ ((n+1/2)⁻¹ - (n+3/2)⁻¹) · (6/5) · ‖w + 1/2‖`
whenever `Re w ≥ 1/4`. -/
private theorem annulus_digamma_term_le {w : ℂ} (hw : (1:ℝ) / 4 ≤ w.re) (n : ℕ) :
    ‖((n:ℂ)+(1/2:ℂ))⁻¹ - ((n:ℂ)+((w:ℂ)+1))⁻¹‖
      ≤ (((n:ℝ)+1/2)⁻¹ - ((n:ℝ)+3/2)⁻¹) * ((6/5:ℝ) * ‖w + (1/2:ℂ)‖) := by
  have hnn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
  have hden1 : (0:ℝ) < (n:ℝ) + 1/2 := by linarith
  have hden3 : (0:ℝ) < (n:ℝ) + 3/2 := by linarith
  have hden4 : (0:ℝ) < (n:ℝ) + 5/4 := by linarith
  -- cast coalescence (the working house idiom)
  have hcast : ((n:ℂ)+(1/2:ℂ)) = (((n:ℝ)+1/2:ℝ):ℂ) := by
    push_cast
    ring
  -- real-part extractions
  have hbre : ((n:ℂ)+((w:ℂ)+1)).re = (n:ℝ) + w.re + 1 := by
    simp [Complex.add_re, Complex.one_re]
    ring
  -- the two series denominators never vanish
  have ha0 : ((n:ℂ)+(1/2:ℂ)) ≠ 0 := by
    intro hEq
    have h1 : ((n:ℂ)+(1/2:ℂ)).re = (n:ℝ) + 1/2 := by
      rw [hcast, Complex.ofReal_re]
    have hpos : (0:ℝ) < (n:ℝ) + 1/2 := hden1
    rw [← h1, hEq, Complex.zero_re] at hpos
    linarith
  have hb0 : ((n:ℂ)+((w:ℂ)+1)) ≠ 0 := by
    intro hEq
    have hpos : (0:ℝ) < (n:ℝ) + w.re + 1 := by linarith
    rw [← hbre, hEq, Complex.zero_re] at hpos
    linarith
  -- algebra of the reciprocal difference (a pure field identity)
  have hsplit : ((n:ℂ)+(1/2:ℂ))⁻¹ - ((n:ℂ)+((w:ℂ)+1))⁻¹
      = (((n:ℂ)+((w:ℂ)+1)) - ((n:ℂ)+(1/2:ℂ)))
        / (((n:ℂ)+(1/2:ℂ)) * ((n:ℂ)+((w:ℂ)+1))) := by
    have hgen : ∀ x y : ℂ, x ≠ 0 → y ≠ 0 →
        x⁻¹ - y⁻¹ = (y - x) / (x * y) := by
      intro x y hx hy
      field_simp
    exact hgen ((n:ℂ)+(1/2:ℂ)) ((n:ℂ)+((w:ℂ)+1)) ha0 hb0
  have hsub : (((n:ℂ)+((w:ℂ)+1)) - ((n:ℂ)+(1/2:ℂ))) = w + (1/2:ℂ) := by
    ring
  have hanorm : ‖((n:ℂ)+(1/2:ℂ))‖ = ((n:ℝ)+1/2 : ℝ) := by
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  have hbpos : (0:ℝ) < ((n:ℂ)+((w:ℂ)+1)).re := by rw [hbre]; linarith
  have hb1 : ((n:ℝ) + 5/4 : ℝ) ≤ ‖((n:ℂ)+((w:ℂ)+1))‖ := by
    have h2 : ((n:ℝ) + 5/4 : ℝ) ≤ ((n:ℂ)+((w:ℂ)+1)).re := by rw [hbre]; linarith
    have h3 := Complex.abs_re_le_norm ((n:ℂ)+((w:ℂ)+1))
    rw [abs_of_pos hbpos] at h3
    exact le_trans h2 h3
  -- the (6/5) slack: (5/6)·(n + 3/2) ≤ n + 5/4, i.e. n ≥ 0
  have hkey : ((1:ℝ)/((n:ℝ)+5/4)) ≤ ((1:ℝ)/(((5:ℝ)/6) * ((n:ℝ)+3/2))) := by
    have h1 : ((5:ℝ)/6) * ((n:ℝ)+3/2) ≤ (n:ℝ) + 5/4 := by
      have h06 : ((5:ℝ)/6) * (n:ℝ) ≤ (n:ℝ) := by
        have h06' : ((5:ℝ)/6) * (n:ℝ) ≤ (1:ℝ) * (n:ℝ) :=
          mul_le_mul_of_nonneg_right (by norm_num : (5:ℝ)/6 ≤ (1:ℝ)) hnn
        rwa [one_mul] at h06'
      linarith
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) h1
  calc ‖((n:ℂ)+(1/2:ℂ))⁻¹ - ((n:ℂ)+((w:ℂ)+1))⁻¹‖
      = ‖(((n:ℂ)+((w:ℂ)+1)) - ((n:ℂ)+(1/2:ℂ)))
          / (((n:ℂ)+(1/2:ℂ)) * ((n:ℂ)+((w:ℂ)+1)))‖ := by rw [hsplit]
    _ = ‖w + (1/2:ℂ)‖ / (((n:ℝ)+1/2) * ‖((n:ℂ)+((w:ℂ)+1))‖) := by
        rw [hsub, norm_div, norm_mul, hanorm]
    _ ≤ ‖w + (1/2:ℂ)‖ / (((n:ℝ)+1/2) * ((n:ℝ)+5/4)) := by
        refine div_le_div_of_nonneg_left (norm_nonneg _)
          (by positivity) (mul_le_mul_of_nonneg_left hb1 hden1.le)
    _ ≤ (‖w + (1/2:ℂ)‖ * ((1:ℝ)/(((5:ℝ)/6) * ((n:ℝ)+3/2)))) / ((n:ℝ)+1/2) := by
        have h1 : ‖w + (1/2:ℂ)‖ / (((n:ℝ)+1/2) * ((n:ℝ)+5/4))
            = (‖w + (1/2:ℂ)‖ * ((1:ℝ)/((n:ℝ)+5/4))) / ((n:ℝ)+1/2) := by
          field_simp
        rw [h1]
        refine (div_le_div_iff_of_pos_right hden1).mpr ?_
        exact mul_le_mul_of_nonneg_left hkey (norm_nonneg _)
    _ = ((6/5:ℝ) * ‖w + (1/2:ℂ)‖) / (((n:ℝ)+1/2) * ((n:ℝ)+3/2)) := by
        field_simp
    _ = (((n:ℝ)+1/2)⁻¹ - ((n:ℝ)+3/2)⁻¹) * ((6/5:ℝ) * ‖w + (1/2:ℂ)‖) := by
        have h2 : ((n:ℝ)+1/2)⁻¹ - ((n:ℝ)+3/2)⁻¹
            = (1:ℝ)/(((n:ℝ)+1/2) * ((n:ℝ)+3/2)) := by
          field_simp
          ring
        rw [h2, one_div_mul_eq_div]

/-- **Linear growth of digamma on the vertical half-line** (record 1734,
the Lemma-B face): for `1/4 ≤ w.re`,
`‖ψ(w)‖ ≤ (‖ψ(1/2)‖ + 4 + 6/5) + (12/5) · ‖w‖`. -/
theorem abs_digamma_le_of_re_ge_quarter {w : ℂ} (hw : (1:ℝ) / 4 ≤ w.re) :
    ‖Complex.digamma w‖
      ≤ (‖Complex.digamma ((1/2:ℂ))‖ + 4 + 6/5) + (12/5:ℝ) * ‖w‖ := by
  -- the recurrence never fails on the closed half-plane
  have hwne : ∀ m : ℕ, w ≠ -(m:ℂ) := by
    intro m hEq
    have h1 : (1:ℝ)/4 ≤ w.re := hw
    rw [hEq, Complex.neg_re] at h1
    have h2 : ((m:ℂ)).re = (m:ℝ) := by
      simp
    rw [h2] at h1
    have h3 : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
    linarith
  have hrec : Complex.digamma w = Complex.digamma (w+1) - (w:ℂ)⁻¹ := by
    have h := Complex.digamma_apply_add_one w hwne
    rw [h]
    ring
  have hz2 : (1:ℝ) < (w+1).re := by
    rw [Complex.add_re, Complex.one_re]
    linarith
  have hanchor : Complex.digamma (w+1)
      = Complex.digamma ((1/2:ℂ))
        + ∑' n : ℕ, (((n:ℂ)+(1/2:ℂ))⁻¹ - ((n:ℂ)+((w:ℂ)+1))⁻¹) := by
    have h :=
      Source.C1XiCenterTwoGamma.halfAnchorGaussReciprocalSeries_eq_digamma_sub_half
        (z := w+1) hz2
    rw [h]
    ring
  -- the series is priced by the telescoping total 2
  have hscale : (0:ℝ) ≤ (6/5:ℝ) * ‖w + (1/2:ℂ)‖ := by positivity
  have hghas := real_scaled_halfAnchorShift_hasSum
    ((6/5:ℝ) * ‖w + (1/2:ℂ)‖) hscale
  have hgbound : ∀ n : ℕ,
      ‖((n:ℂ)+(1/2:ℂ))⁻¹ - ((n:ℂ)+((w:ℂ)+1))⁻¹‖
        ≤ (((n:ℝ)+1/2)⁻¹ - ((n:ℝ)+3/2)⁻¹) * ((6/5:ℝ) * ‖w + (1/2:ℂ)‖) := by
    intro n
    exact annulus_digamma_term_le hw n
  have hcoeff : (2:ℝ) * ((6/5:ℝ) * ‖w + (1/2:ℂ)‖)
      = (12/5:ℝ) * ‖w + (1/2:ℂ)‖ := by ring
  have hser : ‖∑' n : ℕ, (((n:ℂ)+(1/2:ℂ))⁻¹ - ((n:ℂ)+((w:ℂ)+1))⁻¹)‖
      ≤ (12/5:ℝ) * ‖w + (1/2:ℂ)‖ := by
    have h := tsum_of_norm_bounded hghas hgbound
    rw [hcoeff] at h
    exact h
  -- |w⁻¹| ≤ 4 on Re w ≥ 1/4
  have habsre : |w.re| = w.re := abs_of_pos (by linarith)
  have hwbig : (1:ℝ)/4 ≤ ‖w‖ := by
    have h3 := Complex.abs_re_le_norm w
    rw [habsre] at h3
    exact le_trans hw h3
  have h41 : ((4:ℝ))⁻¹ = 1/4 := by norm_num
  have hinv : ‖(w:ℂ)⁻¹‖ ≤ (4:ℝ) := by
    rw [norm_inv]
    have h1 : ((4:ℝ))⁻¹ ≤ ‖w‖ := by rw [h41]; exact hwbig
    exact inv_le_of_inv_le₀ (by norm_num) h1
  -- ‖w + 1/2‖ ≤ ‖w‖ + 1/2
  have hw2 : ‖w + (1/2:ℂ)‖ ≤ ‖w‖ + 1/2 := by
    refine le_trans (norm_add_le w _) ?_
    norm_num
  have htri : ‖Complex.digamma (w+1)‖
      ≤ ‖Complex.digamma ((1/2:ℂ))‖
        + ‖∑' n : ℕ, (((n:ℂ)+(1/2:ℂ))⁻¹ - ((n:ℂ)+((w:ℂ)+1))⁻¹)‖ := by
    rw [hanchor]
    exact norm_add_le _ _
  calc ‖Complex.digamma w‖
      = ‖Complex.digamma (w+1) - (w:ℂ)⁻¹‖ := by rw [hrec]
    _ ≤ ‖Complex.digamma ((1/2:ℂ))‖
          + ‖∑' n : ℕ, (((n:ℂ)+(1/2:ℂ))⁻¹ - ((n:ℂ)+((w:ℂ)+1))⁻¹)‖
          + ‖(w:ℂ)⁻¹‖ := by
        refine le_trans (norm_sub_le _ _) ?_
        linarith [htri]
    _ ≤ (‖Complex.digamma ((1/2:ℂ))‖ + 4 + 6/5) + (12/5:ℝ) * ‖w‖ := by
        linarith [hser, hinv, hw2]

end DigammaLine

end Dev
end ConnesWeilRH
