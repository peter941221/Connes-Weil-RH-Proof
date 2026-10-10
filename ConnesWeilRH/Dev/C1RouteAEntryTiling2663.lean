import ConnesWeilRH.Dev.C1RouteAAnalyticMomentNormalization2618
import ConnesWeilRH.Dev.C1RouteACorrectionCaptureParameters2584
import ConnesWeilRH.Dev.C1RouteAAdaptiveN05440Minus2542

/-! # Record 2663: the (0,3) entry partition — tiling, edge slices, glue

This module assembles the geometric half of the record-2624 GO-route pilot
for the first off-diagonal moment entry: the entry `(0,3)` integral of
`momentEntry2351` is normalized to `storedWidth 3 ^ 2 • ∫_{-1}^{1} entryF`,
the central window `[-19/20, 19/20]` is tiled by the 190 committed panels
`a k = -19/20 + k/100` (Mathlib `sum_integral_adjacent_intervals_Ico`), and
the two edge slices are bounded by the base-2 exponential bar `2 ^ (-302)`
(from `|Re(node0) * r3^2| <= 51923/10000`, so the exponent real part is at
most `-605/2` on `19/20 <= |x| <= 1`).

Scope: the tiling and edge statements here are exact (no numeric slack);
the per-panel L1-ball input comes from the committed record-2662 panel
theorems, and the final numeric close against
`analyticMomentInterval2597 0 3` happens in the generated assembly module.
No producer claim, no owner transfer, no RH statement.
-/

-- The long integral binders exceed the 100-character style limit by construction.
set_option linter.style.longLine false

open MeasureTheory
open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

namespace ConnesWeilRH.Dev

/-! ## The entry integrand and the panel ladder -/

/-- The (0,3) entry integrand: the 2618 normalized integrand at the captured
owner parameters. -/
noncomputable def entryF2663 (x : ℝ) : ℂ :=
  normalizedMomentIntegrand2618 (capturedModulations2584 3) (storedWidth 3 ^ 2)
    (capturedNodes2584 0) x

/-- The 2618 exponent argument at the entry parameters (branch copy of the
`normalizedMomentIntegrand2618` body, token-exact modulo the substitution:
the inner `ℝ`-ascription on `storedWidth 3 ^ 2` keeps the power in `ℝ`
before the `ℂ`-cast). -/
noncomputable def entryArg2663 (u : ℝ) : ℂ :=
  (-30 / (1 - u ^ 2) : ℝ) +
    (capturedNodes2584 0 + (capturedModulations2584 3 : ℂ) * Complex.I) *
      ((storedWidth 3 ^ 2 : ℝ) : ℂ) * (u : ℂ)

/-- The entry integrand away from its `if` support guard. -/
noncomputable def entryG2663 (u : ℝ) : ℂ := Complex.exp (entryArg2663 u)

/-- Panel boundary ladder `a k = -19/20 + k/100`; the 190 panels tile
`[-19/20, 19/20]`. -/
noncomputable def entryA2663 (k : ℕ) : ℝ := -(19 / 20) + (k : ℝ) * (1 / 100)

/-- Panel centers `c k = -19/20 + (2k+1)/200 = (a k + a (k+1)) / 2`. -/
noncomputable def entryCenter2663 (k : ℕ) : ℝ :=
  -(19 / 20) + ((2 * k + 1 : ℕ) : ℝ) * (1 / 200)

theorem entryA_zero2663 : entryA2663 0 = -(19 / 20) := by
  unfold entryA2663
  norm_num

theorem entryA_190_2663 : entryA2663 190 = 19 / 20 := by
  unfold entryA2663
  norm_num

/-! ## Exact owner constants and their rational banners -/

/-- The squared entry width as an exact rational. -/
def widthSq2663 : ℚ := (5224175567749775 / 2251799813685248) ^ 2

/-- The squared entry width is exactly the rational banner. -/
theorem storedWidth_sq_eq2663 :
    storedWidth 3 ^ 2 = ((widthSq2663 : ℚ) : ℝ) := by
  have hw : storedWidth 3 = (5224175567749775 : ℝ) / 2251799813685248 := by
    rw [storedWidth_eq_capturedWidth2584]
    rfl
  rw [hw, widthSq2663]
  push_cast
  ring

theorem storedWidth_sq_pos2663 : (0 : ℝ) < storedWidth 3 ^ 2 := by
  rw [storedWidth_sq_eq2663]
  have h : (0 : ℚ) < widthSq2663 := by
    rw [widthSq2663]
    norm_num
  exact_mod_cast h

/-- The two-slice edge banner `2 * (1/20) * 2^(-302)` as an exact rational. -/
def edgeBar2663 : ℚ := 2 * (1 / 20) * ((1 / 2 : ℚ)) ^ 302

set_option exponentiation.threshold 400 in
-- the literal power `2 ^ 302` sits in this goal; raise the normalization
-- threshold so the numeral normalization can reduce it
/-- The two edge slices total exactly the rational banner. -/
theorem edgeBar2663_total :
    (1 / 20) * (1 / (2 : ℝ) ^ 302) + (1 / 20) * (1 / (2 : ℝ) ^ 302)
      = ((edgeBar2663 : ℚ) : ℝ) := by
  rw [edgeBar2663]
  push_cast
  rw [show (1 / (2 : ℝ) ^ 302) = (1 / 2 : ℝ) ^ 302 by
    rw [one_div, ← inv_pow, show (2 : ℝ)⁻¹ = 1 / 2 by norm_num]]
  ring

set_option exponentiation.threshold 400 in
-- the literal power `(1 / 2) ^ 302` sits in this goal; see above
theorem edgeBar2663_nonneg : (0 : ℝ) ≤ ((edgeBar2663 : ℚ) : ℝ) := by
  have h : (0 : ℚ) ≤ edgeBar2663 := by
    rw [edgeBar2663]
    norm_num
  exact_mod_cast h

/-! ## Edge slices: pointwise decay on `19/20 <= |x| <= 1` -/

/-- Real part of the 2618 exponent (with `|x| <= 1` not used). -/
theorem edgeExpRe2663 (node : ℂ) (radius modulation x : ℝ) :
    ((-30 / (1 - x ^ 2) : ℝ) +
      (node + (modulation : ℂ) * Complex.I) * (radius : ℂ) * (x : ℂ)).re
      = -30 / (1 - x ^ 2) + node.re * radius * x := by
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    zero_mul, mul_zero, sub_zero, add_zero]

/-- Edge pointwise bound: on `19/20 <= |x| <= 1` the normalized integrand is
bounded by the base-2 bar `2 ^ (-302)`, from `|Re(node) * radius| <=
51923/10000` (then the exponent real part is at most
`-4000/13 + 51923/10000 <= -605/2 <= -302 log 2`). -/
theorem normalizedMomentIntegrand2618_norm_edge2663
    (node : ℂ) (radius modulation : ℝ)
    (hβ : |node.re * radius| ≤ 51923 / 10000) {x : ℝ}
    (hx1 : (19 / 20 : ℝ) ≤ |x|) (hx2 : |x| ≤ 1) :
    ‖normalizedMomentIntegrand2618 modulation radius node x‖
      ≤ 1 / (2 : ℝ) ^ 302 := by
  by_cases hlt : |x| < 1
  · rw [normalizedMomentIntegrand2618, if_pos hlt, Complex.norm_exp, edgeExpRe2663]
    have hqx : (0 : ℝ) < 1 - x ^ 2 := by
      have h2 : x ^ 2 < 1 := by
        rw [← sq_abs x]
        nlinarith [abs_nonneg x, hlt, sq_nonneg (|x|)]
      linarith
    have h39 : 1 - x ^ 2 ≤ 39 / 400 := by
      have hsq : (19 / 20 : ℝ) ^ 2 ≤ x ^ 2 := by
        rw [← sq_abs x]
        exact pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 19 / 20) hx1 2
      nlinarith
    have hdiv : (4000 / 13 : ℝ) ≤ 30 / (1 - x ^ 2) := by
      have h := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 30) hqx h39
      have hc : (30 : ℝ) / (39 / 400) = 4000 / 13 := by norm_num
      linarith [h, hc]
    have hlin : node.re * radius * x ≤ |node.re * radius| := by
      have h1 : node.re * radius * x ≤ |node.re * radius * x| := le_abs_self _
      have h2 : |node.re * radius * x| = |node.re * radius| * |x| := abs_mul _ _
      have h4 : |node.re * radius| * |x| ≤ |node.re * radius| * 1 :=
        mul_le_mul_of_nonneg_left hx2 (abs_nonneg _)
      linarith [h1, h2, h4]
    have hexp : -30 / (1 - x ^ 2) + node.re * radius * x ≤ -(605 / 2) := by
      have hneg : -(30 / (1 - x ^ 2)) ≤ -(4000 / 13) := neg_le_neg hdiv
      have hrew : (-30 : ℝ) / (1 - x ^ 2) = -(30 / (1 - x ^ 2)) := by ring
      rw [hrew]
      linarith [hneg, hβ, hlin]
    have hbar : Real.exp (-(605 / 2)) ≤ 1 / (2 : ℝ) ^ 302 := by
      have hpow : (2 : ℝ) ^ 302 ≤ Real.exp (605 / 2) := by
        have hbase : (2 : ℝ) ^ 302 ≤ (Real.exp 1) ^ 302 :=
          pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) Real.exp_one_gt_two.le 302
        have hexp302 : (Real.exp 1) ^ 302 = Real.exp 302 := by
          rw [← Real.exp_nat_mul]
          norm_num
        exact le_trans hbase (le_trans (le_of_eq hexp302)
          (Real.exp_le_exp.mpr (by norm_num)))
      rw [Real.exp_neg, one_div]
      exact (inv_le_inv₀ (Real.exp_pos (605 / 2))
        (pow_pos (by norm_num : (0 : ℝ) < 2) 302)).mpr hpow
    exact le_trans (Real.exp_le_exp.mpr hexp) hbar
  · rw [normalizedMomentIntegrand2618, if_neg hlt, norm_zero]
    exact le_of_lt (one_div_pos.mpr (pow_pos (by norm_num : (0 : ℝ) < 2) 302))

set_option exponentiation.threshold 400 in
-- the literal power `2 ^ 302` sits in the bound; raise the normalization
-- threshold so the rfl checks reduce it silently
/-- Right edge slice `[19/20, 1]`: norm at most `(1/20) * 2 ^ (-302)`. -/
theorem normalizedMomentIntegrand2618_edgeRight2663
    (node : ℂ) (radius modulation : ℝ)
    (hβ : |node.re * radius| ≤ 51923 / 10000) :
    ‖∫ x in (19 / 20)..1, normalizedMomentIntegrand2618 modulation radius node x‖
      ≤ (1 / 20) * (1 / (2 : ℝ) ^ 302) := by
  have hpt : ∀ x ∈ Set.uIoc (19 / 20 : ℝ) 1,
      ‖normalizedMomentIntegrand2618 modulation radius node x‖
        ≤ 1 / (2 : ℝ) ^ 302 := by
    intro x hx
    have hx' : x ∈ Set.Ioc (19 / 20 : ℝ) 1 := by
      simpa only [Set.uIoc, min_eq_left (by norm_num : (19 / 20 : ℝ) ≤ 1),
        max_eq_right (by norm_num : (19 / 20 : ℝ) ≤ 1)] using hx
    have habs : |x| = x := abs_of_pos (lt_trans (by norm_num) hx'.1)
    exact normalizedMomentIntegrand2618_norm_edge2663 node radius modulation hβ
      (by rw [habs]; exact hx'.1.le) (by rw [habs]; exact hx'.2)
  calc ‖∫ x in (19 / 20)..1, normalizedMomentIntegrand2618 modulation radius node x‖
      ≤ (1 / (2 : ℝ) ^ 302) * |1 - 19 / 20| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hpt
    _ = (1 / 20) * (1 / (2 : ℝ) ^ 302) := by
        rw [show |1 - (19 / 20 : ℝ)| = 1 / 20 by norm_num]
        ring

set_option exponentiation.threshold 400 in
-- the literal power `2 ^ 302` sits in the bound; see the right-edge comment
/-- Left edge slice `[-1, -19/20]`: norm at most `(1/20) * 2 ^ (-302)`. -/
theorem normalizedMomentIntegrand2618_edgeLeft2663
    (node : ℂ) (radius modulation : ℝ)
    (hβ : |node.re * radius| ≤ 51923 / 10000) :
    ‖∫ x in (-1)..(-(19 / 20)),
        normalizedMomentIntegrand2618 modulation radius node x‖
      ≤ (1 / 20) * (1 / (2 : ℝ) ^ 302) := by
  have hpt : ∀ x ∈ Set.uIoc (-1 : ℝ) (-(19 / 20)),
      ‖normalizedMomentIntegrand2618 modulation radius node x‖
        ≤ 1 / (2 : ℝ) ^ 302 := by
    intro x hx
    have hx' : x ∈ Set.Ioc (-1 : ℝ) (-(19 / 20)) := by
      simpa only [Set.uIoc, min_eq_left (by norm_num : (-1 : ℝ) ≤ -(19 / 20)),
        max_eq_right (by norm_num : (-1 : ℝ) ≤ -(19 / 20))] using hx
    have habs : |x| = -x := abs_of_neg (lt_of_le_of_lt hx'.2 (by norm_num))
    exact normalizedMomentIntegrand2618_norm_edge2663 node radius modulation hβ
      (by rw [habs]; linarith [hx'.2]) (by rw [habs]; linarith [hx'.1])
  calc ‖∫ x in (-1)..(-(19 / 20)),
          normalizedMomentIntegrand2618 modulation radius node x‖
      ≤ (1 / (2 : ℝ) ^ 302) * |(-(19 / 20)) - (-1)| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hpt
    _ = (1 / 20) * (1 / (2 : ℝ) ^ 302) := by
        rw [show |(-(19 / 20) : ℝ) - (-1)| = 1 / 20 by norm_num]
        ring

/-! ## Concrete entry instantiations -/

/-- The exact entry coefficient `Re(node0) * r3^2` obeys the edge bar
`51923/10000` (both operands are exact binary64 lifts). -/
theorem entryBetaBound2663 :
    |(capturedNodes2584 0).re * (storedWidth 3 ^ 2)| ≤ 51923 / 10000 := by
  have hn : (capturedNodes2584 0).re
      = (4255901647865119 : ℝ) / 4503599627370496 := rfl
  have hw : storedWidth 3 = (5224175567749775 : ℝ) / 2251799813685248 := by
    rw [storedWidth_eq_capturedWidth2584]
    rfl
  rw [hn, hw]
  norm_num

theorem entryEdgeRight2663 :
    ‖∫ x in (19 / 20)..1, entryF2663 x‖
      ≤ (1 / 20) * (1 / (2 : ℝ) ^ 302) :=
  normalizedMomentIntegrand2618_edgeRight2663 (capturedNodes2584 0) (storedWidth 3 ^ 2)
    (capturedModulations2584 3) entryBetaBound2663

theorem entryEdgeLeft2663 :
    ‖∫ x in (-1)..(-(19 / 20)), entryF2663 x‖
      ≤ (1 / 20) * (1 / (2 : ℝ) ^ 302) :=
  normalizedMomentIntegrand2618_edgeLeft2663 (capturedNodes2584 0) (storedWidth 3 ^ 2)
    (capturedModulations2584 3) entryBetaBound2663

/-! ## The 190-panel tiling -/

set_option maxHeartbeats 4000000 in
-- heartbeat budget for the panel hint: the continuity term unifies against the
-- 190-node ladder
theorem entryTilingAbs2663 :
    (∑ k ∈ Finset.Ico 0 190, ∫ x in entryA2663 k..entryA2663 (k + 1), entryF2663 x)
      = ∫ x in entryA2663 0..entryA2663 190, entryF2663 x := by
  have hden : ContinuousOn (fun u : ℝ => 1 - u ^ 2) (Set.Icc (-(19 / 20)) (19 / 20)) :=
    (continuous_const.sub (continuous_id.pow 2)).continuousOn
  have h0 : ∀ u ∈ Set.Icc (-(19 / 20) : ℝ) (19 / 20), 1 - u ^ 2 ≠ 0 := by
    intro u hu
    have h1 : |u| ≤ (19 / 20 : ℝ) := abs_le.mpr hu
    have h2 : u ^ 2 ≤ (19 / 20 : ℝ) ^ 2 := by
      rw [← sq_abs u]
      exact pow_le_pow_left₀ (abs_nonneg u) h1 2
    have : (0 : ℝ) < 1 - u ^ 2 := by nlinarith
    exact ne_of_gt this
  have hdiv : ContinuousOn (fun u : ℝ => (-30 : ℝ) / (1 - u ^ 2))
      (Set.Icc (-(19 / 20)) (19 / 20)) := by
    show ContinuousOn ((fun _ : ℝ => (-30 : ℝ)) / fun u : ℝ => 1 - u ^ 2) _
    exact ContinuousOn.div continuousOn_const hden h0
  have hdivC : ContinuousOn (fun u : ℝ => Complex.ofReal ((-30 : ℝ) / (1 - u ^ 2)))
      (Set.Icc (-(19 / 20)) (19 / 20)) :=
    Complex.continuous_ofReal.comp_continuousOn hdiv
  have hlin : ContinuousOn (fun u : ℝ =>
      (capturedNodes2584 0 + (capturedModulations2584 3 : ℂ) * Complex.I) *
        ((storedWidth 3 ^ 2 : ℝ) : ℂ) * (u : ℂ))
      (Set.Icc (-(19 / 20)) (19 / 20)) := by
    have h1 : ContinuousOn (fun u : ℝ =>
        (capturedNodes2584 0 + (capturedModulations2584 3 : ℂ) * Complex.I) *
          ((storedWidth 3 ^ 2 : ℝ) : ℂ)) (Set.Icc (-(19 / 20)) (19 / 20)) :=
      continuousOn_const
    have h2 : ContinuousOn (fun u : ℝ => (u : ℂ))
        (Set.Icc (-(19 / 20)) (19 / 20)) :=
      Complex.continuous_ofReal.comp_continuousOn continuousOn_id
    exact h1.mul h2
  have hArg : ContinuousOn entryArg2663 (Set.Icc (-(19 / 20)) (19 / 20)) :=
    hdivC.add hlin
  have hG : ContinuousOn entryG2663 (Set.Icc (-(19 / 20)) (19 / 20)) :=
    Complex.continuous_exp.comp_continuousOn hArg
  have hfg : Set.EqOn entryF2663 entryG2663 (Set.Icc (-(19 / 20)) (19 / 20)) := by
    intro u hu
    have h1 : |u| ≤ (19 / 20 : ℝ) := abs_le.mpr hu
    have hlt : |u| < 1 := by linarith
    simp only [entryF2663, entryG2663, entryArg2663,
      normalizedMomentIntegrand2618, if_pos hlt]
  refine intervalIntegral.sum_integral_adjacent_intervals_Ico (f := entryF2663)
    (μ := volume) (a := entryA2663) (m := 0) (n := 190) (by norm_num) ?_
  intro k hk
  have hklt : k < 190 := (Set.mem_Ico.mp hk).2
  have hmono : entryA2663 k ≤ entryA2663 (k + 1) := by
    unfold entryA2663
    push_cast
    linarith
  have hsubIcc : Set.Icc (entryA2663 k) (entryA2663 (k + 1)) ⊆
      Set.Icc (-(19 / 20)) (19 / 20) := by
    intro u hu
    constructor
    · have h := hu.1
      unfold entryA2663 at h
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      have hk' : (0 : ℝ) ≤ (k : ℝ) * (1 / 100) := mul_nonneg hk0 (by norm_num)
      linarith
    · have h := hu.2
      unfold entryA2663 at h
      have hk2 : (k + 1 : ℕ) ≤ 190 := by omega
      have hkR2 : ((k + 1 : ℕ) : ℝ) ≤ 190 := by exact_mod_cast hk2
      have hk' : ((k + 1 : ℕ) : ℝ) * (1 / 100) ≤ 190 * (1 / 100) :=
        mul_le_mul_of_nonneg_right hkR2 (by norm_num)
      linarith
  have hsubU : Set.uIcc (entryA2663 k) (entryA2663 (k + 1)) ⊆
      Set.Icc (-(19 / 20)) (19 / 20) := by
    rw [Set.uIcc_of_le hmono]
    exact hsubIcc
  have hGsub : ContinuousOn entryG2663 (Set.Icc (entryA2663 k) (entryA2663 (k + 1))) :=
    hG.mono hsubIcc
  have hIntG : IntervalIntegrable entryG2663 volume (entryA2663 k) (entryA2663 (k + 1)) :=
    ContinuousOn.intervalIntegrable_of_Icc hmono hGsub (μ := volume)
  have heqIoc : Set.EqOn entryG2663 entryF2663
      (Set.uIoc (entryA2663 k) (entryA2663 (k + 1))) :=
    fun u hu => (hfg (Set.uIoc_subset_uIcc.trans hsubU hu)).symm
  exact IntervalIntegrable.congr heqIoc hIntG

/-- Per-panel shift: the `k`-th tiling slice equals the `k`-th center-shifted
panel integral of the record-2662 ball form. -/
theorem entryShift2663 (k : ℕ) :
    (∫ position in (-(1 / 200))..(1 / 200), entryF2663 (entryCenter2663 k + position))
      = ∫ x in entryA2663 k..entryA2663 (k + 1), entryF2663 x := by
  have hcomp := intervalIntegral.integral_comp_add_left (f := entryF2663)
    (d := entryCenter2663 k) (a := -(1 / 200)) (b := 1 / 200)
  have h1 : entryCenter2663 k + (-(1 / 200)) = entryA2663 k := by
    unfold entryCenter2663 entryA2663
    push_cast
    ring
  have h2 : entryCenter2663 k + (1 / 200) = entryA2663 (k + 1) := by
    unfold entryCenter2663 entryA2663
    push_cast
    ring
  rw [hcomp, h1, h2]

set_option maxHeartbeats 4000000 in
-- heartbeat budget for the assembled tiling: the sum_congr instance matches
-- the shift identity against every panel slice
theorem entryTilingBall2663 :
    (∑ k ∈ Finset.Ico 0 190,
        ∫ position in (-(1 / 200))..(1 / 200), entryF2663 (entryCenter2663 k + position))
      = ∫ x in (-(19 / 20))..(19 / 20), entryF2663 x := by
  rw [show (∑ k ∈ Finset.Ico 0 190,
        ∫ position in (-(1 / 200))..(1 / 200), entryF2663 (entryCenter2663 k + position))
      = ∑ k ∈ Finset.Ico 0 190,
        ∫ x in entryA2663 k..entryA2663 (k + 1), entryF2663 x from
    Finset.sum_congr rfl fun k _ => entryShift2663 k]
  rw [entryTilingAbs2663, entryA_zero2663, entryA_190_2663]

/-! ## Coordinate glue for the generated assembly -/

/-- Real part of a finite complex sum. -/
theorem finset_sum_re2663 {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    (∑ k ∈ s, f k).re = ∑ k ∈ s, (f k).re := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.sum_empty, Complex.zero_re]
  · intro a s ha ih
    simp only [Finset.sum_insert ha]
    rw [Complex.add_re, ih]

/-- Imaginary part of a finite complex sum. -/
theorem finset_sum_im2663 {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    (∑ k ∈ s, f k).im = ∑ k ∈ s, (f k).im := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.sum_empty, Complex.zero_im]
  · intro a s ha ih
    simp only [Finset.sum_insert ha]
    rw [Complex.add_im, ih]

/-- Norm of a finite complex sum against the coordinate L1 sum. -/
theorem norm_sum_le_abs_re_add_abs_im2663 {ι : Type*} (s : Finset ι) (z : ι → ℂ) :
    ‖∑ k ∈ s, z k‖ ≤ ∑ k ∈ s, (|(z k).re| + |(z k).im|) :=
  le_trans (norm_sum_le s z) (Finset.sum_le_sum fun k _ =>
    Complex.norm_le_abs_re_add_abs_im (z k))

/-- Norm of a finite complex sum against an arbitrary per-term L1 budget. -/
theorem norm_sum_le_abs_re_add_abs_im_of_le2663 {ι : Type*} (s : Finset ι)
    (z : ι → ℂ) (ch : ι → ℝ)
    (h : ∀ k ∈ s, |(z k).re| + |(z k).im| ≤ ch k) :
    ‖∑ k ∈ s, z k‖ ≤ ∑ k ∈ s, ch k :=
  le_trans (norm_sum_le_abs_re_add_abs_im2663 s z) (Finset.sum_le_sum h)

/-- Cast of a finite rational sum to `ℝ`. -/
theorem rat_cast_sum2663 {ι : Type*} (s : Finset ι) (f : ι → ℚ) :
    (∑ k ∈ s, ((f k : ℚ) : ℝ)) = ((∑ k ∈ s, f k : ℚ) : ℝ) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.sum_empty, Rat.cast_zero]
  · intro a s ha ih
    simp only [Finset.sum_insert ha]
    rw [Rat.cast_add, ih]

/-- `embedPair2542` preserves addition (coordinatewise). -/
theorem embedPair2542_add2663 (a b : RatPair2542) :
    embedPair2542 (a + b) = embedPair2542 a + embedPair2542 b := by
  apply Complex.ext
  · change ((a + b).1 : ℝ) = (a.1 : ℝ) + (b.1 : ℝ)
    rw [Prod.fst_add, Rat.cast_add]
  · change ((a + b).2 : ℝ) = (a.2 : ℝ) + (b.2 : ℝ)
    rw [Prod.snd_add, Rat.cast_add]

/-- `embedPair2542` preserves finite sums. -/
theorem embedPair2542_sum2663 {ι : Type*} (s : Finset ι) (c : ι → RatPair2542) :
    embedPair2542 (∑ k ∈ s, c k) = ∑ k ∈ s, embedPair2542 (c k) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.sum_empty]
    apply Complex.ext
    · change ((0 : ℚ) : ℝ) = (0 : ℂ).re
      rw [Complex.zero_re, Rat.cast_zero]
    · change ((0 : ℚ) : ℝ) = (0 : ℂ).im
      rw [Complex.zero_im, Rat.cast_zero]
  · intro a s ha ih
    simp only [Finset.sum_insert ha]
    rw [embedPair2542_add2663, ih]

#print axioms entryA_zero2663
#print axioms entryA_190_2663
#print axioms storedWidth_sq_eq2663
#print axioms storedWidth_sq_pos2663
#print axioms edgeBar2663_total
#print axioms edgeBar2663_nonneg
#print axioms edgeExpRe2663
#print axioms normalizedMomentIntegrand2618_norm_edge2663
#print axioms normalizedMomentIntegrand2618_edgeRight2663
#print axioms normalizedMomentIntegrand2618_edgeLeft2663
#print axioms entryBetaBound2663
#print axioms entryEdgeRight2663
#print axioms entryEdgeLeft2663
#print axioms entryTilingAbs2663
#print axioms entryShift2663
#print axioms entryTilingBall2663
#print axioms finset_sum_re2663
#print axioms finset_sum_im2663
#print axioms norm_sum_le_abs_re_add_abs_im2663
#print axioms norm_sum_le_abs_re_add_abs_im_of_le2663
#print axioms rat_cast_sum2663
#print axioms embedPair2542_add2663
#print axioms embedPair2542_sum2663

end ConnesWeilRH.Dev
