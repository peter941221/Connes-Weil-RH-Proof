import ConnesWeilRH.Dev.C1RouteAEntryRect2663
import ConnesWeilRH.Dev.C1RouteAEntryPanels2663
import ConnesWeilRH.Dev.C1RouteAEntryTiling2663

/-! # Record 2663 part 2: membership of entry (0,3)

Assembly of the record-2663 lane into the first unconditional off-diagonal
membership:

  `(analyticMomentInterval2597 0 3).Mem
    (ownerMomentMatrix2351 capturedModulations2584 capturedNodes2584 0 3)`.

Chain: the owner entry is `widthSq * Re(∫_{-1}^{1})` (normalization 2618);
the integral splits into left edge + center + right edge (additivity); the
center is the 190-panel tiling (`entryTilingBall2663`) followed by the
per-panel decomposition `Z_k = c_k + (Z_k - c_k)` with the deviation
bounded by `‖Σ diff‖ ≤ Σ (|re| + |im|) ≤ Σ chBar_k = CBAR`
(`norm_sum_le_abs_re_add_abs_im_of_le2663`, `entryPanelsBall2663`); the
edges by the two `2^{-302}` bars (`entryEdgeLeft2663` / `entryEdgeRight2663`,
`edgeBar2663_total`); and the four coordinates close against the committed
home rectangle through the barrier inequalities of `C1RouteAEntryRect2663`.

This module is hand-written (not generated); every literal it consumes is
a committed artifact literal. -/

open MeasureTheory
open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

namespace ConnesWeilRH.Dev

/-! ## Measurability and the unit norm ceiling -/

/-- The 2618 integrand is measurable: the support guard is a measurable
set and the exponent is a continuous complex function. -/
theorem normalizedMomentIntegrand2618_measurable2663
    (modulation radius : ℝ) (node : ℂ) :
    Measurable (normalizedMomentIntegrand2618 modulation radius node) := by
  unfold normalizedMomentIntegrand2618
  have hinner : Measurable (fun u : ℝ => Complex.exp
      ((-30 / (1 - u ^ 2) : ℝ) +
        (node + (modulation : ℂ) * Complex.I) * (radius : ℂ) * (u : ℂ))) := by
    have h1 : Measurable (fun u : ℝ => (-30 : ℝ) / (1 - u ^ 2)) :=
      measurable_const.div (measurable_const.sub (measurable_id.pow_const 2))
    have h2 : Measurable (fun u : ℝ => (u : ℂ)) :=
      Complex.continuous_ofReal.measurable
    exact Complex.continuous_exp.measurable.comp
      ((Complex.continuous_ofReal.measurable.comp h1).add
        (measurable_const.mul h2))
  exact Measurable.ite
    (measurableSet_lt continuous_abs.measurable measurable_const)
    hinner measurable_const

/-- The entry integrand is measurable. -/
theorem entryF2663_measurable2663 : Measurable entryF2663 :=
  normalizedMomentIntegrand2618_measurable2663 (capturedModulations2584 3)
    (storedWidth 3 ^ 2) (capturedNodes2584 0)

/-- Unit norm ceiling: on the entropy-carrying exponent the real part is
`-30 / (1 - x^2) + node.re * r3^2 * x <= -30 + 51923/10000 < 0` for
`|x| < 1` (`30 <= 30/(1-x^2)` from `1 - x^2 <= 1`, and the linear term
bounded by `entryBetaBound2663`); outside the guard the integrand is `0`. -/
theorem entryF2663_norm_le_one2663 (x : ℝ) : ‖entryF2663 x‖ ≤ 1 := by
  by_cases hlt : |x| < 1
  · have hbridge : entryF2663 x = entryG2663 x := by
      simp only [entryF2663, entryG2663, entryArg2663,
        normalizedMomentIntegrand2618, if_pos hlt]
    rw [hbridge, entryG2663, Complex.norm_exp, entryArg2663, edgeExpRe2663]
    have hqx : (0 : ℝ) < 1 - x ^ 2 := by
      have h2 : x ^ 2 < 1 := by
        rw [← sq_abs x]
        nlinarith [abs_nonneg x, hlt, sq_nonneg (|x|)]
      linarith
    have hdiv : (30 : ℝ) ≤ 30 / (1 - x ^ 2) := by
      rw [le_div_iff₀ hqx]
      nlinarith [sq_nonneg x]
    have hlin : (capturedNodes2584 0).re * (storedWidth 3 ^ 2) * x
        ≤ |(capturedNodes2584 0).re * (storedWidth 3 ^ 2)| := by
      have h1 : (capturedNodes2584 0).re * (storedWidth 3 ^ 2) * x
          ≤ |(capturedNodes2584 0).re * (storedWidth 3 ^ 2) * x| :=
        le_abs_self _
      have h2 : |(capturedNodes2584 0).re * (storedWidth 3 ^ 2) * x|
          = |(capturedNodes2584 0).re * (storedWidth 3 ^ 2)| * |x| :=
        abs_mul _ _
      have h4 : |(capturedNodes2584 0).re * (storedWidth 3 ^ 2)| * |x|
          ≤ |(capturedNodes2584 0).re * (storedWidth 3 ^ 2)| * 1 :=
        mul_le_mul_of_nonneg_left (le_of_lt hlt) (abs_nonneg _)
      linarith [h1, h2, h4]
    have hexp : -30 / (1 - x ^ 2)
        + (capturedNodes2584 0).re * (storedWidth 3 ^ 2) * x ≤ 0 := by
      have hneg : -(30 / (1 - x ^ 2)) ≤ -30 := neg_le_neg hdiv
      have hrew : (-30 : ℝ) / (1 - x ^ 2) = -(30 / (1 - x ^ 2)) := by ring
      rw [hrew]
      linarith [hneg, hlin, entryBetaBound2663]
    have hexp2 : Real.exp (-30 / (1 - x ^ 2)
        + (capturedNodes2584 0).re * (storedWidth 3 ^ 2) * x) ≤ Real.exp 0 :=
      Real.exp_le_exp.mpr hexp
    simpa only [Real.exp_zero] using hexp2
  · have hbridge : entryF2663 x = 0 := by
      simp only [entryF2663, normalizedMomentIntegrand2618, if_neg hlt]
    rw [hbridge, norm_zero]
    norm_num

/-! ## Integrability on every slice inside the support -/

/-- The entry integrand is interval-integrable on any slice inside
`[-1, 1]`: bounded by 1 and measurable, with finite slice measure. -/
theorem entryF2663_intervalIntegrable2663 (a b : ℝ)
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) :
    IntervalIntegrable entryF2663 volume a b := by
  refine intervalIntegrable_iff.mpr ?_
  have hsub : Set.uIoc a b ⊆ Set.Icc (-1 : ℝ) 1 := by
    intro x hx
    have hmin : (-1 : ℝ) ≤ min a b := le_min (abs_le.mp ha).1 (abs_le.mp hb).1
    have hmax : max a b ≤ 1 := max_le (abs_le.mp ha).2 (abs_le.mp hb).2
    rw [Set.uIoc] at hx
    exact ⟨le_trans hmin (le_of_lt hx.1), le_trans hx.2 hmax⟩
  have hvol : volume (Set.uIoc a b) < ⊤ :=
    lt_of_le_of_lt (measure_mono hsub)
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top)
  exact IntegrableOn.of_bound hvol
    (entryF2663_measurable2663.aestronglyMeasurable)
    1 (Filter.Eventually.of_forall fun x => entryF2663_norm_le_one2663 x)

/-! ## The three-piece split -/

/-- Integral additivity: the full slice is left edge + center + right edge. -/
theorem entrySplit2663 :
    (∫ x in (-1 : ℝ)..1, entryF2663 x)
      = (∫ x in (-1)..(-(19 / 20)), entryF2663 x)
        + (∫ x in (-(19 / 20))..(19 / 20), entryF2663 x)
        + (∫ x in (19 / 20)..1, entryF2663 x) := by
  have hA : IntervalIntegrable entryF2663 volume (-1 : ℝ) (-(19 / 20)) :=
    entryF2663_intervalIntegrable2663 (-1) (-(19 / 20)) (by norm_num) (by norm_num)
  have hB : IntervalIntegrable entryF2663 volume (-(19 / 20)) (19 / 20) :=
    entryF2663_intervalIntegrable2663 (-(19 / 20)) (19 / 20)
      (by norm_num) (by norm_num)
  have hC : IntervalIntegrable entryF2663 volume (19 / 20) 1 :=
    entryF2663_intervalIntegrable2663 (19 / 20) 1 (by norm_num) (by norm_num)
  have hBC : IntervalIntegrable entryF2663 volume (-(19 / 20)) 1 := hB.trans hC
  rw [(intervalIntegral.integral_add_adjacent_intervals hA hBC).symm,
    (intervalIntegral.integral_add_adjacent_intervals hB hC).symm]
  ring

/-- Real-part split. -/
theorem entrySplitRe2663 :
    (∫ x in (-1 : ℝ)..1, entryF2663 x).re
      = (∫ x in (-1)..(-(19 / 20)), entryF2663 x).re
        + (∫ x in (-(19 / 20))..(19 / 20), entryF2663 x).re
        + (∫ x in (19 / 20)..1, entryF2663 x).re := by
  rw [entrySplit2663, Complex.add_re, Complex.add_re]

/-- Imaginary-part split. -/
theorem entrySplitIm2663 :
    (∫ x in (-1 : ℝ)..1, entryF2663 x).im
      = (∫ x in (-1)..(-(19 / 20)), entryF2663 x).im
        + (∫ x in (-(19 / 20))..(19 / 20), entryF2663 x).im
        + (∫ x in (19 / 20)..1, entryF2663 x).im := by
  rw [entrySplit2663, Complex.add_im, Complex.add_im]

/-! ## The centered decomposition -/

/-- Real part of the center slice = center sum + deviation sum. -/
theorem entryCentralDecompRe2663 :
    (∫ x in (-(19 / 20))..(19 / 20), entryF2663 x).re
      = ((∑ k ∈ Finset.Ico 0 190, panelAssemblyCenter2662Disp2663 k).1 : ℝ)
        + ∑ k ∈ Finset.Ico 0 190,
            (entryPanel2663 k
              - embedPair2542 (panelAssemblyCenter2662Disp2663 k)).re := by
  have hcen : (∫ x in (-(19 / 20))..(19 / 20), entryF2663 x)
      = ∑ k ∈ Finset.Ico 0 190, entryPanel2663 k := by
    rw [← entryTilingBall2663]
    rfl
  have hdecomp : (∑ k ∈ Finset.Ico 0 190, entryPanel2663 k)
      = embedPair2542 (∑ k ∈ Finset.Ico 0 190, panelAssemblyCenter2662Disp2663 k)
        + ∑ k ∈ Finset.Ico 0 190,
            (entryPanel2663 k
              - embedPair2542 (panelAssemblyCenter2662Disp2663 k)) := by
    rw [embedPair2542_sum2663, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by
      rw [add_comm]
      ring
  rw [hcen, hdecomp, Complex.add_re, finset_sum_re2663]
  rfl

/-- Imaginary part of the center slice = center sum + deviation sum. -/
theorem entryCentralDecompIm2663 :
    (∫ x in (-(19 / 20))..(19 / 20), entryF2663 x).im
      = ((∑ k ∈ Finset.Ico 0 190, panelAssemblyCenter2662Disp2663 k).2 : ℝ)
        + ∑ k ∈ Finset.Ico 0 190,
            (entryPanel2663 k
              - embedPair2542 (panelAssemblyCenter2662Disp2663 k)).im := by
  have hcen : (∫ x in (-(19 / 20))..(19 / 20), entryF2663 x)
      = ∑ k ∈ Finset.Ico 0 190, entryPanel2663 k := by
    rw [← entryTilingBall2663]
    rfl
  have hdecomp : (∑ k ∈ Finset.Ico 0 190, entryPanel2663 k)
      = embedPair2542 (∑ k ∈ Finset.Ico 0 190, panelAssemblyCenter2662Disp2663 k)
        + ∑ k ∈ Finset.Ico 0 190,
            (entryPanel2663 k
              - embedPair2542 (panelAssemblyCenter2662Disp2663 k)) := by
    rw [embedPair2542_sum2663, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by
      rw [add_comm]
      ring
  rw [hcen, hdecomp, Complex.add_im, finset_sum_im2663]
  rfl

/-! ## Central coordinate bounds -/

/-- Upper bound of the center-slice real part: `HIre + CBAR`. -/
theorem entryCentralReLe2663 :
    (∫ x in (-(19 / 20))..(19 / 20), entryF2663 x).re
      ≤ ((HIre2663 : ℚ) : ℝ) + ((CBAR2663 : ℚ) : ℝ) := by
  have hcs : ((∑ k ∈ Finset.Ico 0 190, panelAssemblyCenter2662Disp2663 k).1 : ℝ)
      = ∑ k ∈ Finset.Ico 0 190,
          ((panelAssemblyCenter2662Disp2663 k).1 : ℝ) := by
    rw [show ((∑ k ∈ Finset.Ico 0 190, panelAssemblyCenter2662Disp2663 k).1 : ℝ)
        = (embedPair2542 (∑ k ∈ Finset.Ico 0 190,
            panelAssemblyCenter2662Disp2663 k)).re from rfl]
    rw [embedPair2542_sum2663, finset_sum_re2663]
    rfl
  have h1 : ((∑ k ∈ Finset.Ico 0 190, panelAssemblyCenter2662Disp2663 k).1 : ℝ)
      ≤ ((HIre2663 : ℚ) : ℝ) := by
    calc ((∑ k ∈ Finset.Ico 0 190, panelAssemblyCenter2662Disp2663 k).1 : ℝ)
        = ∑ k ∈ Finset.Ico 0 190,
            ((panelAssemblyCenter2662Disp2663 k).1 : ℝ) := hcs
      _ ≤ ∑ k ∈ Finset.Ico 0 190, ((reHiBar2663 k : ℚ) : ℝ) :=
          Finset.sum_le_sum fun k hk =>
            Rat.cast_le.mpr (entryPanelsCenterFstHi2663 k hk)
      _ = ((∑ k ∈ Finset.Ico 0 190, reHiBar2663 k : ℚ) : ℝ) :=
          rat_cast_sum2663 (Finset.Ico 0 190) reHiBar2663
      _ = ((HIre2663 : ℚ) : ℝ) := by rw [sum_HIre2663]
  have h2 : (∑ k ∈ Finset.Ico 0 190,
        (entryPanel2663 k
          - embedPair2542 (panelAssemblyCenter2662Disp2663 k)).re)
      ≤ ((CBAR2663 : ℚ) : ℝ) := by
    rw [← finset_sum_re2663]
    refine le_trans (le_trans (le_abs_self _) (Complex.abs_re_le_norm _)) ?_
    refine le_trans (norm_sum_le_abs_re_add_abs_im_of_le2663 (Finset.Ico 0 190)
      (fun k => entryPanel2663 k - embedPair2542 (panelAssemblyCenter2662Disp2663 k))
      (fun k => ((chBar2663 k : ℚ) : ℝ))
      (fun k hk => entryPanelsBall2663 k hk)) ?_
    exact le_of_eq (by rw [rat_cast_sum2663, sum_CBAR2663])
  rw [entryCentralDecompRe2663]
  linarith [h1, h2]

/-- Lower bound of the center-slice real part: `LOre - CBAR`. -/
theorem entryCentralReGe2663 :
    ((LOre2663 : ℚ) : ℝ) - ((CBAR2663 : ℚ) : ℝ)
      ≤ (∫ x in (-(19 / 20))..(19 / 20), entryF2663 x).re := by
  have hcs : ((∑ k ∈ Finset.Ico 0 190, panelAssemblyCenter2662Disp2663 k).1 : ℝ)
      = ∑ k ∈ Finset.Ico 0 190,
          ((panelAssemblyCenter2662Disp2663 k).1 : ℝ) := by
    rw [show ((∑ k ∈ Finset.Ico 0 190, panelAssemblyCenter2662Disp2663 k).1 : ℝ)
        = (embedPair2542 (∑ k ∈ Finset.Ico 0 190,
            panelAssemblyCenter2662Disp2663 k)).re from rfl]
    rw [embedPair2542_sum2663, finset_sum_re2663]
    rfl
  have h1 : ((LOre2663 : ℚ) : ℝ)
      ≤ ((∑ k ∈ Finset.Ico 0 190, panelAssemblyCenter2662Disp2663 k).1 : ℝ) := by
    calc ((LOre2663 : ℚ) : ℝ)
        = ((∑ k ∈ Finset.Ico 0 190, reLoBar2663 k : ℚ) : ℝ) := by
          rw [← sum_LOre2663]
      _ = ∑ k ∈ Finset.Ico 0 190, ((reLoBar2663 k : ℚ) : ℝ) :=
          (rat_cast_sum2663 (Finset.Ico 0 190) reLoBar2663).symm
      _ ≤ ∑ k ∈ Finset.Ico 0 190,
            ((panelAssemblyCenter2662Disp2663 k).1 : ℝ) :=
          Finset.sum_le_sum fun k hk =>
            Rat.cast_le.mpr (entryPanelsCenterFstLo2663 k hk)
      _ = ((∑ k ∈ Finset.Ico 0 190, panelAssemblyCenter2662Disp2663 k).1 : ℝ) :=
          hcs.symm
  have h2 : -((CBAR2663 : ℚ) : ℝ)
      ≤ (∑ k ∈ Finset.Ico 0 190,
          (entryPanel2663 k
            - embedPair2542 (panelAssemblyCenter2662Disp2663 k)).re) := by
    rw [← finset_sum_re2663]
    have h5 : ‖∑ k ∈ Finset.Ico 0 190,
          (entryPanel2663 k
            - embedPair2542 (panelAssemblyCenter2662Disp2663 k))‖
        ≤ ((CBAR2663 : ℚ) : ℝ) :=
      le_trans (norm_sum_le_abs_re_add_abs_im_of_le2663 (Finset.Ico 0 190)
        (fun k => entryPanel2663 k - embedPair2542 (panelAssemblyCenter2662Disp2663 k))
        (fun k => ((chBar2663 k : ℚ) : ℝ))
        (fun k hk => entryPanelsBall2663 k hk))
        (le_of_eq (by rw [rat_cast_sum2663, sum_CBAR2663]))
    exact le_trans (neg_le_neg h5)
      (le_trans (neg_le_neg (Complex.abs_re_le_norm _)) (neg_abs_le _))
  rw [entryCentralDecompRe2663]
  linarith [h1, h2]

/-- Upper bound of the center-slice imaginary part: `HIim + CBAR`. -/
theorem entryCentralImLe2663 :
    (∫ x in (-(19 / 20))..(19 / 20), entryF2663 x).im
      ≤ ((HIim2663 : ℚ) : ℝ) + ((CBAR2663 : ℚ) : ℝ) := by
  have hcs : ((∑ k ∈ Finset.Ico 0 190, panelAssemblyCenter2662Disp2663 k).2 : ℝ)
      = ∑ k ∈ Finset.Ico 0 190,
          ((panelAssemblyCenter2662Disp2663 k).2 : ℝ) := by
    rw [show ((∑ k ∈ Finset.Ico 0 190, panelAssemblyCenter2662Disp2663 k).2 : ℝ)
        = (embedPair2542 (∑ k ∈ Finset.Ico 0 190,
            panelAssemblyCenter2662Disp2663 k)).im from rfl]
    rw [embedPair2542_sum2663, finset_sum_im2663]
    rfl
  have h1 : ((∑ k ∈ Finset.Ico 0 190, panelAssemblyCenter2662Disp2663 k).2 : ℝ)
      ≤ ((HIim2663 : ℚ) : ℝ) := by
    calc ((∑ k ∈ Finset.Ico 0 190, panelAssemblyCenter2662Disp2663 k).2 : ℝ)
        = ∑ k ∈ Finset.Ico 0 190,
            ((panelAssemblyCenter2662Disp2663 k).2 : ℝ) := hcs
      _ ≤ ∑ k ∈ Finset.Ico 0 190, ((imHiBar2663 k : ℚ) : ℝ) :=
          Finset.sum_le_sum fun k hk =>
            Rat.cast_le.mpr (entryPanelsCenterSndHi2663 k hk)
      _ = ((∑ k ∈ Finset.Ico 0 190, imHiBar2663 k : ℚ) : ℝ) :=
          rat_cast_sum2663 (Finset.Ico 0 190) imHiBar2663
      _ = ((HIim2663 : ℚ) : ℝ) := by rw [sum_HIim2663]
  have h2 : (∑ k ∈ Finset.Ico 0 190,
        (entryPanel2663 k
          - embedPair2542 (panelAssemblyCenter2662Disp2663 k)).im)
      ≤ ((CBAR2663 : ℚ) : ℝ) := by
    rw [← finset_sum_im2663]
    refine le_trans (le_trans (le_abs_self _) (Complex.abs_im_le_norm _)) ?_
    refine le_trans (norm_sum_le_abs_re_add_abs_im_of_le2663 (Finset.Ico 0 190)
      (fun k => entryPanel2663 k - embedPair2542 (panelAssemblyCenter2662Disp2663 k))
      (fun k => ((chBar2663 k : ℚ) : ℝ))
      (fun k hk => entryPanelsBall2663 k hk)) ?_
    exact le_of_eq (by rw [rat_cast_sum2663, sum_CBAR2663])
  rw [entryCentralDecompIm2663]
  linarith [h1, h2]

/-- Lower bound of the center-slice imaginary part: `LOim - CBAR`. -/
theorem entryCentralImGe2663 :
    ((LOim2663 : ℚ) : ℝ) - ((CBAR2663 : ℚ) : ℝ)
      ≤ (∫ x in (-(19 / 20))..(19 / 20), entryF2663 x).im := by
  have hcs : ((∑ k ∈ Finset.Ico 0 190, panelAssemblyCenter2662Disp2663 k).2 : ℝ)
      = ∑ k ∈ Finset.Ico 0 190,
          ((panelAssemblyCenter2662Disp2663 k).2 : ℝ) := by
    rw [show ((∑ k ∈ Finset.Ico 0 190, panelAssemblyCenter2662Disp2663 k).2 : ℝ)
        = (embedPair2542 (∑ k ∈ Finset.Ico 0 190,
            panelAssemblyCenter2662Disp2663 k)).im from rfl]
    rw [embedPair2542_sum2663, finset_sum_im2663]
    rfl
  have h1 : ((LOim2663 : ℚ) : ℝ)
      ≤ ((∑ k ∈ Finset.Ico 0 190, panelAssemblyCenter2662Disp2663 k).2 : ℝ) := by
    calc ((LOim2663 : ℚ) : ℝ)
        = ((∑ k ∈ Finset.Ico 0 190, imLoBar2663 k : ℚ) : ℝ) := by
          rw [← sum_LOim2663]
      _ = ∑ k ∈ Finset.Ico 0 190, ((imLoBar2663 k : ℚ) : ℝ) :=
          (rat_cast_sum2663 (Finset.Ico 0 190) imLoBar2663).symm
      _ ≤ ∑ k ∈ Finset.Ico 0 190,
            ((panelAssemblyCenter2662Disp2663 k).2 : ℝ) :=
          Finset.sum_le_sum fun k hk =>
            Rat.cast_le.mpr (entryPanelsCenterSndLo2663 k hk)
      _ = ((∑ k ∈ Finset.Ico 0 190, panelAssemblyCenter2662Disp2663 k).2 : ℝ) :=
          hcs.symm
  have h2 : -((CBAR2663 : ℚ) : ℝ)
      ≤ (∑ k ∈ Finset.Ico 0 190,
          (entryPanel2663 k
            - embedPair2542 (panelAssemblyCenter2662Disp2663 k)).im) := by
    rw [← finset_sum_im2663]
    have h5 : ‖∑ k ∈ Finset.Ico 0 190,
          (entryPanel2663 k
            - embedPair2542 (panelAssemblyCenter2662Disp2663 k))‖
        ≤ ((CBAR2663 : ℚ) : ℝ) :=
      le_trans (norm_sum_le_abs_re_add_abs_im_of_le2663 (Finset.Ico 0 190)
        (fun k => entryPanel2663 k - embedPair2542 (panelAssemblyCenter2662Disp2663 k))
        (fun k => ((chBar2663 k : ℚ) : ℝ))
        (fun k hk => entryPanelsBall2663 k hk))
        (le_of_eq (by rw [rat_cast_sum2663, sum_CBAR2663]))
    exact le_trans (neg_le_neg h5)
      (le_trans (neg_le_neg (Complex.abs_im_le_norm _)) (neg_abs_le _))
  rw [entryCentralDecompIm2663]
  linarith [h1, h2]

/-! ## Edge pairs -/

/-- Upper bound of the two edge real parts: `edgeBar`. -/
theorem entryEdgePairReLe2663 :
    (∫ x in (-1)..(-(19 / 20)), entryF2663 x).re
        + (∫ x in (19 / 20)..1, entryF2663 x).re
      ≤ ((edgeBar2663 : ℚ) : ℝ) := by
  have h1 : (∫ x in (-1)..(-(19 / 20)), entryF2663 x).re
      ≤ (1 / 20) * (1 / (2 : ℝ) ^ 302) :=
    le_trans (le_abs_self _)
      (le_trans (Complex.abs_re_le_norm _) entryEdgeLeft2663)
  have h2 : (∫ x in (19 / 20)..1, entryF2663 x).re
      ≤ (1 / 20) * (1 / (2 : ℝ) ^ 302) :=
    le_trans (le_abs_self _)
      (le_trans (Complex.abs_re_le_norm _) entryEdgeRight2663)
  exact le_trans (add_le_add h1 h2) (le_of_eq edgeBar2663_total)

set_option exponentiation.threshold 400 in
-- the literal power `(1 / 2) ^ 302` sits in this goal; see the
-- tiling module
/-- Lower bound of the two edge real parts: `-edgeBar`. -/
theorem entryEdgePairReGe2663 :
    -((edgeBar2663 : ℚ) : ℝ)
      ≤ (∫ x in (-1)..(-(19 / 20)), entryF2663 x).re
        + (∫ x in (19 / 20)..1, entryF2663 x).re := by
  have hB : -((edgeBar2663 : ℚ) : ℝ)
      = -((1 / 20) * (1 / (2 : ℝ) ^ 302))
        - ((1 / 20) * (1 / (2 : ℝ) ^ 302)) := by
    rw [← edgeBar2663_total]
    ring
  have h1 : -((1 / 20) * (1 / (2 : ℝ) ^ 302))
      ≤ (∫ x in (-1)..(-(19 / 20)), entryF2663 x).re :=
    le_trans (neg_le_neg (le_trans (Complex.abs_re_le_norm _) entryEdgeLeft2663))
      (neg_abs_le _)
  have h2 : -((1 / 20) * (1 / (2 : ℝ) ^ 302))
      ≤ (∫ x in (19 / 20)..1, entryF2663 x).re :=
    le_trans (neg_le_neg (le_trans (Complex.abs_re_le_norm _) entryEdgeRight2663))
      (neg_abs_le _)
  rw [hB]
  linarith [h1, h2]

/-- Upper bound of the two edge imaginary parts: `edgeBar`. -/
theorem entryEdgePairImLe2663 :
    (∫ x in (-1)..(-(19 / 20)), entryF2663 x).im
        + (∫ x in (19 / 20)..1, entryF2663 x).im
      ≤ ((edgeBar2663 : ℚ) : ℝ) := by
  have h1 : (∫ x in (-1)..(-(19 / 20)), entryF2663 x).im
      ≤ (1 / 20) * (1 / (2 : ℝ) ^ 302) :=
    le_trans (le_abs_self _)
      (le_trans (Complex.abs_im_le_norm _) entryEdgeLeft2663)
  have h2 : (∫ x in (19 / 20)..1, entryF2663 x).im
      ≤ (1 / 20) * (1 / (2 : ℝ) ^ 302) :=
    le_trans (le_abs_self _)
      (le_trans (Complex.abs_im_le_norm _) entryEdgeRight2663)
  exact le_trans (add_le_add h1 h2) (le_of_eq edgeBar2663_total)

set_option exponentiation.threshold 400 in
-- the literal power `(1 / 2) ^ 302` sits in this goal; see the
-- tiling module
/-- Lower bound of the two edge imaginary parts: `-edgeBar`. -/
theorem entryEdgePairImGe2663 :
    -((edgeBar2663 : ℚ) : ℝ)
      ≤ (∫ x in (-1)..(-(19 / 20)), entryF2663 x).im
        + (∫ x in (19 / 20)..1, entryF2663 x).im := by
  have hB : -((edgeBar2663 : ℚ) : ℝ)
      = -((1 / 20) * (1 / (2 : ℝ) ^ 302))
        - ((1 / 20) * (1 / (2 : ℝ) ^ 302)) := by
    rw [← edgeBar2663_total]
    ring
  have h1 : -((1 / 20) * (1 / (2 : ℝ) ^ 302))
      ≤ (∫ x in (-1)..(-(19 / 20)), entryF2663 x).im :=
    le_trans (neg_le_neg (le_trans (Complex.abs_im_le_norm _) entryEdgeLeft2663))
      (neg_abs_le _)
  have h2 : -((1 / 20) * (1 / (2 : ℝ) ^ 302))
      ≤ (∫ x in (19 / 20)..1, entryF2663 x).im :=
    le_trans (neg_le_neg (le_trans (Complex.abs_im_le_norm _) entryEdgeRight2663))
      (neg_abs_le _)
  rw [hB]
  linarith [h1, h2]

/-! ## The four coordinate bounds of the owner entry -/

/-- Upper bound of the entry real part. -/
theorem entryReLe2663 :
    (ownerMomentMatrix2351 capturedModulations2584 capturedNodes2584 0 3).re
      ≤ ((widthSq2663 * (HIre2663 + (CBAR2663 + edgeBar2663)) : ℚ) : ℝ) := by
  rw [show ownerMomentMatrix2351 capturedModulations2584 capturedNodes2584 0 3
      = momentEntry2351 capturedModulations2584 3 (capturedNodes2584 0) from rfl,
    momentEntry2351_eq_normalizedIntegral2618, Complex.real_smul,
    Complex.re_ofReal_mul,
    show (∫ coordinate in (-1 : ℝ)..1,
        normalizedMomentIntegrand2618 (capturedModulations2584 3) (storedWidth 3 ^ 2)
          (capturedNodes2584 0) coordinate)
      = ∫ x in (-1 : ℝ)..1, entryF2663 x from rfl,
    entrySplitRe2663, storedWidth_sq_eq2663]
  have hw : (0 : ℝ) ≤ ((widthSq2663 : ℚ) : ℝ) :=
    le_of_lt (by rw [← storedWidth_sq_eq2663]; exact storedWidth_sq_pos2663)
  have hinner : (∫ x in (-1)..(-(19 / 20)), entryF2663 x).re
        + (∫ x in (-(19 / 20))..(19 / 20), entryF2663 x).re
        + (∫ x in (19 / 20)..1, entryF2663 x).re
      ≤ ((HIre2663 : ℚ) : ℝ) + ((CBAR2663 : ℚ) : ℝ)
        + ((edgeBar2663 : ℚ) : ℝ) := by
    linarith [entryCentralReLe2663, entryEdgePairReLe2663]
  calc ((widthSq2663 : ℚ) : ℝ) *
        ((∫ x in (-1)..(-(19 / 20)), entryF2663 x).re
          + (∫ x in (-(19 / 20))..(19 / 20), entryF2663 x).re
          + (∫ x in (19 / 20)..1, entryF2663 x).re)
      ≤ ((widthSq2663 : ℚ) : ℝ) * (((HIre2663 : ℚ) : ℝ) + ((CBAR2663 : ℚ) : ℝ)
          + ((edgeBar2663 : ℚ) : ℝ)) := mul_le_mul_of_nonneg_left hinner hw
    _ = ((widthSq2663 * (HIre2663 + (CBAR2663 + edgeBar2663)) : ℚ) : ℝ) := by
        push_cast
        ring

/-- Lower bound of the entry real part. -/
theorem entryReGe2663 :
    ((widthSq2663 * (LOre2663 - (CBAR2663 + edgeBar2663)) : ℚ) : ℝ)
      ≤ (ownerMomentMatrix2351 capturedModulations2584 capturedNodes2584 0 3).re := by
  rw [show ownerMomentMatrix2351 capturedModulations2584 capturedNodes2584 0 3
      = momentEntry2351 capturedModulations2584 3 (capturedNodes2584 0) from rfl,
    momentEntry2351_eq_normalizedIntegral2618, Complex.real_smul,
    Complex.re_ofReal_mul,
    show (∫ coordinate in (-1 : ℝ)..1,
        normalizedMomentIntegrand2618 (capturedModulations2584 3) (storedWidth 3 ^ 2)
          (capturedNodes2584 0) coordinate)
      = ∫ x in (-1 : ℝ)..1, entryF2663 x from rfl,
    entrySplitRe2663, storedWidth_sq_eq2663]
  have hw : (0 : ℝ) ≤ ((widthSq2663 : ℚ) : ℝ) :=
    le_of_lt (by rw [← storedWidth_sq_eq2663]; exact storedWidth_sq_pos2663)
  have hinner : ((LOre2663 : ℚ) : ℝ) - ((CBAR2663 : ℚ) : ℝ)
        - ((edgeBar2663 : ℚ) : ℝ)
      ≤ (∫ x in (-1)..(-(19 / 20)), entryF2663 x).re
        + (∫ x in (-(19 / 20))..(19 / 20), entryF2663 x).re
        + (∫ x in (19 / 20)..1, entryF2663 x).re := by
    linarith [entryCentralReGe2663, entryEdgePairReGe2663]
  calc ((widthSq2663 * (LOre2663 - (CBAR2663 + edgeBar2663)) : ℚ) : ℝ)
      = ((widthSq2663 : ℚ) : ℝ) * (((LOre2663 : ℚ) : ℝ) - ((CBAR2663 : ℚ) : ℝ)
          - ((edgeBar2663 : ℚ) : ℝ)) := by
        push_cast
        ring
    _ ≤ ((widthSq2663 : ℚ) : ℝ) *
        ((∫ x in (-1)..(-(19 / 20)), entryF2663 x).re
          + (∫ x in (-(19 / 20))..(19 / 20), entryF2663 x).re
          + (∫ x in (19 / 20)..1, entryF2663 x).re) :=
        mul_le_mul_of_nonneg_left hinner hw

/-- Upper bound of the entry imaginary part. -/
theorem entryImLe2663 :
    (ownerMomentMatrix2351 capturedModulations2584 capturedNodes2584 0 3).im
      ≤ ((widthSq2663 * (HIim2663 + (CBAR2663 + edgeBar2663)) : ℚ) : ℝ) := by
  rw [show ownerMomentMatrix2351 capturedModulations2584 capturedNodes2584 0 3
      = momentEntry2351 capturedModulations2584 3 (capturedNodes2584 0) from rfl,
    momentEntry2351_eq_normalizedIntegral2618, Complex.real_smul,
    Complex.im_ofReal_mul,
    show (∫ coordinate in (-1 : ℝ)..1,
        normalizedMomentIntegrand2618 (capturedModulations2584 3) (storedWidth 3 ^ 2)
          (capturedNodes2584 0) coordinate)
      = ∫ x in (-1 : ℝ)..1, entryF2663 x from rfl,
    entrySplitIm2663, storedWidth_sq_eq2663]
  have hw : (0 : ℝ) ≤ ((widthSq2663 : ℚ) : ℝ) :=
    le_of_lt (by rw [← storedWidth_sq_eq2663]; exact storedWidth_sq_pos2663)
  have hinner : (∫ x in (-1)..(-(19 / 20)), entryF2663 x).im
        + (∫ x in (-(19 / 20))..(19 / 20), entryF2663 x).im
        + (∫ x in (19 / 20)..1, entryF2663 x).im
      ≤ ((HIim2663 : ℚ) : ℝ) + ((CBAR2663 : ℚ) : ℝ)
        + ((edgeBar2663 : ℚ) : ℝ) := by
    linarith [entryCentralImLe2663, entryEdgePairImLe2663]
  calc ((widthSq2663 : ℚ) : ℝ) *
        ((∫ x in (-1)..(-(19 / 20)), entryF2663 x).im
          + (∫ x in (-(19 / 20))..(19 / 20), entryF2663 x).im
          + (∫ x in (19 / 20)..1, entryF2663 x).im)
      ≤ ((widthSq2663 : ℚ) : ℝ) * (((HIim2663 : ℚ) : ℝ) + ((CBAR2663 : ℚ) : ℝ)
          + ((edgeBar2663 : ℚ) : ℝ)) := mul_le_mul_of_nonneg_left hinner hw
    _ = ((widthSq2663 * (HIim2663 + (CBAR2663 + edgeBar2663)) : ℚ) : ℝ) := by
        push_cast
        ring

/-- Lower bound of the entry imaginary part. -/
theorem entryImGe2663 :
    ((widthSq2663 * (LOim2663 - (CBAR2663 + edgeBar2663)) : ℚ) : ℝ)
      ≤ (ownerMomentMatrix2351 capturedModulations2584 capturedNodes2584 0 3).im := by
  rw [show ownerMomentMatrix2351 capturedModulations2584 capturedNodes2584 0 3
      = momentEntry2351 capturedModulations2584 3 (capturedNodes2584 0) from rfl,
    momentEntry2351_eq_normalizedIntegral2618, Complex.real_smul,
    Complex.im_ofReal_mul,
    show (∫ coordinate in (-1 : ℝ)..1,
        normalizedMomentIntegrand2618 (capturedModulations2584 3) (storedWidth 3 ^ 2)
          (capturedNodes2584 0) coordinate)
      = ∫ x in (-1 : ℝ)..1, entryF2663 x from rfl,
    entrySplitIm2663, storedWidth_sq_eq2663]
  have hw : (0 : ℝ) ≤ ((widthSq2663 : ℚ) : ℝ) :=
    le_of_lt (by rw [← storedWidth_sq_eq2663]; exact storedWidth_sq_pos2663)
  have hinner : ((LOim2663 : ℚ) : ℝ) - ((CBAR2663 : ℚ) : ℝ)
        - ((edgeBar2663 : ℚ) : ℝ)
      ≤ (∫ x in (-1)..(-(19 / 20)), entryF2663 x).im
        + (∫ x in (-(19 / 20))..(19 / 20), entryF2663 x).im
        + (∫ x in (19 / 20)..1, entryF2663 x).im := by
    linarith [entryCentralImGe2663, entryEdgePairImGe2663]
  calc ((widthSq2663 * (LOim2663 - (CBAR2663 + edgeBar2663)) : ℚ) : ℝ)
      = ((widthSq2663 : ℚ) : ℝ) * (((LOim2663 : ℚ) : ℝ) - ((CBAR2663 : ℚ) : ℝ)
          - ((edgeBar2663 : ℚ) : ℝ)) := by
        push_cast
        ring
    _ ≤ ((widthSq2663 : ℚ) : ℝ) *
        ((∫ x in (-1)..(-(19 / 20)), entryF2663 x).im
          + (∫ x in (-(19 / 20))..(19 / 20), entryF2663 x).im
          + (∫ x in (19 / 20)..1, entryF2663 x).im) :=
        mul_le_mul_of_nonneg_left hinner hw

/-! ## Membership -/

/-- The owner entry `(0,3)` lies in the committed home rectangle: the
first unconditional off-diagonal membership of the 2663 lane. -/
theorem entry03Mem2663 :
    (analyticMomentInterval2597 0 3).Mem
      (ownerMomentMatrix2351 capturedModulations2584 capturedNodes2584 0 3) := by
  rw [ComplexRect2427.Mem]
  exact ⟨le_trans (le_trans (le_of_eq rectReLo2663_tie2663)
      rectReLo2663_le2663) entryReGe2663,
    le_trans entryReLe2663
      (le_trans rectReHi2663_ge2663 (le_of_eq rectReHi2663_tie2663.symm)),
    le_trans (le_trans (le_of_eq rectImLo2663_tie2663)
      rectImLo2663_le2663) entryImGe2663,
    le_trans entryImLe2663
      (le_trans rectImHi2663_ge2663 (le_of_eq rectImHi2663_tie2663.symm))⟩

/-! ## Axiom audit -/

#print axioms entryF2663_norm_le_one2663
#print axioms entryF2663_intervalIntegrable2663
#print axioms entrySplit2663
#print axioms entrySplitRe2663
#print axioms entrySplitIm2663
#print axioms entryCentralDecompRe2663
#print axioms entryCentralDecompIm2663
#print axioms entryCentralReLe2663
#print axioms entryCentralReGe2663
#print axioms entryCentralImLe2663
#print axioms entryCentralImGe2663
#print axioms entryEdgePairReLe2663
#print axioms entryEdgePairReGe2663
#print axioms entryEdgePairImLe2663
#print axioms entryEdgePairImGe2663
#print axioms entryReLe2663
#print axioms entryReGe2663
#print axioms entryImLe2663
#print axioms entryImGe2663
#print axioms entry03Mem2663

end ConnesWeilRH.Dev
