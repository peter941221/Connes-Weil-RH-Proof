import ConnesWeilRH.Dev.Wall14PlateauFDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace ConnesWeilRH.Source.Dev.Wall14Plateau

open MeasureTheory Filter Set
open scoped Topology Interval

noncomputable def bb (x : ℝ) : ℝ → ℝ := fun u => bumpReal (x - u) * bd u

lemma bb_cont (x : ℝ) : Continuous (bb x) := by
  unfold bb
  have h1 : Continuous (fun w : ℝ => x - w) := continuous_const.sub continuous_id
  exact (bumpReal_continuous.comp h1).mul bd_continuous

/-- If `bd u ≠ 0` then `|u| ≤ 1`. -/
lemma bd_ne_zero_imp_abs_le_one (u : ℝ) (h : bd u ≠ 0) : |u| ≤ (1 : ℝ) := by
  by_contra hc
  have hlt : (1 : ℝ) < |u| := lt_of_not_ge hc
  exact h (bd_outer_zero u hlt)

/-- `bb x u = 0` when `|u| > 1` (outer). -/
lemma bb_outer_zero (x : ℝ) (u : ℝ) (hu : (1 : ℝ) < |u|) : bb x u = 0 := by
  unfold bb
  simp [bd_outer_zero u hu]

/-- `bb x u = 0` when `|u| < 9/10` (plateau). -/
lemma bb_plateau_zero (x : ℝ) (u : ℝ) (hu : |u| < (9 / 10 : ℝ)) : bb x u = 0 := by
  unfold bb
  simp [bd_plateau_zero u hu]

/-- `bb x u = 0` when `|u| = 1` (outer endpoints, smooth bump). -/
lemma bb_abs_one_zero (x : ℝ) (u : ℝ) (hu : |u| = (1 : ℝ)) : bb x u = 0 := by
  -- derivative on u=1 or -1 vanishes; use evenness + bd at +-1. Prove bd 1 = 0 and bd (-1) = 0.
  by_cases hnu : u = 1
  · -- u = 1
    subst u
    unfold bb
    have hb : bd 1 = 0 := by
      -- bumpReal is locally equal to 0 near 1 (since bumpEx = 0 for |x|>1 and continuous), so deriv = 0
      sorry
    simp [hb]
  · -- |u| = 1 and u ≠ 1, so u = -1
    have hu' : u = -1 := by
      rcases abs_eq.1 hu with hpos | hneg
      · exact hpos
      · exact hneg
    subst u
    unfold bb
    have hd : bd (-1) = 0 := by
      -- bd odd and bd 1 = 0
      have : bd 1 = 0 := by
        -- need bd 1 = 0 separately
        sorry
      simpa [bd_neg, this] using this
    simp [hd]
      -- outer endpoint smooth
      sorry
  · sorry

@[export bd_one_zero] theorem bd_one_zero : bd (1 : ℝ) = 0 := by
  -- bumpReal is locally constant (0) in a punctured neighbourhood of 1; derivative 0
  have h_ev : (fun x : ℝ => bumpReal x) =ᶠ[𝓝 (1:ℝ)] (fun _ : ℝ => (0 : ℝ)) := by
    rw [Filter.EventuallyEq]
    have hset : {x : ℝ | (1 : ℝ) < |x|} ∈ 𝓝 (1 : ℝ) := by
      exact (isOpen_lt continuous_const continuous_abs).mem_nhds (by norm_num : (1:ℝ) < |(1:ℝ)|)
    filter_upwards [hset] with x hx
    exact bumpReal_eq_zero_of_abs_ge x (le_of_lt hx)
  have hder : HasDerivAt (fun x : ℝ => bumpReal x) (0 : ℝ) (1 : ℝ) := by
    simpa using ((hasDerivAt_const (1:ℝ) (0:ℝ)).congr_of_eventuallyEq h_ev)
  unfold bd
  exact hder.deriv

@[export] theorem bd_neg_one_zero : bd (-1 : ℝ) = 0 := by
  -- bd(-1) = -bd 1 = 0
  rw [bd_neg, bd_one_zero, neg_zero]

end ConnesWeilRH.Source.Dev.Wall14Plateau
