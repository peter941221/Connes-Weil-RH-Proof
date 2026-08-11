import ConnesWeilRH.Dev.Wall14PlateauFDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms

namespace ConnesWeilRH.Source.Dev.Wall14Plateau

open MeasureTheory Filter Set
open scoped Topology Interval

noncomputable def bb (x : ℝ) : ℝ → ℝ := fun u => bumpReal (x - u) * bd u

lemma bb_cont (x : ℝ) : Continuous (bb x) := by
  unfold bb
  have h1 : Continuous (fun w : ℝ => x - w) := continuous_const.sub continuous_id
  exact (bumpReal_continuous.comp h1).mul bd_continuous

lemma bb_interval_integrable (x) (a b : ℝ) : IntervalIntegrable (bb x) volume a b :=
  (bb_cont x).intervalIntegrable

/-- If `bd u ≠ 0` then `|u| ≤ 1`. -/
lemma bd_ne_zero_imp_abs_le_one (u : ℝ) (h : bd u ≠ 0) : |u| ≤ (1 : ℝ) := by
  by_contra hc
  have hlt : (1 : ℝ) < |u| := lt_of_not_ge hc
  exact h (bd_outer_zero u hlt)

/-- `bb x u = 0` when `|u| > 1`. -/
lemma bb_outer_zero (x : ℝ) (u : ℝ) (hu : (1 : ℝ) < |u|) : bb x u = 0 := by
  unfold bb; simp [bd_outer_zero u hu]

/-- `bb x u = 0` when `|u| < 9/10`. -/
lemma bb_plateau_zero (x : ℝ) (u : ℝ) (hu : |u| < (9 / 10 : ℝ)) : bb x u = 0 := by
  unfold bb; simp [bd_plateau_zero u hu]

/-- support of `bb x` lies within `(-2, 2]`. -/
lemma bb_support_subset (x : ℝ) : Function.support (bb x) ⊆ Set.Ioc (-2 : ℝ) 2 := by
  intro u hu
  have hb : bb x u ≠ 0 := hu
  unfold bb at hb
  have hbd : bd u ≠ 0 := by
    intro hz; exact hb (by simp [bz])
  have hub : |u| ≤ (1 : ℝ) := bd_ne_zero_imp_abs_le_one u hbd
  have hlo : -2 < u := (abs_le.mp hub).1 |>.trans ... 
  sorry

/-- `∫_ℝ bb x = ∫ in -2..2 bb x`. -/
lemma bb_integral_reduce (x : ℝ) :
    (∫ u : ℝ, bb x u) = ∫ u in (-2)..(2), bb x u := by
  exact (intervalIntegral.integral_eq_integral_of_support_subset (bb_support_subset x)).symm

/-- Zero on the outer-left interval `(-2, -1)`. -/
lemma bb_outer_left_interval (x : ℝ) : (∫ u in (-2)..(-1), bb x u) = 0 := by
  apply interval_integral_eq_zero_of_Ioo (a := (-2 : ℝ)) (b := (-1 : ℝ))
  · linarith
  · intro u hu1 hu2
    have huabs : (1 : ℝ) < |u| := by
      have hu : |u| = -u := by
        rw [abs_of_neg (by linarith)]
      rw [hu]; linarith
    exact bb_outer_zero x u huabs

/-- Zero on the plateau interval `(-9/10, 9/10)`. -/
lemma bb_plateau_mid (x : ℝ) : (∫ u in (-9/10)..(9/10), bb x u) = 0 := by
  apply interval_integral_eq_zero_of_Ioo (a := (-9/10 : ℝ)) (b := (9/10 : ℝ))
  · norm_num
  · intro u hu1 hu2
    have : |u| < (9/10 : ℝ) := abs_lt.mpr ⟨hu1, hu2⟩
    exact bb_plateau_zero x u this

/-- Zero-outer-right interval `(1, 2)`. -/
lemma bb_outer_right_interval (x : ℝ) : (∫ u in (1)..(2), bb x u) = 0 := by
  apply interval_integral_eq_zero_of_Ioo (a := (1 : ℝ)) (b := (2 : ℝ))
  · linarith
  · intro u hu1 hu2
    have huabs : (1 : ℝ) < |u| := by
      have hu : (0:ℝ) ≤ u := by linarith
      rwa [abs_of_nonneg hu]
    exact bb_outer_zero x u huabs

/-- Two-band reduction: `∫ -2..2 bb = ∫ -1..-9/10 bb + ∫ 9/10..1 bb`. -/
theorem bb_two_band (x : ℝ) :
    (∫ u in (-2)..2, bb x u)
      = (∫ u in (-1)..(-9/10), bb x u) + (∫ u in (9/10)..1, bb x u) := by
  calc
    (∫ u in (-2)..2, bb x u)
        = (∫ u in (-2)..(-1), bb x u) + ∫ u in (-1)..(-9/10), bb x u
            + (∫ u in (-9/10)..(9/10), bb x u + ∫ u in (9/10)..(1), bb x u)
            + ∫ u in (1)..(2), bb x u := by
          -- chain adjacent intervals
          rw [← intervalIntegral.integral_add_adjacent_intervals (bb_interval_integrable x (-2)(-1))]
          -- ?? this is getting messy; do a different approach
          sorry

end ConnesWeilRH.Source.Dev.Wall14Plateau
