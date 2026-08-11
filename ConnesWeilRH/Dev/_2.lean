import ConnesWeilRH.Dev.Wall14PlateauFDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms

namespace ConnesWeilRH.Source.Dev.Wall14Plateau

open MeasureTheory Filter Set
open scoped Topology Interval

/-- If `f = 0` on the open interval `(a,b)`, the interval integral is zero. -/
theorem interval_integral_eq_zero_of_Ioo {a b : ℝ} (ha : a < b) {f : ℝ → ℝ}
    (hf : ∀ x, a < x → x < b → f x = 0) :
    (∫ x in a..b, f x) = 0 := by
  rw [intervalIntegral.integral_of_le (le_of_lt ha)]
  have hset : Ioo a b =ᵐ[volume] Ioc a b := by
    simpa using (MeasureTheory.Ioo_ae_eq_Ioc (μ := (volume : Measure ℝ)) (a := a) (b := b))
  calc
    (∫ x in (Ioc a b : Set ℝ), f x ∂volume)
        = ∫ x in (Ioo a b), f x ∂volume := (setIntegral_congr_set hset).symm
    _ = ∫ x in (Ioo a b), (fun _ : ℝ => (0 : ℝ)) x ∂volume := by
        apply setIntegral_congr_fun measurableSet_Ioo
        intro x hx; exact hf x hx.1 hx.2
    _ = 0 := by simp

noncomputable def bb (x : ℝ) : ℝ → ℝ := fun u => bumpReal (x - u) * bd u

lemma bb_cont (x : ℝ) : Continuous (bb x) := by
  unfold bb
  have h1 : Continuous (fun w : ℝ => x - w) := continuous_const.sub continuous_id
  exact (bumpReal_continuous.comp h1).mul bd_continuous

lemma bb_int (x) (a b : ℝ) : IntervalIntegrable (bb x) volume a b := (bb_cont x).intervalIntegrable a b

lemma bd_ne_zero_imp_abs_le_one (u : ℝ) (h : bd u ≠ 0) : |u| ≤ (1 : ℝ) := by
  by_contra hc; exact h (bd_outer_zero u (lt_of_not_ge hc))

lemma bb_outer_zero (x : ℝ) (u : ℝ) (hu : (1 : ℝ) < |u|) : bb x u = 0 := by
  unfold bb; simp [bd_outer_zero u hu]

lemma bb_plateau_zero (x : ℝ) (u : ℝ) (hu : |u| < (9 / 10 : ℝ)) : bb x u = 0 := by
  unfold bb; simp [bd_plateau_zero u hu]

lemma bb_support_subset (x : ℝ) : Function.support (bb x) ⊆ Set.Ioc (-2 : ℝ) 2 := by
  intro u hu
  have hb : bb x u ≠ 0 := hu
  unfold bb at hb
  have hbd : bd u ≠ 0 := by intro hz; exact hb (by simp [hz])
  have hub : |u| ≤ (1 : ℝ) := bd_ne_zero_imp_abs_le_one u hbd
  constructor
  · have : -(1 : ℝ) ≤ u := (abs_le.mp hub).1; linarith
  · have : u ≤ (1 : ℝ) := (abs_le.mp hub).2; linarith

lemma bb_integral_reduce (x : ℝ) :
    (∫ u : ℝ, bb x u) = ∫ u in (-2)..(2), bb x u := by
  exact (intervalIntegral.integral_eq_integral_of_support_subset (bb_support_subset x)).symm

lemma bb_outer_left_interval (x : ℝ) : (∫ u in (-2)..(-1), bb x u) = 0 := by
  apply interval_integral_eq_zero_of_Ioo (a := (-2 : ℝ)) (b := (-1 : ℝ))
  · linarith
  · intro u hu1 hu2
    have hu : |u| = -u := abs_of_neg (by linarith)
    have : (1 : ℝ) < |u| := by rw [hu]; linarith
    exact bb_outer_zero x u this

lemma bb_plateau_mid (x : ℝ) : (∫ u in (-(9/10 : ℝ))..(9/10), bb x u) = 0 := by
  apply interval_integral_eq_zero_of_Ioo (a := (-(9/10 : ℝ))) (b := (9/10 : ℝ))
  · norm_num
  · intro u hu1 hu2
    exact bb_plateau_zero x u (abs_lt.mpr ⟨hu1, hu2⟩)

lemma bb_outer_right_interval (x : ℝ) : (∫ u in (1)..(2), bb x u) = 0 := by
  apply interval_integral_eq_zero_of_Ioo (a := (1 : ℝ)) (b := (2 : ℝ))
  · linarith
  · intro u hu1 hu2
    have huabs : (1 : ℝ) < |u| := by
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ u)]; linarith
    exact bb_outer_zero x u huabs

theorem bb_chain (x : ℝ) :
    (∫ u in (-2)..2, bb x u)
      = (∫ u in (-2)..(-1), bb x u) + (∫ u in (-1)..(-(9/10 : ℝ)), bb x u)
        + (∫ u in (-(9/10 : ℝ))..(9/10), bb x u) + (∫ u in (9/10)..1, bb x u)
        + (∫ u in (1)..2, bb x u) := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (bb_int x (-2) 1) (bb_int x 1 2)]
  rw [← intervalIntegral.integral_add_adjacent_intervals (bb_int x (-2) (9/10)) (bb_int x (9/10) 1)]
  rw [← intervalIntegral.integral_add_adjacent_intervals (bb_int x (-2) (-(9/10 : ℝ))) (bb_int x (-(9/10 : ℝ)) (9/10))]
  rw [← intervalIntegral.integral_add_adjacent_intervals (bb_int x (-2) (-1)) (bb_int x (-1) (-(9/10 : ℝ)))]

theorem bb_two_band (x : ℝ) :
    (∫ u in (-2)..2, bb x u) = (∫ u in (-1)..(-(9/10 : ℝ)), bb x u) + (∫ u in (9/10)..1, bb x u) := by
  have hchain := bb_chain x
  rw [bb_outer_left_interval x, bb_outer_right_interval x, bb_plateau_mid x] at hchain
  -- hchain: ∫-2..2 = 0 + B + 0 + D + 0  (parens from the chain RHS)
  simp at hchain
  linarith

end ConnesWeilRH.Source.Dev.Wall14Plateau
