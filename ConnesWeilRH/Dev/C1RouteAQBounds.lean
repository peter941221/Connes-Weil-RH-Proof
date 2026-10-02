import Mathlib.Algebra.Order.Ring.Abs

namespace ConnesWeilRH.Dev

theorem q_nonneg_of_abs_le_one2443 {u : ℝ} (hu : |u| ≤ 1) :
    0 ≤ 1 - u ^ 2 := by
  rw [sub_nonneg, sq_le_one_iff_abs_le_one]
  exact hu

theorem q_pos_of_abs_lt_one2443 {u : ℝ} (hu : |u| < 1) :
    0 < 1 - u ^ 2 := by
  rw [sub_pos, sq_lt_one_iff_abs_lt_one]
  exact hu

theorem q_le_one2443 (u : ℝ) : 1 - u ^ 2 ≤ 1 := by
  linarith [sq_nonneg u]

end ConnesWeilRH.Dev
