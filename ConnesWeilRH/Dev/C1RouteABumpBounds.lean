import ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

theorem widthBump_nonneg2439 {radius position : ℝ} (hradius : 0 < radius) :
    0 ≤ widthBump radius position := by
  unfold widthBump
  split
  · exact Real.exp_nonneg _
  · rfl

theorem widthBump_le_one2439 {radius position : ℝ} (hradius : 0 < radius) :
    widthBump radius position ≤ 1 := by
  unfold widthBump
  split
  · rename_i hinside
    have hratio : |position / radius| < 1 := by
      rw [abs_div]
      exact (div_lt_one (abs_nonneg radius)).2
        (by simpa [abs_of_pos hradius] using hinside)
    have hsq : (position / radius) ^ 2 < 1 :=
      (sq_lt_one_iff_abs_lt_one).2 hratio
    apply Real.exp_le_one_iff.mpr
    have hden : 0 < 1 - (position / radius) ^ 2 := by linarith
    exact (div_nonpos_of_nonpos_of_nonneg (by norm_num) hden.le)
  · norm_num

end ConnesWeilRH.Dev
