import ConnesWeilRH.Dev.C1RouteBExpRealPartPositive3009
import Mathlib.Tactic

namespace ConnesWeilRH.Dev

theorem complex_norm_add_one_gt_one_of_re_pos3010 {w : ℂ}
    (hw : 0 < w.re) :
    1 < ‖w + 1‖ := by
  have hre : (1 : ℝ) < (w + 1).re := by
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith
  have habs : |(w + 1).re| = (w + 1).re := abs_of_pos (by linarith)
  have hcoord : |(w + 1).re| ≤ ‖w + 1‖ := Complex.abs_re_le_norm _
  rw [habs] at hcoord
  exact lt_of_lt_of_le hre hcoord

theorem routeBThetaExpPlusOneNormLower3010 (θ : ℝ) :
    1 < ‖Complex.exp (routeBThetaDoubledArgument2992 θ) + 1‖ :=
  complex_norm_add_one_gt_one_of_re_pos3010
    (routeBThetaExpRealPartPositive3009 θ)

end ConnesWeilRH.Dev
