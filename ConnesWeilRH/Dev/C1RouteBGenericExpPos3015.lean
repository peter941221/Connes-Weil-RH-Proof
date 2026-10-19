import ConnesWeilRH.Dev.C1RouteBCayleyNormBound3011
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

namespace ConnesWeilRH.Dev

theorem complex_exp_re_pos_of_norm_le3015 {z : ℂ}
    (hz : ‖z‖ ≤ (80 : ℝ) / 399) :
    0 < (Complex.exp z).re := by
  rw [Complex.exp_re]
  have hi : |z.im| ≤ ‖z‖ := by
    exact le_trans (le_abs_self _) (Complex.abs_im_le_norm _)
  have hp : (80 : ℝ) / 399 < Real.pi / 2 := by
    have hpi := Real.pi_gt_three
    norm_num
    linarith
  have him : z.im ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [hi.trans hz, abs_nonneg z.im]
  exact mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo him)

end ConnesWeilRH.Dev
