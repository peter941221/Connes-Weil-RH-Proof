import ConnesWeilRH.Dev.C1RouteBThetaDoubledArgumentNormGlobal3008
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

namespace ConnesWeilRH.Dev

theorem routeBThetaExpRealPartPositive3009 (θ : ℝ) :
    0 < (Complex.exp (routeBThetaDoubledArgument2992 θ)).re := by
  rw [Complex.exp_re]
  have hz := routeBThetaDoubledArgumentNormGlobal3008 θ
  have him : |(routeBThetaDoubledArgument2992 θ).im| < Real.pi / 2 := by
    have hi : |(routeBThetaDoubledArgument2992 θ).im| ≤
        ‖routeBThetaDoubledArgument2992 θ‖ := by
      exact le_trans (le_abs_self _) (Complex.abs_im_le_norm _)
    have hp : (80 : ℝ) / 399 < Real.pi / 2 := by
      have hpi := Real.pi_gt_three
      norm_num
      linarith
    exact lt_of_le_of_lt (hi.trans hz) hp
  exact mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo
    ⟨by linarith [him], by linarith [him]⟩)

end ConnesWeilRH.Dev
