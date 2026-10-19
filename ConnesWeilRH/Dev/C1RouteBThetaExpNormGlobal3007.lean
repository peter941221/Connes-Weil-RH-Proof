import ConnesWeilRH.Dev.C1RouteBThetaArgumentNorm2986
import ConnesWeilRH.Dev.C1RouteBThetaDoubledArgument2992
import Mathlib.Tactic

namespace ConnesWeilRH.Dev

theorem routeBThetaExpNormGlobal3007 (θ : ℝ) :
    ‖Complex.exp (routeBThetaDoubledArgument2992 θ)‖ ≤
      Real.exp ((80 : ℝ) / 399) := by
  rw [Complex.norm_exp]
  have harg := routeBThetaArgumentNorm2986 θ
  have harg2 :
      ‖routeBThetaDoubledArgument2992 θ‖ ≤ (80 : ℝ) / 399 := by
    rw [routeBThetaDoubledArgumentDefinition2992]
    have h := harg
    rw [show (4 : ℂ) = 2 * 2 by norm_num, mul_assoc] at ⊢
    rw [norm_mul]
    norm_num
    nlinarith [h]
  exact Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans harg2)

end ConnesWeilRH.Dev
