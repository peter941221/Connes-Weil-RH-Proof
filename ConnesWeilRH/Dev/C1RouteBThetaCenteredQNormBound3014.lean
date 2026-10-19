import ConnesWeilRH.Dev.C1RouteBCenteredQExpForm3013
import ConnesWeilRH.Dev.C1RouteBThetaExpNormGlobal3007
import ConnesWeilRH.Dev.C1RouteBExpPlusOneNormLower3010

namespace ConnesWeilRH.Dev

theorem routeBThetaCenteredQNormBound3014 (θ : ℝ) :
    ‖routeBCenteredQ2900 (routeBThetaTCoarse2982 θ)‖ ≤
      Real.exp ((80 : ℝ) / 399) := by
  rw [routeBCenteredQ_exp_form3013]
  have hden := routeBThetaExpPlusOneNormLower3010 θ
  have hnum :
      ‖Complex.exp (routeBThetaDoubledArgument2992 θ)‖ ≤
        Real.exp ((80 : ℝ) / 399) :=
    routeBThetaExpNormGlobal3007 θ
  have hpos : 0 < ‖Complex.exp (routeBThetaDoubledArgument2992 θ) + 1‖ :=
    by linarith
  rw [norm_div]
  apply (div_le_iff₀ hpos).2
  have hone : 1 ≤ ‖Complex.exp (routeBThetaDoubledArgument2992 θ) + 1‖ :=
    le_of_lt hden
  nlinarith [hnum, norm_nonneg
    (Complex.exp (routeBThetaDoubledArgument2992 θ))]

end ConnesWeilRH.Dev
