import ConnesWeilRH.Dev.C1RouteBThetaArgumentNorm2986
import ConnesWeilRH.Dev.C1RouteBThetaDoubledArgument2992
import Mathlib.Tactic

namespace ConnesWeilRH.Dev

theorem routeBThetaDoubledArgumentNormGlobal3008 (θ : ℝ) :
    ‖routeBThetaDoubledArgument2992 θ‖ ≤ (80 : ℝ) / 399 := by
  have harg := routeBThetaArgumentNorm2986 θ
  rw [routeBThetaDoubledArgumentDefinition2992]
  rw [show (4 : ℂ) = 2 * 2 by norm_num, mul_assoc, norm_mul]
  norm_num
  nlinarith [harg]

end ConnesWeilRH.Dev
