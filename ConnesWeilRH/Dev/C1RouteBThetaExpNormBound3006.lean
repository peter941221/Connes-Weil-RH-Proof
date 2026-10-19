import ConnesWeilRH.Dev.C1RouteBThetaExpRectMem3005
import ConnesWeilRH.Dev.C1RouteBLocalStageExp2907

namespace ConnesWeilRH.Dev

theorem routeBThetaExpNormBound3006 {δ : ℝ}
    (hδlo : Real.pi / 192 ≤ δ)
    (hδhi : δ ≤ Real.pi / 192 + Real.pi / 1024) :
    ‖Complex.exp
        (routeBThetaDoubledArgument2992 (5 * Real.pi / 3 + δ))‖ ≤ 2 := by
  exact routeBLocalStageExpNormBound2907
    (routeBThetaExpRectMem3005 hδlo hδhi)

end ConnesWeilRH.Dev
