import ConnesWeilRH.Dev.C1RouteBThetaArgumentDenom2985
import ConnesWeilRH.Dev.C1RouteBDoubledArgumentFormula2990

namespace ConnesWeilRH.Dev

noncomputable def routeBThetaDoubledArgument2992 (θ : ℝ) : ℂ :=
  4 * routeBThetaTCoarse2982 θ /
    (1 - (routeBThetaTCoarse2982 θ) ^ 2)

theorem routeBThetaDoubledArgumentDenom2992 (θ : ℝ) :
    1 - (routeBThetaTCoarse2982 θ) ^ 2 ≠ 0 :=
  routeBThetaArgumentDenomNonzero2985 θ

theorem routeBThetaDoubledArgumentDefinition2992 (θ : ℝ) :
    routeBThetaDoubledArgument2992 θ =
      4 * routeBThetaTCoarse2982 θ /
        (1 - (routeBThetaTCoarse2982 θ) ^ 2) := by
  rfl

end ConnesWeilRH.Dev
