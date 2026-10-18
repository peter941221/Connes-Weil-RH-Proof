import ConnesWeilRH.Dev.C1RouteBSubcellTMembershipClosed2933
import ConnesWeilRH.Dev.C1RouteBLocalStageT2910

namespace ConnesWeilRH.Dev

theorem routeBSubcellTNormClosed2934 {θ : ℝ}
    (hθ : (107 : ℝ) * Real.pi / 64 ≤ θ)
    (hθ' : θ ≤ (107 : ℝ) * Real.pi / 64 + Real.pi / 1024) :
    ‖(1 / 20 : ℝ) * (Real.cos θ + Complex.I * Real.sin θ)‖ ≤ (1 : ℝ) / 20 := by
  apply routeBLocalStageTNormBound2910
  exact routeBSubcellTMembershipClosed2933 hθ hθ'

theorem routeBSubcellArgumentNormClosed2934 {θ : ℝ}
    (hθ : (107 : ℝ) * Real.pi / 64 ≤ θ)
    (hθ' : θ ≤ (107 : ℝ) * Real.pi / 64 + Real.pi / 1024) :
    ‖2 * ((1 / 20 : ℝ) * (Real.cos θ + Complex.I * Real.sin θ)) /
        (1 - ((1 / 20 : ℝ) * (Real.cos θ + Complex.I * Real.sin θ)) ^ 2)‖ ≤
      (40 : ℝ) / 399 := by
  exact routeBArgumentNormBound2900 _ (routeBSubcellTNormClosed2934 hθ hθ')

end ConnesWeilRH.Dev
