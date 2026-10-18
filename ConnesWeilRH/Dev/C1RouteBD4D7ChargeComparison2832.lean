import ConnesWeilRH.Dev.C1RouteBD4D7CornerNorm2831

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed

theorem routeB_d4d7_charge_comparison2832
    (i : ℕ) {width charge4 charge7 norm4 norm7 : ℝ}
    (hw : 0 ≤ width)
    (h4norm : (seedTransitionJetInterval2734 (routeBSeedCell2809 i) 4).endpointAbsMax ≤ norm4)
    (h7norm : (seedTransitionJetInterval2734 (routeBSeedCell2809 i) 7).endpointAbsMax ≤ norm7)
    (h4charge : width * norm4 ≤ charge4)
    (h7charge : width * norm7 ≤ charge7) :
    width * (seedTransitionJetInterval2734 (routeBSeedCell2809 i) 4).endpointAbsMax ≤ charge4 ∧
      width * (seedTransitionJetInterval2734 (routeBSeedCell2809 i) 7).endpointAbsMax ≤ charge7 := by
  exact ⟨le_trans (mul_le_mul_of_nonneg_left h4norm hw) h4charge,
    le_trans (mul_le_mul_of_nonneg_left h7norm hw) h7charge⟩

end ConnesWeilRH.Source.C1ExplicitSmoothSeed
