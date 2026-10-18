import ConnesWeilRH.Dev.C1RouteBSeedRectCornerNorm2810
import ConnesWeilRH.Dev.C1RouteBSeedCellGeometry2809

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed

theorem routeB_d4d7_corner_norm2831
    (i : ℕ)
    {norm4 norm7 : ℝ}
    (h4 : (seedTransitionJetInterval2734 (routeBSeedCell2809 i) 4).endpointAbsMax ≤ norm4)
    (h7 : (seedTransitionJetInterval2734 (routeBSeedCell2809 i) 7).endpointAbsMax ≤ norm7) :
    (seedJetComplexRect2808 (routeBSeedCell2809 i) 4).cornerNorm ≤ norm4 ∧
      (seedJetComplexRect2808 (routeBSeedCell2809 i) 7).cornerNorm ≤ norm7 := by
  have h4eq := seedJetComplexRect_cornerNorm_eq_absMax2810
    (routeBSeedCell2809 i) 4
  have h7eq := seedJetComplexRect_cornerNorm_eq_absMax2810
    (routeBSeedCell2809 i) 7
  exact ⟨h4eq ▸ h4, h7eq ▸ h7⟩

theorem routeB_d4d7_corner_norm_self_bound2831 (i : ℕ) :
    (seedJetComplexRect2808 (routeBSeedCell2809 i) 4).cornerNorm ≤
        (seedTransitionJetInterval2734 (routeBSeedCell2809 i) 4).endpointAbsMax ∧
    (seedJetComplexRect2808 (routeBSeedCell2809 i) 7).cornerNorm ≤
        (seedTransitionJetInterval2734 (routeBSeedCell2809 i) 7).endpointAbsMax := by
  constructor <;> rw [seedJetComplexRect_cornerNorm_eq_absMax2810]

end ConnesWeilRH.Source.C1ExplicitSmoothSeed
