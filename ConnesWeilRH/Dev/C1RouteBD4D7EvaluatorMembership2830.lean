import ConnesWeilRH.Dev.C1RouteBSeedCellGeometry2809

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed

open ConnesWeilRH.Dev

theorem routeB_d4d7_evaluator_membership2830 (i : ℕ) (hi : i < 8192)
    {x : ℝ} (hx : (routeBSeedCell2809 i).Mem x) :
    (seedJetComplexRect2808 (routeBSeedCell2809 i) 4).Mem
        ((iteratedDeriv 4 Real.smoothTransition
          x : ℝ) : ℂ) ∧
    (seedJetComplexRect2808 (routeBSeedCell2809 i) 7).Mem
        ((iteratedDeriv 7 Real.smoothTransition
          x : ℝ) : ℂ) := by
  have h4 := routeBSeedCell2809_d4_mem i hi hx
  have h7 := routeBSeedCell2809_d7_mem i hi hx
  exact ⟨h4, h7⟩

end ConnesWeilRH.Source.C1ExplicitSmoothSeed
