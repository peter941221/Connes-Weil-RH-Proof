import ConnesWeilRH.Dev.C1RouteBD4D7EvaluatorMembership2830
import ConnesWeilRH.Dev.C1RouteBEndpointAdapter2833

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed

open ConnesWeilRH.Dev
open Set

theorem routeBConcreteEndpoint_mono3022 {k : ℕ} (hk : k < 8192) :
    routeBSeedEndpoint2833 k ≤ routeBSeedEndpoint2833 (k + 1) := by
  exact routeBSeedEndpoint2833_mono (Nat.le_add_right k 1)

theorem routeBConcreteCell_mem_of_endpoint_interval3022
    {k : ℕ} (hk : k < 8192) {x : ℝ}
    (hx : x ∈ Icc (routeBSeedEndpoint2833 k)
      (routeBSeedEndpoint2833 (k + 1))) :
    (routeBSeedCell2809 k).Mem x := by
  change (routeBSeedCell2809 k).lo ≤ x ∧
    x ≤ (routeBSeedCell2809 k).hi
  simpa [routeBSeedEndpoint2833_cell_eq] using hx

theorem routeBConcreteD4D7Membership3022 {k : ℕ} (hk : k < 8192)
    {x : ℝ} (hx : x ∈ Icc (routeBSeedEndpoint2833 k)
      (routeBSeedEndpoint2833 (k + 1))) :
    (seedJetComplexRect2808 (routeBSeedCell2809 k) 4).Mem
        ((iteratedDeriv 4 Real.smoothTransition x : ℝ) : ℂ) ∧
    (seedJetComplexRect2808 (routeBSeedCell2809 k) 7).Mem
        ((iteratedDeriv 7 Real.smoothTransition x : ℝ) : ℂ) := by
  exact routeB_d4d7_evaluator_membership2830 hk
    (routeBConcreteCell_mem_of_endpoint_interval3022 hk hx)

end ConnesWeilRH.Source.C1ExplicitSmoothSeed
