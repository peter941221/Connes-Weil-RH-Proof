import ConnesWeilRH.Dev.C1RepresentativeClosedChildJet2767

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed

theorem leftClosedChildD4D7_mem2768 {x : ℝ}
    (hl : leftCell2740.Mem x) :
    (rationalSeedTransitionJet2738 leftCell2740 4 4).Mem
        (iteratedDeriv 4 Real.smoothTransition x) ∧
      (rationalSeedTransitionJet2738 leftCell2740 4 7).Mem
        (iteratedDeriv 7 Real.smoothTransition x) := by
  exact ⟨leftChildTransitionJet_mem_of_mem2767 4 hl,
    leftChildTransitionJet_mem_of_mem2767 7 hl⟩

theorem rightClosedChildD4D7_mem2768 {x : ℝ}
    (hr : rightCell2740.Mem x) :
    (rationalSeedTransitionJet2738 rightCell2740 4 4).Mem
        (iteratedDeriv 4 Real.smoothTransition x) ∧
      (rationalSeedTransitionJet2738 rightCell2740 4 7).Mem
        (iteratedDeriv 7 Real.smoothTransition x) := by
  exact ⟨rightChildTransitionJet_mem_of_mem2767 4 hr,
    rightChildTransitionJet_mem_of_mem2767 7 hr⟩

end ConnesWeilRH.Source.C1ExplicitSmoothSeed
