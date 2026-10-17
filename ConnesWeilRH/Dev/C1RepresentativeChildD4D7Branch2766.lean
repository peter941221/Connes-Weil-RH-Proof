import ConnesWeilRH.Dev.C1RepresentativeChildJetBranch2765

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed

theorem leftChildD4D7_mem_of_lt_midpoint2766 {x : ℝ}
    (hx : representativeCell2736.Mem x) (hxm : x < leftCell2740.hi) :
    (rationalSeedTransitionJet2738 leftCell2740 4 4).Mem
        (iteratedDeriv 4 Real.smoothTransition x) ∧
      (rationalSeedTransitionJet2738 leftCell2740 4 7).Mem
        (iteratedDeriv 7 Real.smoothTransition x) := by
  exact ⟨leftChildTransitionJet_mem_of_lt_midpoint2765 4 hx hxm,
    leftChildTransitionJet_mem_of_lt_midpoint2765 7 hx hxm⟩

theorem rightChildD4D7_mem_of_gt_midpoint2766 {x : ℝ}
    (hx : representativeCell2736.Mem x) (hxm : rightCell2740.lo < x) :
    (rationalSeedTransitionJet2738 rightCell2740 4 4).Mem
        (iteratedDeriv 4 Real.smoothTransition x) ∧
      (rationalSeedTransitionJet2738 rightCell2740 4 7).Mem
        (iteratedDeriv 7 Real.smoothTransition x) := by
  exact ⟨rightChildTransitionJet_mem_of_gt_midpoint2765 4 hx hxm,
    rightChildTransitionJet_mem_of_gt_midpoint2765 7 hx hxm⟩

end ConnesWeilRH.Source.C1ExplicitSmoothSeed
