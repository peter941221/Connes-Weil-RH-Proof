import ConnesWeilRH.Dev.C1RepresentativeReciprocalJet2777

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed

open ConnesWeilRH.Dev

theorem representativeTransitionD4D7_mem2778 {x : ℝ}
    (hx : representativeCell2736.Mem x) :
    (rationalSeedTransitionJet2738 representativeCell2736 4 4).Mem
        (iteratedDeriv 4 Real.smoothTransition x) ∧
      (rationalSeedTransitionJet2738 representativeCell2736 4 7).Mem
        (iteratedDeriv 7 Real.smoothTransition x) := by
  exact ⟨representativeRationalTransitionJet_mem2739 4 hx,
    representativeRationalTransitionJet_mem2739 7 hx⟩

end ConnesWeilRH.Source.C1ExplicitSmoothSeed
