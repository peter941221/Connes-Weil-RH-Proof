import ConnesWeilRH.Dev.C1RationalBoxBridge2744
import ConnesWeilRH.Dev.C1RationalTransitionPartition2740

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed

open ConnesWeilRH.Dev
noncomputable section

def representativeD4Box2755 : RealInterval2429 :=
  rationalSeedTransitionJet2738 representativeCell2736 4 4

def representativeD7Box2755 : RealInterval2429 :=
  rationalSeedTransitionJet2738 representativeCell2736 4 7

theorem representativeD4Box_mem2755 {x : ℝ}
    (hx : representativeCell2736.Mem x) :
    representativeD4Box2755.Mem (iteratedDeriv 4 Real.smoothTransition x) := by
  exact representativeRationalTransitionJet_mem2739 4 hx

theorem representativeD7Box_mem2755 {x : ℝ}
    (hx : representativeCell2736.Mem x) :
    representativeD7Box2755.Mem (iteratedDeriv 7 Real.smoothTransition x) := by
  exact representativeRationalTransitionJet_mem2739 7 hx

theorem representativeD4D7Boxes_mem2755 {x : ℝ}
    (hx : representativeCell2736.Mem x) :
    representativeD4Box2755.Mem (iteratedDeriv 4 Real.smoothTransition x) ∧
      representativeD7Box2755.Mem (iteratedDeriv 7 Real.smoothTransition x) := by
  exact ⟨representativeD4Box_mem2755 hx, representativeD7Box_mem2755 hx⟩

end
end ConnesWeilRH.Source.C1ExplicitSmoothSeed
