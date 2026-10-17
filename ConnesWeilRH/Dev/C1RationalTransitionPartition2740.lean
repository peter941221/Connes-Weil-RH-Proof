import ConnesWeilRH.Dev.C1RepresentativeRationalTransition2739

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed
open ConnesWeilRH.Dev
noncomputable section

def leftCell2740 : RealInterval2429 :=
  { lo := representativeCell2736.lo
    hi := (representativeCell2736.lo + representativeCell2736.hi) / 2 }

def rightCell2740 : RealInterval2429 :=
  { lo := (representativeCell2736.lo + representativeCell2736.hi) / 2
    hi := representativeCell2736.hi }

theorem partitionRationalTransitionJet_mem2740 {x : ℝ} (n : ℕ)
    (hx : leftCell2740.Mem x ∨ rightCell2740.Mem x) :
    (rationalSeedTransitionJet2738 leftCell2740 4 n).Mem (iteratedDeriv n Real.smoothTransition x) ∨
    (rationalSeedTransitionJet2738 rightCell2740 4 n).Mem (iteratedDeriv n Real.smoothTransition x) := by
  classical
  rcases hx with hleft | hright
  · have hlo : 0 < leftCell2740.lo := by norm_num [leftCell2740, representativeCell2736]
    have hhi : leftCell2740.hi < 1 := by norm_num [leftCell2740, representativeCell2736]
    have hp := phaseJetInterval_mem2734 leftCell2740 0 hlo hhi hleft
    have hP : (phaseJetInterval2734 leftCell2740 0).hi ≤ 0 := by
      have h := hp.2
      rw [show (phaseJetInterval2734 leftCell2740 0).hi =
        (1 - leftCell2740.hi)⁻¹ - leftCell2740.hi⁻¹ by
        simp [phaseJetInterval2734, reciprocalJetInterval2734,
          reflectedCoordinateJetInterval2734, coordinateJetInterval2734,
          RealInterval2429.sub, RealInterval2429.invPositive,
          RealInterval2429.point]]
      norm_num [leftCell2740, representativeCell2736]
    have hcap : -(phaseJetInterval2734 leftCell2740 0).lo ≤ (4 : ℝ) := by
      rw [show (phaseJetInterval2734 leftCell2740 0).lo =
        (1 - leftCell2740.lo)⁻¹ - leftCell2740.lo⁻¹ by
        simp [phaseJetInterval2734, reciprocalJetInterval2734,
          reflectedCoordinateJetInterval2734, coordinateJetInterval2734,
          RealInterval2429.sub, RealInterval2429.point,
          RealInterval2429.invPositive]]
      norm_num [leftCell2740, representativeCell2736]
    exact Or.inl (rationalSeedTransitionJet_mem2738 leftCell2740 4 n
      (by norm_num) hlo hhi hP hcap hleft)
  · have hlo : 0 < rightCell2740.lo := by norm_num [rightCell2740, representativeCell2736]
    have hhi : rightCell2740.hi < 1 := by norm_num [rightCell2740, representativeCell2736]
    have hp := phaseJetInterval_mem2734 rightCell2740 0 hlo hhi hright
    have hP : (phaseJetInterval2734 rightCell2740 0).hi ≤ 0 := by
      have h := hp.2
      rw [show (phaseJetInterval2734 rightCell2740 0).hi =
        (1 - rightCell2740.hi)⁻¹ - rightCell2740.hi⁻¹ by
        simp [phaseJetInterval2734, reciprocalJetInterval2734,
          reflectedCoordinateJetInterval2734, coordinateJetInterval2734,
          RealInterval2429.sub, RealInterval2429.invPositive,
          RealInterval2429.point]]
      norm_num [rightCell2740, representativeCell2736]
    have hcap : -(phaseJetInterval2734 rightCell2740 0).lo ≤ (4 : ℝ) := by
      rw [show (phaseJetInterval2734 rightCell2740 0).lo =
        (1 - rightCell2740.lo)⁻¹ - rightCell2740.lo⁻¹ by
        simp [phaseJetInterval2734, reciprocalJetInterval2734,
          reflectedCoordinateJetInterval2734, coordinateJetInterval2734,
          RealInterval2429.sub, RealInterval2429.point,
          RealInterval2429.invPositive]]
      norm_num [rightCell2740, representativeCell2736]
    exact Or.inr (rationalSeedTransitionJet_mem2738 rightCell2740 4 n
      (by norm_num) hlo hhi hP hcap hright)

theorem representativeCell_partition2740 {x : ℝ}
    (hx : representativeCell2736.Mem x) :
    leftCell2740.Mem x ∨ rightCell2740.Mem x := by
  by_cases hxm : x ≤ (representativeCell2736.lo + representativeCell2736.hi) / 2
  · left
    constructor
    · exact hx.1
    · exact hxm
  · right
    constructor
    · exact le_of_not_ge hxm
    · exact hx.2

theorem representativeRationalTransitionPartition_mem2740 {x : ℝ} (n : ℕ)
    (hx : representativeCell2736.Mem x) :
    (rationalSeedTransitionJet2738 leftCell2740 4 n).Mem
        (iteratedDeriv n Real.smoothTransition x) ∨
    (rationalSeedTransitionJet2738 rightCell2740 4 n).Mem
        (iteratedDeriv n Real.smoothTransition x) := by
  exact partitionRationalTransitionJet_mem2740 n
    (representativeCell_partition2740 hx)

theorem partitionCells_ordered2740 :
    representativeCell2736.lo ≤ leftCell2740.hi ∧
    leftCell2740.hi = rightCell2740.lo ∧
    rightCell2740.lo ≤ representativeCell2736.hi := by
  constructor
  · norm_num [leftCell2740, representativeCell2736]
  constructor
  · rfl
  · norm_num [rightCell2740, representativeCell2736]

theorem partitionCells_subset2740 {x : ℝ}
    (hx : leftCell2740.Mem x ∨ rightCell2740.Mem x) :
    representativeCell2736.Mem x := by
  rcases hx with hleft | hright
  · exact ⟨hleft.1, le_trans hleft.2 (by
      norm_num [leftCell2740, representativeCell2736])⟩
  · exact ⟨le_trans (by
      norm_num [rightCell2740, representativeCell2736]) hright.1, hright.2⟩

end
end ConnesWeilRH.Source.C1ExplicitSmoothSeed




