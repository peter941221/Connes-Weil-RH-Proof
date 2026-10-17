import ConnesWeilRH.Dev.C1RepresentativePartitionBranch2764

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed

open ConnesWeilRH.Dev
noncomputable section

theorem leftChildTransitionJet_mem_of_lt_midpoint2765 {x : ℝ} (n : ℕ)
    (hx : representativeCell2736.Mem x) (hxm : x < leftCell2740.hi) :
    (rationalSeedTransitionJet2738 leftCell2740 4 n).Mem
      (iteratedDeriv n Real.smoothTransition x) := by
  have hl : leftCell2740.Mem x := leftChild_of_lt_midpoint2764 hx hxm
  have hlo : 0 < leftCell2740.lo := by
    norm_num [leftCell2740, representativeCell2736]
  have hhi : leftCell2740.hi < 1 := by
    norm_num [leftCell2740, representativeCell2736]
  have hp := phaseJetInterval_mem2734 leftCell2740 0 hlo hhi hl
  have hP : (phaseJetInterval2734 leftCell2740 0).hi ≤ 0 := by
    have h := hp.2
    rw [show (phaseJetInterval2734 leftCell2740 0).hi =
      (1 - leftCell2740.hi)⁻¹ - leftCell2740.hi⁻¹ by
      simp [phaseJetInterval2734, reciprocalJetInterval2734,
        reflectedCoordinateJetInterval2734, coordinateJetInterval2734,
        RealInterval2429.sub, RealInterval2429.invPositive,
        RealInterval2429.point]]
    norm_num [leftCell2740, representativeCell2736] at h ⊢
  have hcap : -(phaseJetInterval2734 leftCell2740 0).lo ≤ (4 : ℝ) := by
    rw [show (phaseJetInterval2734 leftCell2740 0).lo =
      (1 - leftCell2740.lo)⁻¹ - leftCell2740.lo⁻¹ by
      simp [phaseJetInterval2734, reciprocalJetInterval2734,
        reflectedCoordinateJetInterval2734, coordinateJetInterval2734,
        RealInterval2429.sub, RealInterval2429.invPositive,
        RealInterval2429.point]]
    norm_num [leftCell2740, representativeCell2736]
  exact rationalSeedTransitionJet_mem2738 leftCell2740 4 n
    (by norm_num) hlo hhi hP hcap hl

theorem rightChildTransitionJet_mem_of_gt_midpoint2765 {x : ℝ} (n : ℕ)
    (hx : representativeCell2736.Mem x) (hxm : rightCell2740.lo < x) :
    (rationalSeedTransitionJet2738 rightCell2740 4 n).Mem
      (iteratedDeriv n Real.smoothTransition x) := by
  have hr : rightCell2740.Mem x := rightChild_of_gt_midpoint2764 hx hxm
  have hlo : 0 < rightCell2740.lo := by
    norm_num [rightCell2740, representativeCell2736]
  have hhi : rightCell2740.hi < 1 := by
    norm_num [rightCell2740, representativeCell2736]
  have hp := phaseJetInterval_mem2734 rightCell2740 0 hlo hhi hr
  have hP : (phaseJetInterval2734 rightCell2740 0).hi ≤ 0 := by
    have h := hp.2
    rw [show (phaseJetInterval2734 rightCell2740 0).hi =
      (1 - rightCell2740.hi)⁻¹ - rightCell2740.hi⁻¹ by
      simp [phaseJetInterval2734, reciprocalJetInterval2734,
        reflectedCoordinateJetInterval2734, coordinateJetInterval2734,
        RealInterval2429.sub, RealInterval2429.invPositive,
        RealInterval2429.point]]
    norm_num [rightCell2740, representativeCell2736] at h ⊢
  have hcap : -(phaseJetInterval2734 rightCell2740 0).lo ≤ (4 : ℝ) := by
    rw [show (phaseJetInterval2734 rightCell2740 0).lo =
      (1 - rightCell2740.lo)⁻¹ - rightCell2740.lo⁻¹ by
      simp [phaseJetInterval2734, reciprocalJetInterval2734,
        reflectedCoordinateJetInterval2734, coordinateJetInterval2734,
        RealInterval2429.sub, RealInterval2429.invPositive,
        RealInterval2429.point]]
    norm_num [rightCell2740, representativeCell2736]
  exact rationalSeedTransitionJet_mem2738 rightCell2740 4 n
    (by norm_num) hlo hhi hP hcap hr

end
end ConnesWeilRH.Source.C1ExplicitSmoothSeed
