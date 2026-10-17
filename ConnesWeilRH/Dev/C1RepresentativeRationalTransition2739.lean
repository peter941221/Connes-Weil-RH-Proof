import ConnesWeilRH.Dev.C1SeedRationalTransitionJet2738

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed

open ConnesWeilRH.Dev

noncomputable section

theorem representativeRationalTransitionJet_mem2739 {x : ℝ} (n : ℕ)
    (hx : representativeCell2736.Mem x) :
    (rationalSeedTransitionJet2738 representativeCell2736 4 n).Mem
      (iteratedDeriv n Real.smoothTransition x) := by
  have hlo : 0 < representativeCell2736.lo := by
    norm_num [representativeCell2736]
  have hhi : representativeCell2736.hi < 1 := by
    norm_num [representativeCell2736]
  have hp := phaseJetInterval_mem2734 representativeCell2736 0 hlo hhi hx
  have hP : (phaseJetInterval2734 representativeCell2736 0).hi ≤ 0 := by
    have h := hp.2
    rw [show (phaseJetInterval2734 representativeCell2736 0).hi =
      (1 - representativeCell2736.hi)⁻¹ - representativeCell2736.hi⁻¹ by
      simp [phaseJetInterval2734, reciprocalJetInterval2734,
        reflectedCoordinateJetInterval2734, coordinateJetInterval2734,
        RealInterval2429.sub, RealInterval2429.invPositive,
        RealInterval2429.point]]
    norm_num [representativeCell2736]
  have hcap : -(phaseJetInterval2734 representativeCell2736 0).lo ≤ (4 : ℝ) := by
    rw [show (phaseJetInterval2734 representativeCell2736 0).lo =
      (1 - representativeCell2736.lo)⁻¹ - representativeCell2736.lo⁻¹ by
      simp [phaseJetInterval2734, reciprocalJetInterval2734,
        reflectedCoordinateJetInterval2734, coordinateJetInterval2734,
        RealInterval2429.sub, RealInterval2429.invPositive,
        RealInterval2429.point]]
    norm_num [representativeCell2736]
  exact rationalSeedTransitionJet_mem2738 representativeCell2736 4 n
    (by norm_num) hlo hhi hP hcap hx

end
end ConnesWeilRH.Source.C1ExplicitSmoothSeed
