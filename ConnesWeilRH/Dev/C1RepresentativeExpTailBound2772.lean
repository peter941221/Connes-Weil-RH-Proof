import ConnesWeilRH.Dev.C1RepresentativeRationalTransition2739

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed

open ConnesWeilRH.Dev
noncomputable section

theorem representativePhaseExpTail_le_scaled_phase2772 :
    expTail (-(phaseJetInterval2734 representativeCell2736 0).lo / 4) ≤
      -(phaseJetInterval2734 representativeCell2736 0).lo / 4 := by
  have hlo : 0 < representativeCell2736.lo := by
    norm_num [representativeCell2736]
  have hhi : representativeCell2736.hi < 1 := by
    norm_num [representativeCell2736]
  have hp := phaseJetInterval_mem2734 representativeCell2736 0 hlo hhi
    (show representativeCell2736.Mem representativeCell2736.lo by
      constructor <;> norm_num [representativeCell2736])
  have hP : (phaseJetInterval2734 representativeCell2736 0).hi ≤ 0 := by
    have h := hp.2
    rw [show (phaseJetInterval2734 representativeCell2736 0).hi =
      (1 - representativeCell2736.hi)⁻¹ - representativeCell2736.hi⁻¹ by
      simp [phaseJetInterval2734, reciprocalJetInterval2734,
        reflectedCoordinateJetInterval2734, coordinateJetInterval2734,
        RealInterval2429.sub, RealInterval2429.invPositive,
        RealInterval2429.point]]
    norm_num [representativeCell2736] at h ⊢
  have hcap : -(phaseJetInterval2734 representativeCell2736 0).lo ≤ (4 : ℝ) := by
    rw [show (phaseJetInterval2734 representativeCell2736 0).lo =
      (1 - representativeCell2736.lo)⁻¹ - representativeCell2736.lo⁻¹ by
      simp [phaseJetInterval2734, reciprocalJetInterval2734,
        reflectedCoordinateJetInterval2734, coordinateJetInterval2734,
        RealInterval2429.sub, RealInterval2429.invPositive,
        RealInterval2429.point]]
    norm_num [representativeCell2736]
  apply expTail_le_self
  · have hplo : (phaseJetInterval2734 representativeCell2736 0).lo ≤ 0 := by
      have h := hp.1
      simpa only [iteratedDeriv_zero] using le_trans h (le_trans hp.2 hP)
    linarith
  · linarith

end
end ConnesWeilRH.Source.C1ExplicitSmoothSeed
