import ConnesWeilRH.Dev.C1ExpTailTightBound2773

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed

open ConnesWeilRH.Dev

theorem representativePhaseExpTail_le_one_div_2402774 :
    expTail (-(phaseJetInterval2734 representativeCell2736 0).lo / 4) ≤
      (1 : ℝ) / 240 := by
  apply expTail_le_one_div_2402773
  · have h := representativePhaseExpTail_le_scaled_phase2772
    have hP : (phaseJetInterval2734 representativeCell2736 0).hi ≤ 0 := by
      rw [show (phaseJetInterval2734 representativeCell2736 0).hi =
        (1 - representativeCell2736.hi)⁻¹ - representativeCell2736.hi⁻¹ by
        simp [phaseJetInterval2734, reciprocalJetInterval2734, reflectedCoordinateJetInterval2734,
          coordinateJetInterval2734, RealInterval2429.sub, RealInterval2429.invPositive,
          RealInterval2429.point]]
      norm_num [representativeCell2736]
    have hord := (phaseJetInterval2734 representativeCell2736 0).ord
    have hPlo : (phaseJetInterval2734 representativeCell2736 0).lo ≤ 0 := by
      linarith
    have htail : 0 ≤ expTail (-(phaseJetInterval2734 representativeCell2736 0).lo / 4) :=
      expTail_nonneg (by linarith)
    linarith
  · have hP : (phaseJetInterval2734 representativeCell2736 0).hi ≤ 0 := by
      rw [show (phaseJetInterval2734 representativeCell2736 0).hi =
        (1 - representativeCell2736.hi)⁻¹ - representativeCell2736.hi⁻¹ by
        simp [phaseJetInterval2734, reciprocalJetInterval2734, reflectedCoordinateJetInterval2734,
          coordinateJetInterval2734, RealInterval2429.sub, RealInterval2429.invPositive,
          RealInterval2429.point]]
      norm_num [representativeCell2736]
    have hcap : -(phaseJetInterval2734 representativeCell2736 0).lo ≤ (4 : ℝ) := by
      rw [show (phaseJetInterval2734 representativeCell2736 0).lo =
        (1 - representativeCell2736.lo)⁻¹ - representativeCell2736.lo⁻¹ by
        simp [phaseJetInterval2734, reciprocalJetInterval2734, reflectedCoordinateJetInterval2734,
          coordinateJetInterval2734, RealInterval2429.sub, RealInterval2429.invPositive,
          RealInterval2429.point]]
      norm_num [representativeCell2736]
    linarith

end ConnesWeilRH.Source.C1ExplicitSmoothSeed
