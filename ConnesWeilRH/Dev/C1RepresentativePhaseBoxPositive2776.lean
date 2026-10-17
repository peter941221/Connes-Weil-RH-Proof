import ConnesWeilRH.Dev.C1RepresentativePhaseBoxOrdered2775

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed

open ConnesWeilRH.Dev

theorem representativePhaseExpBox_positive2776 :
    0 < (rationalPhaseExpBox2736 (phaseJetInterval2734 representativeCell2736 0) 4).lo ∧
    0 < (rationalPhaseExpBox2736 (phaseJetInterval2734 representativeCell2736 0) 4).hi := by
  constructor
  · apply rationalPhaseExpBox_lo_pos2742
    · norm_num
    · rw [show (phaseJetInterval2734 representativeCell2736 0).lo =
        (1 - representativeCell2736.lo)⁻¹ - representativeCell2736.lo⁻¹ by
        simp [phaseJetInterval2734, reciprocalJetInterval2734, reflectedCoordinateJetInterval2734,
          coordinateJetInterval2734, RealInterval2429.sub, RealInterval2429.invPositive,
          RealInterval2429.point]]
      norm_num [representativeCell2736]
    · rw [show (phaseJetInterval2734 representativeCell2736 0).lo =
        (1 - representativeCell2736.lo)⁻¹ - representativeCell2736.lo⁻¹ by
        simp [phaseJetInterval2734, reciprocalJetInterval2734, reflectedCoordinateJetInterval2734,
          coordinateJetInterval2734, RealInterval2429.sub, RealInterval2429.invPositive,
          RealInterval2429.point]]
      norm_num [representativeCell2736]
  · apply rationalPhaseExpBox_hi_pos2742
    · norm_num
    · rw [show (phaseJetInterval2734 representativeCell2736 0).hi =
        (1 - representativeCell2736.hi)⁻¹ - representativeCell2736.hi⁻¹ by
        simp [phaseJetInterval2734, reciprocalJetInterval2734, reflectedCoordinateJetInterval2734,
          coordinateJetInterval2734, RealInterval2429.sub, RealInterval2429.invPositive,
          RealInterval2429.point]]
      norm_num [representativeCell2736]
    · rw [show (phaseJetInterval2734 representativeCell2736 0).hi =
        (1 - representativeCell2736.hi)⁻¹ - representativeCell2736.hi⁻¹ by
        simp [phaseJetInterval2734, reciprocalJetInterval2734, reflectedCoordinateJetInterval2734,
          coordinateJetInterval2734, RealInterval2429.sub, RealInterval2429.invPositive,
          RealInterval2429.point]]
      norm_num [representativeCell2736]

end ConnesWeilRH.Source.C1ExplicitSmoothSeed
