import ConnesWeilRH.Dev.C1RepresentativePartitionGeometry2761

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed

theorem representativeD4D7RationalBudget2762 :
    (∫ x in leftCell2740.lo..leftCell2740.hi,
      ‖iteratedDeriv 4 Real.smoothTransition x‖) +
      (∫ x in rightCell2740.lo..rightCell2740.hi,
        ‖iteratedDeriv 4 Real.smoothTransition x‖) ≤
        ((2047 : ℝ) / 33554432) * representativeD4Box2755.endpointAbsMax ∧
    (∫ x in leftCell2740.lo..leftCell2740.hi,
      ‖iteratedDeriv 7 Real.smoothTransition x‖) +
      (∫ x in rightCell2740.lo..rightCell2740.hi,
        ‖iteratedDeriv 7 Real.smoothTransition x‖) ≤
        ((2047 : ℝ) / 33554432) * representativeD7Box2755.endpointAbsMax := by
  have h := representativeD4D7Partition_budget2759
  rw [representativeCell2736_length_eq] at h
  exact h

end ConnesWeilRH.Source.C1ExplicitSmoothSeed
