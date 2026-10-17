import ConnesWeilRH.Dev.C1RepresentativeD4D7PartitionIntegral2758

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed

noncomputable section

theorem representativeD4D7Partition_budget2759 :
    (∫ x in leftCell2740.lo..leftCell2740.hi,
      ‖iteratedDeriv 4 Real.smoothTransition x‖) +
      (∫ x in rightCell2740.lo..rightCell2740.hi,
        ‖iteratedDeriv 4 Real.smoothTransition x‖) ≤
        (representativeCell2736.hi - representativeCell2736.lo) *
          representativeD4Box2755.endpointAbsMax ∧
    (∫ x in leftCell2740.lo..leftCell2740.hi,
      ‖iteratedDeriv 7 Real.smoothTransition x‖) +
      (∫ x in rightCell2740.lo..rightCell2740.hi,
        ‖iteratedDeriv 7 Real.smoothTransition x‖) ≤
        (representativeCell2736.hi - representativeCell2736.lo) *
          representativeD7Box2755.endpointAbsMax := by
  have hsplit := representativeD4D7Partition_integral_add2758
  have hbound := representativeD4D7Cell_integral_bound2757
  constructor
  · rw [← hsplit.1]
    exact hbound.1
  · rw [← hsplit.2]
    exact hbound.2

end
end ConnesWeilRH.Source.C1ExplicitSmoothSeed
