import ConnesWeilRH.Dev.C1RepresentativeD4D7PartitionBudget2759

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed

theorem representativeCell2736_length_eq :
    representativeCell2736.hi - representativeCell2736.lo =
      (2047 : ℝ) / 33554432 := by
  norm_num [representativeCell2736]

theorem representativeCell2736_length_pos :
    0 < representativeCell2736.hi - representativeCell2736.lo := by
  rw [representativeCell2736_length_eq]
  norm_num

end ConnesWeilRH.Source.C1ExplicitSmoothSeed
