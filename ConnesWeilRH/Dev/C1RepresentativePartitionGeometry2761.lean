import ConnesWeilRH.Dev.C1RepresentativeCellGeometry2760

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed

theorem leftCell2740_length_eq :
    leftCell2740.hi - leftCell2740.lo = (2047 : ℝ) / 67108864 := by
  norm_num [leftCell2740, representativeCell2736]

theorem rightCell2740_length_eq :
    rightCell2740.hi - rightCell2740.lo = (2047 : ℝ) / 67108864 := by
  norm_num [rightCell2740, representativeCell2736]

theorem partitionCellLengths_sum2761 :
    (leftCell2740.hi - leftCell2740.lo) +
      (rightCell2740.hi - rightCell2740.lo) =
        representativeCell2736.hi - representativeCell2736.lo := by
  rw [leftCell2740_length_eq, rightCell2740_length_eq,
    representativeCell2736_length_eq]
  norm_num

end ConnesWeilRH.Source.C1ExplicitSmoothSeed
