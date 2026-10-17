import ConnesWeilRH.Dev.C1RepresentativePartitionGeometry2761

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed

theorem representativeCell2740_iff_childCoverage2763 {x : ℝ} :
    representativeCell2736.Mem x ↔
      leftCell2740.Mem x ∨ rightCell2740.Mem x := by
  constructor
  · exact representativeCell_partition2740
  · exact partitionCells_subset2740

end ConnesWeilRH.Source.C1ExplicitSmoothSeed
