import ConnesWeilRH.Dev.C1RepresentativePartitionCoverage2763

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed

theorem leftChild_of_lt_midpoint2764 {x : ℝ}
    (hx : representativeCell2736.Mem x)
    (hxm : x < leftCell2740.hi) :
    leftCell2740.Mem x := by
  exact ⟨hx.1, le_of_lt hxm⟩

theorem rightChild_of_gt_midpoint2764 {x : ℝ}
    (hx : representativeCell2736.Mem x)
    (hxm : rightCell2740.lo < x) :
    rightCell2740.Mem x := by
  exact ⟨le_of_lt hxm, hx.2⟩

end ConnesWeilRH.Source.C1ExplicitSmoothSeed
