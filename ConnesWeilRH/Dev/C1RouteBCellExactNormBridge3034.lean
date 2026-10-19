import ConnesWeilRH.Dev.C1RouteBSourceCellEnvelope2834

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed

open ConnesWeilRH.Dev

theorem routeBCell_exact_norm_le_sourceNorm3034
    (i n : ℕ) (hi : i < 8192) {x : ℝ}
    (hx : (routeBSeedCell2809 i).Mem x) :
    ‖iteratedDeriv n Real.smoothTransition x‖ ≤ routeBSourceNorm2834 i n := by
  unfold routeBSourceNorm2834
  exact norm_iteratedDeriv_le_seedCellJet2734 (routeBSeedCell2809 i) n
    (routeBSeedCell2809_mem_unit i hi).1
    (routeBSeedCell2809_mem_unit i hi).2 hx

end ConnesWeilRH.Source.C1ExplicitSmoothSeed
