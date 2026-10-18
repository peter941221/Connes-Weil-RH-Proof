import ConnesWeilRH.Dev.C1RouteBSeedCellGeometry2809

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed

open ConnesWeilRH.Dev

theorem seedJetComplexRect_cornerNormSq2810 (B : RealInterval2429) (n : ℕ) :
    (seedJetComplexRect2808 B n).cornerNormSq =
      (seedTransitionJetInterval2734 B n).endpointAbsMax ^ 2 := by
  simp [seedJetComplexRect2808, ComplexRect2427.cornerNormSq,
    RealInterval2429.endpointAbsMax]

theorem seedJetComplexRect_cornerNorm_eq_absMax2810
    (B : RealInterval2429) (n : ℕ) :
    (seedJetComplexRect2808 B n).cornerNorm =
      (seedTransitionJetInterval2734 B n).endpointAbsMax := by
  rw [ComplexRect2427.cornerNorm, seedJetComplexRect_cornerNormSq2810]
  rw [Real.sqrt_sq_eq_abs]
  exact abs_of_nonneg (by
    simp [RealInterval2429.endpointAbsMax])

end ConnesWeilRH.Source.C1ExplicitSmoothSeed
