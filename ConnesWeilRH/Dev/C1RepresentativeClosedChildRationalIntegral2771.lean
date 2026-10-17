import ConnesWeilRH.Dev.C1RepresentativeClosedChildIntegral2770
import ConnesWeilRH.Dev.C1RepresentativePartitionGeometry2761

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed

theorem leftChildD4D7_rational_integral_bounds2771 :
    (∫ x in leftCell2740.lo..leftCell2740.hi,
      ‖iteratedDeriv 4 Real.smoothTransition x‖) ≤
        ((2047 : ℝ) / 67108864) * leftChildD4Box2770.endpointAbsMax ∧
    (∫ x in leftCell2740.lo..leftCell2740.hi,
      ‖iteratedDeriv 7 Real.smoothTransition x‖) ≤
        ((2047 : ℝ) / 67108864) * leftChildD7Box2770.endpointAbsMax := by
  have h := leftChildD4D7_integral_bounds2770
  rw [leftCell2740_length_eq] at h
  exact h

theorem rightChildD4D7_rational_integral_bounds2771 :
    (∫ x in rightCell2740.lo..rightCell2740.hi,
      ‖iteratedDeriv 4 Real.smoothTransition x‖) ≤
        ((2047 : ℝ) / 67108864) * rightChildD4Box2770.endpointAbsMax ∧
    (∫ x in rightCell2740.lo..rightCell2740.hi,
      ‖iteratedDeriv 7 Real.smoothTransition x‖) ≤
        ((2047 : ℝ) / 67108864) * rightChildD7Box2770.endpointAbsMax := by
  have h := rightChildD4D7_integral_bounds2770
  rw [rightCell2740_length_eq] at h
  exact h

end ConnesWeilRH.Source.C1ExplicitSmoothSeed
