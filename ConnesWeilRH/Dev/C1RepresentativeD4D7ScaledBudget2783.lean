import ConnesWeilRH.Dev.C1RepresentativeD4D7BudgetSandwich2782

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed

theorem representativeD4D7_scaled_budget2783
    {c4 c7 : ℝ} (hc4 : 0 ≤ c4) (hc7 : 0 ≤ c7) :
    c4 *
        ((∫ x in leftCell2740.lo..leftCell2740.hi,
          ‖iteratedDeriv 4 Real.smoothTransition x‖) +
        (∫ x in rightCell2740.lo..rightCell2740.hi,
          ‖iteratedDeriv 4 Real.smoothTransition x‖)) +
      c7 *
        ((∫ x in leftCell2740.lo..leftCell2740.hi,
          ‖iteratedDeriv 7 Real.smoothTransition x‖) +
        (∫ x in rightCell2740.lo..rightCell2740.hi,
          ‖iteratedDeriv 7 Real.smoothTransition x‖)) ≤
    c4 * (((2047 : ℝ) / 33554432) * representativeD4Box2755.endpointAbsMax) +
      c7 * (((2047 : ℝ) / 33554432) * representativeD7Box2755.endpointAbsMax) := by
  have h := representativeD4D7Budget_sandwich2782
  exact add_le_add
    (mul_le_mul_of_nonneg_left h.2.1 hc4)
    (mul_le_mul_of_nonneg_left h.2.2.2 hc7)

end ConnesWeilRH.Source.C1ExplicitSmoothSeed
