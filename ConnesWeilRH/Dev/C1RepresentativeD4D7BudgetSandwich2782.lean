import ConnesWeilRH.Dev.C1RepresentativeD4D7RationalBudget2762
import ConnesWeilRH.Dev.C1RepresentativeD4D7BudgetRhsNonneg2780

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed

theorem representativeD4D7Budget_sandwich2782 :
    0 ≤
        (∫ x in leftCell2740.lo..leftCell2740.hi,
          ‖iteratedDeriv 4 Real.smoothTransition x‖) +
        (∫ x in rightCell2740.lo..rightCell2740.hi,
          ‖iteratedDeriv 4 Real.smoothTransition x‖) ∧
      (∫ x in leftCell2740.lo..leftCell2740.hi,
        ‖iteratedDeriv 4 Real.smoothTransition x‖) +
        (∫ x in rightCell2740.lo..rightCell2740.hi,
          ‖iteratedDeriv 4 Real.smoothTransition x‖) ≤
        ((2047 : ℝ) / 33554432) * representativeD4Box2755.endpointAbsMax ∧
    0 ≤
        (∫ x in leftCell2740.lo..leftCell2740.hi,
          ‖iteratedDeriv 7 Real.smoothTransition x‖) +
        (∫ x in rightCell2740.lo..rightCell2740.hi,
          ‖iteratedDeriv 7 Real.smoothTransition x‖) ∧
      (∫ x in leftCell2740.lo..leftCell2740.hi,
        ‖iteratedDeriv 7 Real.smoothTransition x‖) +
        (∫ x in rightCell2740.lo..rightCell2740.hi,
          ‖iteratedDeriv 7 Real.smoothTransition x‖) ≤
        ((2047 : ℝ) / 33554432) * representativeD7Box2755.endpointAbsMax := by
  have h := representativeD4D7RationalBudget2762
  have h4l : 0 ≤ ∫ x in leftCell2740.lo..leftCell2740.hi,
      ‖iteratedDeriv 4 Real.smoothTransition x‖ :=
    intervalIntegral.integral_nonneg (by norm_num [leftCell2740, representativeCell2736])
      (fun _ _ => norm_nonneg _)
  have h4r : 0 ≤ ∫ x in rightCell2740.lo..rightCell2740.hi,
      ‖iteratedDeriv 4 Real.smoothTransition x‖ :=
    intervalIntegral.integral_nonneg (by norm_num [rightCell2740, representativeCell2736])
      (fun _ _ => norm_nonneg _)
  have h7l : 0 ≤ ∫ x in leftCell2740.lo..leftCell2740.hi,
      ‖iteratedDeriv 7 Real.smoothTransition x‖ :=
    intervalIntegral.integral_nonneg (by norm_num [leftCell2740, representativeCell2736])
      (fun _ _ => norm_nonneg _)
  have h7r : 0 ≤ ∫ x in rightCell2740.lo..rightCell2740.hi,
      ‖iteratedDeriv 7 Real.smoothTransition x‖ :=
    intervalIntegral.integral_nonneg (by norm_num [rightCell2740, representativeCell2736])
      (fun _ _ => norm_nonneg _)
  exact ⟨add_nonneg h4l h4r, h.1, add_nonneg h7l h7r, h.2⟩

end ConnesWeilRH.Source.C1ExplicitSmoothSeed
