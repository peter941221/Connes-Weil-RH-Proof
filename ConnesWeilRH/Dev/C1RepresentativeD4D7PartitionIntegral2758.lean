import ConnesWeilRH.Dev.C1RepresentativeD4D7CellIntegral2757

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed

open MeasureTheory
noncomputable section

theorem representativeD4D7Partition_integral_add2758 :
    (∫ x in representativeCell2736.lo..representativeCell2736.hi,
      ‖iteratedDeriv 4 Real.smoothTransition x‖) =
      (∫ x in leftCell2740.lo..leftCell2740.hi,
        ‖iteratedDeriv 4 Real.smoothTransition x‖) +
      (∫ x in rightCell2740.lo..rightCell2740.hi,
        ‖iteratedDeriv 4 Real.smoothTransition x‖) ∧
    (∫ x in representativeCell2736.lo..representativeCell2736.hi,
      ‖iteratedDeriv 7 Real.smoothTransition x‖) =
      (∫ x in leftCell2740.lo..leftCell2740.hi,
        ‖iteratedDeriv 7 Real.smoothTransition x‖) +
      (∫ x in rightCell2740.lo..rightCell2740.hi,
        ‖iteratedDeriv 7 Real.smoothTransition x‖) := by
  have hmid : leftCell2740.hi = rightCell2740.lo := by rfl
  have hleft (n : ℕ) : IntervalIntegrable
      (fun x : ℝ => ‖iteratedDeriv n Real.smoothTransition x‖) volume
      leftCell2740.lo leftCell2740.hi :=
    (continuous_norm.comp (contDiff_one_iteratedDeriv_smoothTransition n).continuous).intervalIntegrable _ _
  have hright (n : ℕ) : IntervalIntegrable
      (fun x : ℝ => ‖iteratedDeriv n Real.smoothTransition x‖) volume
      rightCell2740.lo rightCell2740.hi :=
    (continuous_norm.comp (contDiff_one_iteratedDeriv_smoothTransition n).continuous).intervalIntegrable _ _
  constructor
  · have h := intervalIntegral.integral_add_adjacent_intervals
      (f := fun x : ℝ => ‖iteratedDeriv 4 Real.smoothTransition x‖)
      (μ := volume) (a := leftCell2740.lo) (b := leftCell2740.hi)
      (c := rightCell2740.hi) (hleft 4) (hright 4)
    simpa [leftCell2740, rightCell2740, representativeCell2736] using h.symm
  · have h := intervalIntegral.integral_add_adjacent_intervals
      (f := fun x : ℝ => ‖iteratedDeriv 7 Real.smoothTransition x‖)
      (μ := volume) (a := leftCell2740.lo) (b := leftCell2740.hi)
      (c := rightCell2740.hi) (hleft 7) (hright 7)
    simpa [leftCell2740, rightCell2740, representativeCell2736] using h.symm

end
end ConnesWeilRH.Source.C1ExplicitSmoothSeed
