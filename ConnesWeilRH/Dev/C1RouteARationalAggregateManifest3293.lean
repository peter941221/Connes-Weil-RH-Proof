import ConnesWeilRH.Dev.C1RouteARational40960Aggregate3290

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

theorem intervalIntegral_record2680_40960_strict_upper_of_manifest3293
    {endpoint : ℕ → ℝ}
    (hendpoint : ∀ index < 40960,
      ratCellValueUpper3289 index ≤ endpoint index)
    (hsum :
      Finset.sum (Finset.range 40960)
        (record2680CellUpper3209 record2680Grid3212 endpoint
          record2680CellSecondBound3224 record2680CellFourthBound3224
          record2680UniformSixthBound3220) < 0) :
    (∫ position in (-diagnosticRadius3201)..diagnosticRadius3201,
      weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
        capturedModulations2584 position) < 0 := by
  have haggregate := intervalIntegral_record2680_40960_rational_aggregate_upper3290
  have hsum_le :
      Finset.sum (Finset.range 40960)
          (record2680CellUpper3209 record2680Grid3212 ratCellValueUpper3289
            record2680CellSecondBound3224 record2680CellFourthBound3224
            record2680UniformSixthBound3220) ≤
        Finset.sum (Finset.range 40960)
          (record2680CellUpper3209 record2680Grid3212 endpoint
            record2680CellSecondBound3224 record2680CellFourthBound3224
            record2680UniformSixthBound3220) := by
    apply Finset.sum_le_sum
    intro index hindex
    have hi : index < 40960 := Finset.mem_range.mp hindex
    have hstep : 0 ≤ record2680Grid3212 (index + 1) -
        record2680Grid3212 index := by
      linarith [record2680_grid_order3212 hi]
    have hmul := mul_le_mul_of_nonneg_left
      (hendpoint index hi) hstep
    unfold record2680CellUpper3209
    nlinarith
  exact lt_of_le_of_lt (haggregate.trans hsum_le) hsum

end ConnesWeilRH.Dev
