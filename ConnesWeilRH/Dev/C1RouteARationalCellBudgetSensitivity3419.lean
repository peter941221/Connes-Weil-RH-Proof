import ConnesWeilRH.Dev.C1RouteARationalSignedCellUpper3415

namespace ConnesWeilRH.Dev

theorem record2680_cell1_second_budget_unit_cost3419 :
    (record2680Grid3212 2 - record2680Grid3212 1) ^ 3 / 24 >
      1 / 10 ^ 12 := by
  norm_num [record2680Grid3212, diagnosticRadius3201]

theorem record2680_cell1_second_budget_difference3419
    (secondUpperA secondUpperB : ℝ) :
    ((record2680Grid3212 2 - record2680Grid3212 1) *
        ratCellValueUpperTight3298 1 +
      (record2680Grid3212 2 - record2680Grid3212 1) ^ 3 * secondUpperA / 24 +
      (record2680Grid3212 2 - record2680Grid3212 1) ^ 5 *
        record2680CellFourthBound3224 1 / 1920 +
      (record2680Grid3212 2 - record2680Grid3212 1) ^ 7 *
        record2680UniformSixthBound3220 1 / 322560) -
      ((record2680Grid3212 2 - record2680Grid3212 1) *
        ratCellValueUpperTight3298 1 +
      (record2680Grid3212 2 - record2680Grid3212 1) ^ 3 * secondUpperB / 24 +
      (record2680Grid3212 2 - record2680Grid3212 1) ^ 5 *
        record2680CellFourthBound3224 1 / 1920 +
      (record2680Grid3212 2 - record2680Grid3212 1) ^ 7 *
        record2680UniformSixthBound3220 1 / 322560) =
      (record2680Grid3212 2 - record2680Grid3212 1) ^ 3 *
        (secondUpperA - secondUpperB) / 24 := by
  ring

end ConnesWeilRH.Dev
