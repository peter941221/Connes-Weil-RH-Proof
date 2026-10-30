import ConnesWeilRH.Dev.C1RouteAConcreteOwnerCellUpper3208
import ConnesWeilRH.Dev.C1RouteACellUpperCertificate3198

namespace ConnesWeilRH.Dev

open MeasureTheory
open scoped BigOperators

noncomputable def record2680CellUpper3209
    (grid valueUpper secondUpper fourthUpper sixthBound : ℕ → ℝ)
    (index : ℕ) : ℝ :=
  (grid (index + 1) - grid index) * valueUpper index +
    (grid (index + 1) - grid index) ^ 3 * secondUpper index / 24 +
    (grid (index + 1) - grid index) ^ 5 * fourthUpper index / 1920 +
    (grid (index + 1) - grid index) ^ 7 * sixthBound index / 322560

theorem intervalIntegral_record2680_aggregate_upper3209
    {grid valueUpper secondUpper fourthUpper sixthBound center : ℕ → ℝ}
    {left right : ℝ} {cells : ℕ}
    (hgrid_left : grid 0 = left)
    (hgrid_right : grid cells = right)
    (horder : ∀ index < cells, grid index < grid (index + 1))
    (hcenter : ∀ index < cells,
      center index = (grid index + grid (index + 1)) / 2)
    (hvalue : ∀ index < cells,
      weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
        capturedModulations2584 (center index) ≤ valueUpper index)
    (hsecond : ∀ index < cells,
      iteratedDerivWithin 2
        (weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
          capturedModulations2584) (Set.Icc (grid index) (grid (index + 1)))
        (center index) ≤ secondUpper index)
    (hfourth : ∀ index < cells,
      iteratedDerivWithin 4
        (weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
          capturedModulations2584) (Set.Icc (grid index) (grid (index + 1)))
        (center index) ≤ fourthUpper index)
    (hderiv : ∀ index < cells, ∀ coordinate,
      ‖iteratedDeriv 6
        (weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
          capturedModulations2584) coordinate‖ ≤ sixthBound index)
    (hsixthBound : ∀ index < cells, 0 ≤ sixthBound index) :
    (∫ position in left..right,
      weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
        capturedModulations2584 position) ≤
      Finset.sum (Finset.range cells)
        (record2680CellUpper3209 grid valueUpper secondUpper fourthUpper
          sixthBound) := by
  apply intervalIntegral_le_sum_cell_upper3198 hgrid_left hgrid_right
  · intro index hindex
    exact weightedExternal3201_intervalIntegrable (-1 / 2)
      record2680CorrectionCoefficient capturedModulations2584
      (grid index) (grid (index + 1))
  · intro index hindex
    exact intervalIntegral_record2680_cell_upper3208
      (horder index hindex) (hcenter index hindex) (hvalue index hindex)
      (hsecond index hindex) (hfourth index hindex)
      (hderiv index hindex) (hsixthBound index hindex)

end ConnesWeilRH.Dev
