import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace ConnesWeilRH.Dev

open MeasureTheory
open scoped BigOperators

/--
Aggregate a finite partition of interval-integral upper bounds.

The cell bounds are explicit premises. This theorem does not treat external
JSON data as proofs; each row must separately supply an integral upper bound
for the same function and the same grid.
-/
theorem intervalIntegral_le_sum_cell_upper3198
    {function : ℝ → ℝ} {grid cellUpper : ℕ → ℝ} {left right : ℝ}
    {cells : ℕ}
    (hgrid_left : grid 0 = left)
    (hgrid_right : grid cells = right)
    (hinterval : ∀ index < cells,
      IntervalIntegrable function volume (grid index) (grid (index + 1)))
    (hcell : ∀ index < cells,
      (∫ position in grid index..grid (index + 1), function position) ≤
        cellUpper index) :
    (∫ position in left..right, function position) ≤
      Finset.sum (Finset.range cells) cellUpper := by
  have hsum_integral :
      (Finset.sum (Finset.range cells) fun index =>
          (∫ position in grid index..grid (index + 1), function position)) =
        ∫ position in grid 0..grid cells, function position := by
    exact intervalIntegral.sum_integral_adjacent_intervals (f := function)
      (μ := volume) (a := grid) (n := cells) hinterval
  have hsum_upper :
      (Finset.sum (Finset.range cells) fun index =>
          (∫ position in grid index..grid (index + 1), function position)) ≤
        Finset.sum (Finset.range cells) cellUpper := by
    exact Finset.sum_le_sum fun index hindex => hcell index
      (Finset.mem_range.mp hindex)
  rw [hgrid_left, hgrid_right] at hsum_integral
  rw [← hsum_integral]
  exact hsum_upper

end ConnesWeilRH.Dev
