import ConnesWeilRH.Dev.C1RouteARationalTightBlockConsumer3303
import ConnesWeilRH.Dev.C1RouteAConcreteOwner40960AggregateUpper3213

namespace ConnesWeilRH.Dev

open MeasureTheory
open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

/-
Record 3305 parameterizes the derivative rows at the block-consumer boundary.

The fixed 3224 rows are absolute-value family majorants and cannot consume the
3302 signed block manifest.  A future signed row provider can use this theorem
without changing the endpoint, owner, grid, or block index semantics.
-/

theorem intervalIntegral_record2680_40960_strict_upper_of_tight_signed_block_manifest3305
    {secondUpper fourthUpper sixthBound blockUpper : ℕ → ℝ}
    (hsecond : ∀ index < 40960,
      iteratedDeriv 2
        (weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
          capturedModulations2584) (record2680Center3212 index) ≤ secondUpper index)
    (hfourth : ∀ index < 40960,
      iteratedDeriv 4
        (weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
          capturedModulations2584) (record2680Center3212 index) ≤ fourthUpper index)
    (hderiv : ∀ index < 40960, ∀ coordinate,
      ‖iteratedDeriv 6
        (weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
          capturedModulations2584) coordinate‖ ≤ sixthBound index)
    (hsixthBound : ∀ index < 40960, 0 ≤ sixthBound index)
    (hblock : ∀ block < 160,
      Finset.sum (Finset.range 256) (fun offset =>
        record2680CellUpper3209 record2680Grid3212 ratCellValueUpperTight3298
          secondUpper fourthUpper sixthBound (block * 256 + offset)) ≤
        blockUpper block)
    (hsum : Finset.sum (Finset.range 160) blockUpper < 0) :
    (∫ position in (-diagnosticRadius3201)..diagnosticRadius3201,
      weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
        capturedModulations2584 position) < 0 := by
  have haggregate := intervalIntegral_record2680_40960_global_aggregate_upper3213
    (valueUpper := ratCellValueUpperTight3298)
    (secondUpper := secondUpper)
    (fourthUpper := fourthUpper)
    (sixthBound := sixthBound)
    (by
      intro index hindex
      exact ratCellValueUpperTight3298_spec hindex)
    hsecond hfourth hderiv hsixthBound
  have hdecomp := sum_range_mul_block_decomp3294
    (record2680CellUpper3209 record2680Grid3212 ratCellValueUpperTight3298
      secondUpper fourthUpper sixthBound) 160
  have hcount : 160 * 256 = 40960 := by norm_num
  have hsum_cells :
      Finset.sum (Finset.range 40960)
          (record2680CellUpper3209 record2680Grid3212 ratCellValueUpperTight3298
            secondUpper fourthUpper sixthBound) < 0 := by
    rw [hcount] at hdecomp
    calc
      Finset.sum (Finset.range 40960)
          (record2680CellUpper3209 record2680Grid3212 ratCellValueUpperTight3298
            secondUpper fourthUpper sixthBound) =
          Finset.sum (Finset.range 160) (fun block =>
            Finset.sum (Finset.range 256) (fun offset =>
              record2680CellUpper3209 record2680Grid3212 ratCellValueUpperTight3298
                secondUpper fourthUpper sixthBound (block * 256 + offset))) := hdecomp
      _ ≤ Finset.sum (Finset.range 160) blockUpper := by
        apply Finset.sum_le_sum
        intro block hmem
        exact hblock block (Finset.mem_range.mp hmem)
      _ < 0 := hsum
  exact lt_of_le_of_lt haggregate hsum_cells

end ConnesWeilRH.Dev
