import ConnesWeilRH.Dev.C1RouteARationalTightBlockManifest3302
import ConnesWeilRH.Dev.C1RouteARationalTightCell3298
import ConnesWeilRH.Dev.C1RouteAConcreteOwnerAggregateWithCellLocalJets3225
import ConnesWeilRH.Dev.C1RouteARationalBlockManifest3294

namespace ConnesWeilRH.Dev

open MeasureTheory
open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

/-
Record 3303 is the tight-endpoint consumer for the directed block manifest.

The older 3294 consumer is intentionally not reused as its endpoint premise
mentions ratCellValueUpper3289.  This module keeps the endpoint object aligned
with the 3298 tight proof and only imports the 3294 range decomposition.
-/

noncomputable def routeADirectedBlockUpper3302Real (block : ℕ) : ℝ :=
  if hblock : block < 160 then
    (routeADirectedBlockUpper3302 ⟨block, hblock⟩ : ℝ)
  else
    0

theorem routeADirectedBlockUpper3302Real_eq
    {block : ℕ} (hblock : block < 160) :
    routeADirectedBlockUpper3302Real block =
      (routeADirectedBlockUpper3302 ⟨block, hblock⟩ : ℝ) := by
  simp [routeADirectedBlockUpper3302Real, hblock]

theorem routeADirectedBlockUpper3302Real_sum_eq :
    Finset.sum (Finset.range 160) routeADirectedBlockUpper3302Real =
      ∑ block : Fin 160, (routeADirectedBlockUpper3302 block : ℝ) := by
  calc
    Finset.sum (Finset.range 160) routeADirectedBlockUpper3302Real =
        ∑ block : Fin 160, routeADirectedBlockUpper3302Real (block : ℕ) := by
          symm
          exact Fin.sum_univ_eq_sum_range routeADirectedBlockUpper3302Real 160
    _ = ∑ block : Fin 160, (routeADirectedBlockUpper3302 block : ℝ) := by
      apply Finset.sum_congr rfl
      intro block hmem
      exact routeADirectedBlockUpper3302Real_eq block.isLt

theorem routeADirectedBlockUpper3302Real_sum_lt_zero :
    Finset.sum (Finset.range 160) routeADirectedBlockUpper3302Real < 0 := by
  rw [routeADirectedBlockUpper3302Real_sum_eq]
  exact routeADirectedBlockUpper3302_real_sum_lt_zero

theorem intervalIntegral_record2680_40960_strict_upper_of_tight_block_manifest3303
    (hblock : ∀ block < 160,
      Finset.sum (Finset.range 256) (fun offset =>
        record2680CellUpper3209 record2680Grid3212 ratCellValueUpperTight3298
          record2680CellSecondBound3224 record2680CellFourthBound3224
          record2680UniformSixthBound3220 (block * 256 + offset)) ≤
        routeADirectedBlockUpper3302Real block) :
    (∫ position in (-diagnosticRadius3201)..diagnosticRadius3201,
      weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
        capturedModulations2584 position) < 0 := by
  have haggregate := intervalIntegral_record2680_40960_aggregate_upper_with_cell_local_jets3225
    (valueUpper := ratCellValueUpperTight3298)
    (by
      intro index hindex
      exact ratCellValueUpperTight3298_spec hindex)
  have hdecomp := sum_range_mul_block_decomp3294
    (record2680CellUpper3209 record2680Grid3212 ratCellValueUpperTight3298
      record2680CellSecondBound3224 record2680CellFourthBound3224
      record2680UniformSixthBound3220) 160
  have hcount : 160 * 256 = 40960 := by norm_num
  have hsum :
      Finset.sum (Finset.range 40960)
          (record2680CellUpper3209 record2680Grid3212 ratCellValueUpperTight3298
            record2680CellSecondBound3224 record2680CellFourthBound3224
            record2680UniformSixthBound3220) < 0 := by
    rw [hcount] at hdecomp
    calc
      Finset.sum (Finset.range 40960)
          (record2680CellUpper3209 record2680Grid3212 ratCellValueUpperTight3298
            record2680CellSecondBound3224 record2680CellFourthBound3224
            record2680UniformSixthBound3220) =
          Finset.sum (Finset.range 160) (fun block =>
            Finset.sum (Finset.range 256) (fun offset =>
              record2680CellUpper3209 record2680Grid3212 ratCellValueUpperTight3298
                record2680CellSecondBound3224 record2680CellFourthBound3224
                record2680UniformSixthBound3220 (block * 256 + offset))) := hdecomp
      _ ≤ Finset.sum (Finset.range 160) routeADirectedBlockUpper3302Real := by
        apply Finset.sum_le_sum
        intro block hmem
        exact hblock block (Finset.mem_range.mp hmem)
      _ < 0 := routeADirectedBlockUpper3302Real_sum_lt_zero
  exact lt_of_le_of_lt haggregate hsum

end ConnesWeilRH.Dev
