import ConnesWeilRH.Dev.C1RouteARationalAggregateManifest3293

namespace ConnesWeilRH.Dev

open MeasureTheory
open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

noncomputable def routeABlockCellUpper3294 (endpoint : ℕ → ℝ) (block : ℕ) : ℝ :=
  Finset.sum (Finset.range 256) (fun offset =>
    record2680CellUpper3209 record2680Grid3212 endpoint
      record2680CellSecondBound3224 record2680CellFourthBound3224
      record2680UniformSixthBound3220 (block * 256 + offset))

lemma sum_range_mul_block_decomp3294 {α : Type*} [AddCommMonoid α]
    (f : ℕ → α) (blockCount : ℕ) :
    Finset.sum (Finset.range (blockCount * 256)) f =
      Finset.sum (Finset.range blockCount) (fun block =>
        Finset.sum (Finset.range 256) (fun offset => f (block * 256 + offset))) := by
  induction blockCount with
  | zero => simp
  | succ block ih =>
      calc
        Finset.sum (Finset.range ((block + 1) * 256)) f =
            Finset.sum (Finset.range (block * 256)) f +
              Finset.sum (Finset.range 256) (fun offset => f (block * 256 + offset)) := by
                rw [Nat.succ_mul, Finset.sum_range_add]
        _ = Finset.sum (Finset.range block) (fun oldBlock =>
              Finset.sum (Finset.range 256) (fun offset => f (oldBlock * 256 + offset))) +
              Finset.sum (Finset.range 256) (fun offset => f (block * 256 + offset)) := by
                rw [ih]
        _ = Finset.sum (Finset.range (block + 1)) (fun newBlock =>
              Finset.sum (Finset.range 256) (fun offset => f (newBlock * 256 + offset))) := by
                rw [Finset.sum_range_succ
                  (fun newBlock => Finset.sum (Finset.range 256)
                    (fun offset => f (newBlock * 256 + offset))) block]

theorem intervalIntegral_record2680_40960_strict_upper_of_block_manifest3294
    {endpoint blockUpper : ℕ → ℝ}
    (hendpoint : ∀ index < 40960,
      ratCellValueUpper3289 index ≤ endpoint index)
    (hblock : ∀ block < 160,
      Finset.sum (Finset.range 256) (fun offset =>
        record2680CellUpper3209 record2680Grid3212 endpoint
          record2680CellSecondBound3224 record2680CellFourthBound3224
          record2680UniformSixthBound3220 (block * 256 + offset)) ≤
        blockUpper block)
    (hsum : Finset.sum (Finset.range 160) blockUpper < 0) :
    (∫ position in (-diagnosticRadius3201)..diagnosticRadius3201,
      weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
        capturedModulations2584 position) < 0 := by
  have haggregate := intervalIntegral_record2680_40960_strict_upper_of_manifest3293
    (endpoint := endpoint) hendpoint
      (hsum := by
        have hdecomp := sum_range_mul_block_decomp3294
          (record2680CellUpper3209 record2680Grid3212 endpoint
            record2680CellSecondBound3224 record2680CellFourthBound3224
            record2680UniformSixthBound3220) 160
        have hcount : 160 * 256 = 40960 := by norm_num
        rw [hcount] at hdecomp
        calc
          Finset.sum (Finset.range 40960)
              (record2680CellUpper3209 record2680Grid3212 endpoint
                record2680CellSecondBound3224 record2680CellFourthBound3224
                record2680UniformSixthBound3220) =
              Finset.sum (Finset.range 160) (fun block =>
                Finset.sum (Finset.range 256) (fun offset =>
                  record2680CellUpper3209 record2680Grid3212 endpoint
                    record2680CellSecondBound3224 record2680CellFourthBound3224
                    record2680UniformSixthBound3220 (block * 256 + offset))) := hdecomp
          _ ≤ Finset.sum (Finset.range 160) blockUpper := by
            apply Finset.sum_le_sum
            intro block hmem
            exact hblock block (Finset.mem_range.mp hmem)
          _ < 0 := hsum)
  exact haggregate

end ConnesWeilRH.Dev
