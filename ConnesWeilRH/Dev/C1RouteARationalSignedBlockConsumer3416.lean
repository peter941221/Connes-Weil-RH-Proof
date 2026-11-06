import ConnesWeilRH.Dev.C1RouteARationalSignedCellUpper3415
import ConnesWeilRH.Dev.C1RouteARationalBlockManifest3294

namespace ConnesWeilRH.Dev

open scoped BigOperators

noncomputable def record2680CellUpperSignedAt3416
    (familyUpper : Fin 30 → ℝ) (index : ℕ) : ℝ :=
  if index = 1 then
    record2680CellUpperSigned3415 familyUpper
  else
    record2680CellUpper3209 record2680Grid3212 ratCellValueUpperTight3298
      record2680CellSecondBound3224 record2680CellFourthBound3224
      record2680UniformSixthBound3220 index

theorem record2680CellUpperSignedAt3416_eq_old_of_ne_one
    (familyUpper : Fin 30 → ℝ) {index : ℕ} (hindex : index ≠ 1) :
    record2680CellUpperSignedAt3416 familyUpper index =
      record2680CellUpper3209 record2680Grid3212 ratCellValueUpperTight3298
        record2680CellSecondBound3224 record2680CellFourthBound3224
        record2680UniformSixthBound3220 index := by
  simp [record2680CellUpperSignedAt3416, hindex]

theorem record2680CellUpperSignedAt3416_sum_le_old
    (familyUpper : Fin 30 → ℝ)
    (hcell : record2680CellUpperSigned3415 familyUpper ≤
      record2680CellUpper3209 record2680Grid3212 ratCellValueUpperTight3298
        record2680CellSecondBound3224 record2680CellFourthBound3224
        record2680UniformSixthBound3220 1) :
    ∀ block : ℕ,
      Finset.sum (Finset.range 256) (fun offset =>
        record2680CellUpperSignedAt3416 familyUpper (block * 256 + offset)) ≤
      Finset.sum (Finset.range 256) (fun offset =>
        record2680CellUpper3209 record2680Grid3212 ratCellValueUpperTight3298
          record2680CellSecondBound3224 record2680CellFourthBound3224
          record2680UniformSixthBound3220 (block * 256 + offset)) := by
  intro block
  apply Finset.sum_le_sum
  intro offset hoff
  by_cases hindex : block * 256 + offset = 1
  · simpa [record2680CellUpperSignedAt3416, hindex] using hcell
  · rw [record2680CellUpperSignedAt3416_eq_old_of_ne_one familyUpper hindex]

theorem record2680_signed_block_upper3416_of_old_block_certificate
    (familyUpper : Fin 30 → ℝ)
    (hcell : record2680CellUpperSigned3415 familyUpper ≤
      record2680CellUpper3209 record2680Grid3212 ratCellValueUpperTight3298
        record2680CellSecondBound3224 record2680CellFourthBound3224
        record2680UniformSixthBound3220 1)
    {blockUpper : ℕ → ℝ}
    (hblock : ∀ block < 160,
      Finset.sum (Finset.range 256) (fun offset =>
        record2680CellUpper3209 record2680Grid3212 ratCellValueUpperTight3298
          record2680CellSecondBound3224 record2680CellFourthBound3224
          record2680UniformSixthBound3220 (block * 256 + offset)) ≤
        blockUpper block) :
    ∀ block < 160,
      Finset.sum (Finset.range 256) (fun offset =>
        record2680CellUpperSignedAt3416 familyUpper (block * 256 + offset)) ≤
      blockUpper block := by
  intro block hblock_index
  exact (record2680CellUpperSignedAt3416_sum_le_old familyUpper hcell block).trans
    (hblock block hblock_index)

end ConnesWeilRH.Dev
