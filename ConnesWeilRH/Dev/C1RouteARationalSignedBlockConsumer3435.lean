import ConnesWeilRH.Dev.C1RouteARationalSignedCellAggregate3433
import ConnesWeilRH.Dev.C1RouteARationalBlockManifest3294

namespace ConnesWeilRH.Dev

open scoped BigOperators

noncomputable def record2680CellUpperSignedAt3435
    (index : ℕ) : ℝ :=
  if index = 1 then
    record2680CellUpperSigned3433
  else
    record2680CellUpper3209 record2680Grid3212 ratCellValueUpperTight3298
      record2680CellSecondBound3224 record2680CellFourthBound3224
      record2680UniformSixthBound3220 index

theorem record2680CellUpperSignedAt3435_eq_old_of_ne_one
    {index : ℕ} (hindex : index ≠ 1) :
    record2680CellUpperSignedAt3435 index =
      record2680CellUpper3209 record2680Grid3212 ratCellValueUpperTight3298
        record2680CellSecondBound3224 record2680CellFourthBound3224
        record2680UniformSixthBound3220 index := by
  simp [record2680CellUpperSignedAt3435, hindex]

theorem record2680_signed_block_upper3435_of_new_block0_certificate
    {blockUpper : ℕ → ℝ}
    (hblock0 :
      Finset.sum (Finset.range 256) (fun offset =>
        record2680CellUpperSignedAt3435 offset) ≤
      blockUpper 0)
    (hblock_old : ∀ block, 0 < block → block < 160 →
      Finset.sum (Finset.range 256) (fun offset =>
        record2680CellUpper3209 record2680Grid3212 ratCellValueUpperTight3298
          record2680CellSecondBound3224 record2680CellFourthBound3224
          record2680UniformSixthBound3220 (block * 256 + offset)) ≤
      blockUpper block) :
    ∀ block < 160,
      Finset.sum (Finset.range 256) (fun offset =>
        record2680CellUpperSignedAt3435 (block * 256 + offset)) ≤
      blockUpper block := by
  intro block hblock_index
  by_cases hzero : block = 0
  · simpa [hzero] using hblock0
  · have hpositive : 0 < block := Nat.pos_of_ne_zero hzero
    have hsum :
        Finset.sum (Finset.range 256) (fun offset =>
          record2680CellUpperSignedAt3435 (block * 256 + offset)) =
        Finset.sum (Finset.range 256) (fun offset =>
          record2680CellUpper3209 record2680Grid3212 ratCellValueUpperTight3298
            record2680CellSecondBound3224 record2680CellFourthBound3224
            record2680UniformSixthBound3220 (block * 256 + offset)) := by
      apply Finset.sum_congr rfl
      intro offset hoffset
      have hindex : block * 256 + offset ≠ 1 := by
        omega
      exact record2680CellUpperSignedAt3435_eq_old_of_ne_one hindex
    rw [hsum]
    exact hblock_old block hpositive hblock_index

end ConnesWeilRH.Dev
