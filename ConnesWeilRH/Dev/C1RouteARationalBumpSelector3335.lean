import ConnesWeilRH.Dev.C1RouteARationalSignedFamily3332

namespace ConnesWeilRH.Dev

theorem signed_bump_selector3335_cell0_family4 :
    let radius := storedWidthRat3287 4 ^ 2
    let position := |record2680CenterRat3279 0|
    let t := ratBumpT3286 radius position
    |t / 8| > (1 : ℚ) ∧ t < (-64 : ℚ) := by
  norm_num [ratBumpT3286, record2680CenterRat3279,
    storedWidthRat3287, Matrix.cons_val_four]

theorem signed_bump_tail_selector3335_cell0_family4 :
    ratTailBumpInterval3298
        (ratBumpT3286 (storedWidthRat3287 4 ^ 2)
          |record2680CenterRat3279 0|) =
      { lo := 0
        hi := (RatInterval3276.powNat ratBaseInterval3284 188).hi } := by
  have h := signed_bump_selector3335_cell0_family4
  dsimp at h
  have hsmall :
      ¬ |ratBumpT3286 (storedWidthRat3287 4 ^ 2)
          |record2680CenterRat3279 0| / 8| ≤ (1 : ℚ) := by
    exact not_le_of_gt h.1
  have h16 :
      ¬ (-16 : ℚ) ≤
        ratBumpT3286 (storedWidthRat3287 4 ^ 2)
          |record2680CenterRat3279 0| := by
    linarith [h.2]
  have h32 :
      ¬ (-32 : ℚ) ≤
        ratBumpT3286 (storedWidthRat3287 4 ^ 2)
          |record2680CenterRat3279 0| := by
    linarith [h.2]
  have h64 :
      ¬ (-64 : ℚ) ≤
        ratBumpT3286 (storedWidthRat3287 4 ^ 2)
          |record2680CenterRat3279 0| := by
    exact not_le_of_gt h.2
  simp only [ratTailBumpInterval3298, if_neg hsmall, if_neg h16,
    if_neg h32, if_neg h64]

end ConnesWeilRH.Dev
