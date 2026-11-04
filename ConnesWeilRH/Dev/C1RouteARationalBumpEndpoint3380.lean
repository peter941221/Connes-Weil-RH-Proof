import ConnesWeilRH.Dev.C1RouteARationalSignedFamily3332
import ConnesWeilRH.Dev.C1RouteARationalTaylorEndpoint3346
import ConnesWeilRH.Dev.C1RouteARationalBumpEndpoint3347

namespace ConnesWeilRH.Dev

theorem signed_bump_selector3380_cell1_family4 :
    let radius := storedWidthRat3287 4 ^ 2
    let position := |record2680CenterRat3279 1|
    let t := ratBumpT3286 radius position
    |t / 8| > (1 : ℚ) ∧ t < (-64 : ℚ) := by
  norm_num [ratBumpT3286, record2680CenterRat3279,
    storedWidthRat3287, Matrix.cons_val_four]

theorem signed_bump_tail_selector3380_cell1_family4 :
    ratTailBumpInterval3298
        (ratBumpT3286 (storedWidthRat3287 4 ^ 2)
          |record2680CenterRat3279 1|) =
      { lo := 0
        hi := (RatInterval3276.powNat ratBaseInterval3284 188).hi } := by
  have h := signed_bump_selector3380_cell1_family4
  dsimp at h
  have hsmall :
      ¬ |ratBumpT3286 (storedWidthRat3287 4 ^ 2)
          |record2680CenterRat3279 1| / 8| ≤ (1 : ℚ) := by
    exact not_le_of_gt h.1
  have h16 :
      ¬ (-16 : ℚ) ≤
        ratBumpT3286 (storedWidthRat3287 4 ^ 2)
          |record2680CenterRat3279 1| := by
    linarith [h.2]
  have h32 :
      ¬ (-32 : ℚ) ≤
        ratBumpT3286 (storedWidthRat3287 4 ^ 2)
          |record2680CenterRat3279 1| := by
    linarith [h.2]
  have h64 :
      ¬ (-64 : ℚ) ≤
        ratBumpT3286 (storedWidthRat3287 4 ^ 2)
          |record2680CenterRat3279 1| := by
    exact not_le_of_gt h.2
  simp only [ratTailBumpInterval3298, if_neg hsmall, if_neg h16,
    if_neg h32, if_neg h64]

theorem signed_bump_endpoint3380_cell1_order2_family4_reLo_eq_zero :
    (ratBumpJetInterval3310 2 (storedWidthRat3287 4 ^ 2)
      (record2680CenterRat3279 1)).lo = 0 := by
  have hsel := signed_bump_tail_selector3380_cell1_family4
  have hfactor :
      0 ≤
        (1 - (record2680CenterRat3279 1 /
          (storedWidthRat3287 4 ^ 2)) ^ 2)⁻¹ ^ (2 * 2) *
          ratBumpNumerator3310 2
            (record2680CenterRat3279 1 /
              (storedWidthRat3287 4 ^ 2)) /
          (storedWidthRat3287 4 ^ 2) ^ 2 := by
    norm_num [ratBumpNumerator3310, record2680CenterRat3279,
      storedWidthRat3287, Matrix.cons_val_four]
  have hbaseHi : 0 ≤ (RatInterval3276.powNat ratBaseInterval3284 188).hi :=
    ratBaseInterval3284_powNat_hi_nonneg3344 188
  unfold ratBumpJetInterval3310
  rw [if_pos]
  · rw [hsel]
    dsimp [RatInterval3276.mul]
    apply le_antisymm
    · norm_num
    · apply le_min
      · apply le_min <;> norm_num
      · apply le_min <;> exact mul_nonneg hbaseHi hfactor
  · norm_num [record2680CenterRat3279, storedWidthRat3287,
      Matrix.cons_val_four]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem signed_bump_endpoint3380_cell1_order2_family4_hi_eq :
    (ratBumpJetInterval3310 2 (storedWidthRat3287 4 ^ 2)
      (record2680CenterRat3279 1)).hi =
      (RatInterval3276.powNat ratBaseInterval3284 188).hi *
        ((1 - (record2680CenterRat3279 1 /
          (storedWidthRat3287 4 ^ 2)) ^ 2)⁻¹ ^ (2 * 2) *
          ratBumpNumerator3310 2
            (record2680CenterRat3279 1 /
              (storedWidthRat3287 4 ^ 2)) /
          (storedWidthRat3287 4 ^ 2) ^ 2) := by
  have hsel := signed_bump_tail_selector3380_cell1_family4
  have hfactor :
      0 ≤
        (1 - (record2680CenterRat3279 1 /
          (storedWidthRat3287 4 ^ 2)) ^ 2)⁻¹ ^ (2 * 2) *
          ratBumpNumerator3310 2
            (record2680CenterRat3279 1 /
              (storedWidthRat3287 4 ^ 2)) /
          (storedWidthRat3287 4 ^ 2) ^ 2 := by
    norm_num [ratBumpNumerator3310, record2680CenterRat3279,
      storedWidthRat3287, Matrix.cons_val_four]
  have hbaseHi : 0 ≤ (RatInterval3276.powNat ratBaseInterval3284 188).hi :=
    ratBaseInterval3284_powNat_hi_nonneg3344 188
  unfold ratBumpJetInterval3310
  rw [if_pos]
  · rw [hsel]
    dsimp
    have hmul := ratInterval_mul_hi_eq_hi_mul_of_zero_lo_nonneg3347
      ({lo := 0, hi := _} : RatInterval3276)
      ({lo := _, hi := _} : RatInterval3276)
      rfl hbaseHi hfactor hfactor (by norm_num)
    simpa [RatInterval3276.mul, ratBumpNumerator3310] using hmul
  · norm_num [record2680CenterRat3279, storedWidthRat3287,
      Matrix.cons_val_four]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem signed_bump_endpoint3380_cell1_order2_family4_hi_le :
    (ratBumpJetInterval3310 2 (storedWidthRat3287 4 ^ 2)
      (record2680CenterRat3279 1)).hi ≤ 1 / 10 ^ 16 := by
  rw [signed_bump_endpoint3380_cell1_order2_family4_hi_eq]
  rw [ratBaseInterval3284_powNat_hi_eq_pow3346]
  norm_num (config := { maxSteps := 2000000000 }) [
    ratBaseInterval3284,
    ratTaylorInterval3283,
    ratTaylorSum3283,
    ratTaylorError3283,
    storedWidthRat3287,
    record2680CenterRat3279,
    ratBumpNumerator3310,
    Matrix.cons_val_four]

end ConnesWeilRH.Dev
