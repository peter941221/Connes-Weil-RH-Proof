import ConnesWeilRH.Dev.C1RouteARationalBumpEndpoint3380
import ConnesWeilRH.Dev.C1RouteARationalTaylorEndpoint3344

namespace ConnesWeilRH.Dev

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem signed_bump_endpoint3382_cell1_order1_family4_reLo_eq_zero :
    (ratBumpJetInterval3310 1 (storedWidthRat3287 4 ^ 2)
      (record2680CenterRat3279 1)).lo = 0 := by
  have hsel := signed_bump_tail_selector3380_cell1_family4
  have hfactor :
      0 ≤
        (1 - (record2680CenterRat3279 1 /
          (storedWidthRat3287 4 ^ 2)) ^ 2)⁻¹ ^ (2 * 1) *
          ratBumpNumerator3310 1
            (record2680CenterRat3279 1 /
              (storedWidthRat3287 4 ^ 2)) /
          (storedWidthRat3287 4 ^ 2) ^ 1 := by
    norm_num [ratBumpNumerator3310, record2680CenterRat3279,
      storedWidthRat3287, Matrix.cons_val_four]
  have hbaseHi : 0 ≤ (RatInterval3276.powNat ratBaseInterval3284 188).hi :=
    ratBaseInterval3284_powNat_hi_nonneg3344 188
  unfold ratBumpJetInterval3310
  rw [if_pos]
  · rw [hsel]
    dsimp [RatInterval3276.mul]
    have hprod :
        0 ≤ (RatInterval3276.powNat ratBaseInterval3284 188).hi *
          ((1 - (record2680CenterRat3279 1 /
            (storedWidthRat3287 4 ^ 2)) ^ 2)⁻¹ ^ (2 * 1) *
            ratBumpNumerator3310 1
              (record2680CenterRat3279 1 /
                (storedWidthRat3287 4 ^ 2)) /
            (storedWidthRat3287 4 ^ 2) ^ 1) :=
      mul_nonneg hbaseHi hfactor
    apply le_antisymm
    · simp only [zero_mul, min_self]
      rw [min_eq_left hprod]
    · simp only [zero_mul, min_self]
      rw [min_eq_left hprod]
  · norm_num [record2680CenterRat3279, storedWidthRat3287,
      Matrix.cons_val_four]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem signed_bump_endpoint3382_cell1_order1_family4_hi_eq :
    (ratBumpJetInterval3310 1 (storedWidthRat3287 4 ^ 2)
      (record2680CenterRat3279 1)).hi =
      (RatInterval3276.powNat ratBaseInterval3284 188).hi *
        ((1 - (record2680CenterRat3279 1 /
          (storedWidthRat3287 4 ^ 2)) ^ 2)⁻¹ ^ (2 * 1) *
          ratBumpNumerator3310 1
            (record2680CenterRat3279 1 /
              (storedWidthRat3287 4 ^ 2)) /
          (storedWidthRat3287 4 ^ 2) ^ 1) := by
  have hsel := signed_bump_tail_selector3380_cell1_family4
  have hfactor :
      0 ≤
        (1 - (record2680CenterRat3279 1 /
          (storedWidthRat3287 4 ^ 2)) ^ 2)⁻¹ ^ (2 * 1) *
          ratBumpNumerator3310 1
            (record2680CenterRat3279 1 /
              (storedWidthRat3287 4 ^ 2)) /
          (storedWidthRat3287 4 ^ 2) ^ 1 := by
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
      rfl hbaseHi hfactor hfactor le_rfl
    simpa [RatInterval3276.mul] using hmul
  · norm_num [record2680CenterRat3279, storedWidthRat3287,
      Matrix.cons_val_four]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem signed_bump_endpoint3382_cell1_order0_family4_reLo_eq_zero :
    (ratBumpJetInterval3310 0 (storedWidthRat3287 4 ^ 2)
      (record2680CenterRat3279 1)).lo = 0 := by
  have hsel := signed_bump_tail_selector3380_cell1_family4
  have hfactor :
      0 ≤
        (1 - (record2680CenterRat3279 1 /
          (storedWidthRat3287 4 ^ 2)) ^ 2)⁻¹ ^ (2 * 0) *
          ratBumpNumerator3310 0
            (record2680CenterRat3279 1 /
              (storedWidthRat3287 4 ^ 2)) /
          (storedWidthRat3287 4 ^ 2) ^ 0 := by
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
theorem signed_bump_endpoint3382_cell1_order0_family4_hi_eq :
    (ratBumpJetInterval3310 0 (storedWidthRat3287 4 ^ 2)
      (record2680CenterRat3279 1)).hi =
      (RatInterval3276.powNat ratBaseInterval3284 188).hi := by
  have hsel := signed_bump_tail_selector3380_cell1_family4
  have hfactor :
      0 ≤
        (1 - (record2680CenterRat3279 1 /
          (storedWidthRat3287 4 ^ 2)) ^ 2)⁻¹ ^ (2 * 0) *
          ratBumpNumerator3310 0
            (record2680CenterRat3279 1 /
              (storedWidthRat3287 4 ^ 2)) /
          (storedWidthRat3287 4 ^ 2) ^ 0 := by
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
      rfl hbaseHi hfactor hfactor le_rfl
    simpa [RatInterval3276.mul, ratBumpNumerator3310] using hmul
  · norm_num [record2680CenterRat3279, storedWidthRat3287,
      Matrix.cons_val_four]

end ConnesWeilRH.Dev
