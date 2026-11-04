import ConnesWeilRH.Dev.C1RouteARationalTaylorEndpoint3346
import ConnesWeilRH.Dev.C1RouteARationalBumpSign3336

namespace ConnesWeilRH.Dev

theorem ratInterval_mul_hi_eq_hi_mul_of_zero_lo_nonneg3347
    (a b : RatInterval3276)
    (haLo : a.lo = 0) (haHi : 0 ≤ a.hi)
    (hbLo : 0 ≤ b.lo) (hbHi : 0 ≤ b.hi)
    (hbOrder : b.lo ≤ b.hi) :
    (RatInterval3276.mul a b).hi = a.hi * b.hi := by
  apply ratInterval_mul_hi_eq_hi_mul_hi_of_nonneg3345
  · rw [haLo]
  · exact haHi
  · exact hbLo
  · exact hbHi
  · rw [haLo]
    exact haHi
  · exact hbOrder

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem signed_bump_endpoint3347_cell0_order0_family4_hi_eq :
    (ratBumpJetInterval3310 0 (storedWidthRat3287 4 ^ 2)
      (record2680CenterRat3279 0)).hi =
      (RatInterval3276.powNat ratBaseInterval3284 188).hi := by
  have hsel := signed_bump_tail_selector3335_cell0_family4
  have hfactor :
      0 ≤
        (1 - (record2680CenterRat3279 0 /
          (storedWidthRat3287 4 ^ 2)) ^ 2)⁻¹ ^ (2 * 0) *
          ratBumpNumerator3310 0
            (record2680CenterRat3279 0 /
              (storedWidthRat3287 4 ^ 2)) /
          (storedWidthRat3287 4 ^ 2) ^ 0 := by
    norm_num [ratBumpNumerator3310, record2680CenterRat3279,
      storedWidthRat3287, Matrix.cons_val_four]
  have hbaseHi :
      0 ≤ (RatInterval3276.powNat ratBaseInterval3284 188).hi :=
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem signed_bump_endpoint3347_cell0_order1_family4_hi_eq :
    (ratBumpJetInterval3310 1 (storedWidthRat3287 4 ^ 2)
      (record2680CenterRat3279 0)).hi =
      (RatInterval3276.powNat ratBaseInterval3284 188).hi *
        ((1 - (record2680CenterRat3279 0 /
          (storedWidthRat3287 4 ^ 2)) ^ 2)⁻¹ ^ (2 * 1) *
          ratBumpNumerator3310 1
            (record2680CenterRat3279 0 /
              (storedWidthRat3287 4 ^ 2)) /
          (storedWidthRat3287 4 ^ 2) ^ 1) := by
  have hsel := signed_bump_tail_selector3335_cell0_family4
  have hfactor :
      0 ≤
        (1 - (record2680CenterRat3279 0 /
          (storedWidthRat3287 4 ^ 2)) ^ 2)⁻¹ ^ (2 * 1) *
          ratBumpNumerator3310 1
            (record2680CenterRat3279 0 /
              (storedWidthRat3287 4 ^ 2)) /
          (storedWidthRat3287 4 ^ 2) ^ 1 := by
    norm_num [ratBumpNumerator3310, record2680CenterRat3279,
      storedWidthRat3287, Matrix.cons_val_four]
  have hbaseHi :
      0 ≤ (RatInterval3276.powNat ratBaseInterval3284 188).hi :=
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
theorem signed_bump_endpoint3347_cell0_order2_family4_hi_eq :
    (ratBumpJetInterval3310 2 (storedWidthRat3287 4 ^ 2)
      (record2680CenterRat3279 0)).hi =
      (RatInterval3276.powNat ratBaseInterval3284 188).hi *
        ((1 - (record2680CenterRat3279 0 /
          (storedWidthRat3287 4 ^ 2)) ^ 2)⁻¹ ^ (2 * 2) *
          ratBumpNumerator3310 2
            (record2680CenterRat3279 0 /
              (storedWidthRat3287 4 ^ 2)) /
          (storedWidthRat3287 4 ^ 2) ^ 2) := by
  have hsel := signed_bump_tail_selector3335_cell0_family4
  have hfactor :
      0 ≤
        (1 - (record2680CenterRat3279 0 /
          (storedWidthRat3287 4 ^ 2)) ^ 2)⁻¹ ^ (2 * 2) *
          ratBumpNumerator3310 2
            (record2680CenterRat3279 0 /
              (storedWidthRat3287 4 ^ 2)) /
          (storedWidthRat3287 4 ^ 2) ^ 2 := by
    norm_num [ratBumpNumerator3310, record2680CenterRat3279,
      storedWidthRat3287, Matrix.cons_val_four]
  have hbaseHi :
      0 ≤ (RatInterval3276.powNat ratBaseInterval3284 188).hi :=
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

end ConnesWeilRH.Dev
