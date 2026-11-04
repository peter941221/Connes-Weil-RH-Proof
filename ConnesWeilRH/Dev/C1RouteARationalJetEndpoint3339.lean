import ConnesWeilRH.Dev.C1RouteARationalJetEndpoint3338
import ConnesWeilRH.Dev.C1RouteARationalTaylorEndpoint3344

namespace ConnesWeilRH.Dev

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem signed_bump_endpoint3339_cell0_order0_family4_reLo_eq_zero :
    (ratBumpJetInterval3310 0 (storedWidthRat3287 4 ^ 2)
      (record2680CenterRat3279 0)).lo = 0 := by
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
  have hbaseHi : 0 ≤ (RatInterval3276.powNat ratBaseInterval3284 188).hi := by
    exact ratBaseInterval3284_powNat_hi_nonneg3344 188
  unfold ratBumpJetInterval3310
  rw [if_pos]
  · rw [hsel]
    dsimp [RatInterval3276.mul]
    apply le_antisymm
    · norm_num
    · apply le_min
      · apply le_min <;> norm_num
      · apply le_min <;> exact mul_nonneg
          hbaseHi hfactor
  · norm_num [record2680CenterRat3279, storedWidthRat3287,
      Matrix.cons_val_four]

theorem signed_jet_endpoint3339_cell0_order2_index2_reLo_le_zero :
    (ratWeightedUnitJetRect3310 2 2 0 4).reLo ≤ 0 := by
  unfold ratWeightedUnitJetRect3310
  apply ratRect_mul_real_reLo_le_zero_of_zero_lo3338
  exact signed_bump_endpoint3339_cell0_order0_family4_reLo_eq_zero

end ConnesWeilRH.Dev
