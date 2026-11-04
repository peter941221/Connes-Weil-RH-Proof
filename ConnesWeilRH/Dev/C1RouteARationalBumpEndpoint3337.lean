import ConnesWeilRH.Dev.C1RouteARationalBumpSign3336
import ConnesWeilRH.Dev.C1RouteARationalTaylorEndpoint3344

namespace ConnesWeilRH.Dev

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem signed_bump_endpoint3337_cell0_order2_family4_reLo_eq_zero :
    (ratBumpJetInterval3310 2 (storedWidthRat3287 4 ^ 2)
      (record2680CenterRat3279 0)).lo = 0 := by
  have hsel := signed_bump_tail_selector3335_cell0_family4
  have hfactor := signed_bump_factor3336_cell0_order2_family4_nonneg
  have hfactor' :
      0 ≤
        (1 - (|record2680CenterRat3279 0| /
          (storedWidthRat3287 4 ^ 2)) ^ 2)⁻¹ ^ (2 * 2) *
          ratBumpNumerator3310 2
            (|record2680CenterRat3279 0| /
              (storedWidthRat3287 4 ^ 2)) /
          (storedWidthRat3287 4 ^ 2) ^ 2 := by
    simpa using hfactor
  have hfactorCenter :
      0 ≤
        (1 - (record2680CenterRat3279 0 /
          (storedWidthRat3287 4 ^ 2)) ^ 2)⁻¹ ^ (2 * 2) *
          ratBumpNumerator3310 2
            (record2680CenterRat3279 0 /
              (storedWidthRat3287 4 ^ 2)) /
          (storedWidthRat3287 4 ^ 2) ^ 2 := by
    norm_num [ratBumpNumerator3310, record2680CenterRat3279,
      storedWidthRat3287, Matrix.cons_val_four]
  have hbaseHi : 0 ≤ (RatInterval3276.powNat ratBaseInterval3284 188).hi := by
    exact ratBaseInterval3284_powNat_hi_nonneg3344 188
  have htail0 :
      (ratTailBumpInterval3298
          (ratBumpT3286 (storedWidthRat3287 4 ^ 2)
            |record2680CenterRat3279 0|)).lo = 0 := by
    rw [hsel]
  unfold ratBumpJetInterval3310
  rw [if_pos]
  · rw [hsel]
    dsimp [RatInterval3276.mul]
    apply le_antisymm
    · norm_num
    · apply le_min
      · apply le_min <;> norm_num
      · apply le_min <;> exact mul_nonneg hbaseHi hfactorCenter
  · norm_num [record2680CenterRat3279, storedWidthRat3287,
      Matrix.cons_val_four]

end ConnesWeilRH.Dev
