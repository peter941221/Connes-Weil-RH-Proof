import ConnesWeilRH.Dev.C1RouteARationalTaylorEndpoint3346

namespace ConnesWeilRH.Dev

theorem ratCellWeightTaylorHi3377_cell1 :
    (ratTaylorInterval3283 (ratCellWeightArgument3289 1)).hi ≤
      169 / 160 := by
  norm_num [ratCellWeightArgument3289, record2680CenterRat3279,
    ratTaylorInterval3283, ratTaylorSum3283, ratTaylorError3283]

theorem ratCellWeightTaylorLoNonneg3377_cell1 :
    0 ≤ (ratTaylorInterval3283 (ratCellWeightArgument3289 1)).lo := by
  norm_num [ratCellWeightArgument3289, record2680CenterRat3279,
    ratTaylorInterval3283, ratTaylorSum3283, ratTaylorError3283]

theorem ratCellWeightTaylorHiNonneg3377_cell1 :
    0 ≤ (ratTaylorInterval3283 (ratCellWeightArgument3289 1)).hi := by
  exact le_trans (ratCellWeightTaylorLoNonneg3377_cell1)
    (by
      norm_num [ratCellWeightArgument3289, record2680CenterRat3279,
        ratTaylorInterval3283, ratTaylorSum3283, ratTaylorError3283])

theorem ratCellWeightTaylorOrder3377_cell1 :
    (ratTaylorInterval3283 (ratCellWeightArgument3289 1)).lo ≤
      (ratTaylorInterval3283 (ratCellWeightArgument3289 1)).hi := by
  norm_num [ratCellWeightArgument3289, record2680CenterRat3279,
    ratTaylorInterval3283, ratTaylorSum3283, ratTaylorError3283]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem ratCellWeightIntervalEndpointAbsBound3377_cell1 :
    ratIntervalEndpointAbsBound3325
      (ratCellWeightInterval3289 1) ≤ 32 := by
  have hTaylorLo := ratCellWeightTaylorLoNonneg3377_cell1
  have hTaylorHi := ratCellWeightTaylorHiNonneg3377_cell1
  have hTaylorOrder := ratCellWeightTaylorOrder3377_cell1
  rw [ratCellWeightInterval3289]
  unfold ratIntervalEndpointAbsBound3325
  rw [ratInterval_powNat_hi_eq_pow_of_nonneg3345
    (ratTaylorInterval3283 (ratCellWeightArgument3289 1))
    hTaylorLo hTaylorHi hTaylorOrder]
  have hpow :
      0 ≤ (ratTaylorInterval3283 (ratCellWeightArgument3289 1)).hi ^ 60 := by
    positivity
  have hpowLo :
      0 ≤ (RatInterval3276.powNat
        (ratTaylorInterval3283 (ratCellWeightArgument3289 1)) 60).lo := by
    exact ratInterval_powNat_lo_nonneg3344
      (ratTaylorInterval3283 (ratCellWeightArgument3289 1))
      hTaylorLo hTaylorHi 60
  have hpowOrder :
      (RatInterval3276.powNat
        (ratTaylorInterval3283 (ratCellWeightArgument3289 1)) 60).lo ≤
      (RatInterval3276.powNat
        (ratTaylorInterval3283 (ratCellWeightArgument3289 1)) 60).hi := by
    exact ratInterval_powNat_order3344
      (ratTaylorInterval3283 (ratCellWeightArgument3289 1)) 60
  apply max_le
  · rw [abs_of_nonneg hpowLo]
    exact le_trans hpowOrder (by
      rw [ratInterval_powNat_hi_eq_pow_of_nonneg3345
        (ratTaylorInterval3283 (ratCellWeightArgument3289 1))
        hTaylorLo hTaylorHi hTaylorOrder]
      norm_num [ratCellWeightArgument3289, record2680CenterRat3279,
        ratTaylorInterval3283, ratTaylorSum3283, ratTaylorError3283])
  · rw [abs_of_nonneg hpow]
    norm_num [ratCellWeightArgument3289, record2680CenterRat3279,
      ratTaylorInterval3283, ratTaylorSum3283, ratTaylorError3283]

end ConnesWeilRH.Dev
