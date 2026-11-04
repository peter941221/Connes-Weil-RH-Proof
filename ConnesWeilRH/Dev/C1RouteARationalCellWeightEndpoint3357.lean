import ConnesWeilRH.Dev.C1RouteARationalTaylorEndpoint3346

namespace ConnesWeilRH.Dev

theorem ratCellWeightTaylorHi3357_cell0 :
    (ratTaylorInterval3283 (ratCellWeightArgument3289 0)).hi ≤
      169 / 160 := by
  norm_num [ratCellWeightArgument3289, record2680CenterRat3279,
    ratTaylorInterval3283, ratTaylorSum3283, ratTaylorError3283]

theorem ratCellWeightTaylorLoNonneg3357_cell0 :
    0 ≤ (ratTaylorInterval3283 (ratCellWeightArgument3289 0)).lo := by
  norm_num [ratCellWeightArgument3289, record2680CenterRat3279,
    ratTaylorInterval3283, ratTaylorSum3283, ratTaylorError3283]

theorem ratCellWeightTaylorHiNonneg3357_cell0 :
    0 ≤ (ratTaylorInterval3283 (ratCellWeightArgument3289 0)).hi := by
  exact le_trans (ratCellWeightTaylorLoNonneg3357_cell0)
    (by
      norm_num [ratCellWeightArgument3289, record2680CenterRat3279,
        ratTaylorInterval3283, ratTaylorSum3283, ratTaylorError3283])

theorem ratCellWeightTaylorOrder3357_cell0 :
    (ratTaylorInterval3283 (ratCellWeightArgument3289 0)).lo ≤
      (ratTaylorInterval3283 (ratCellWeightArgument3289 0)).hi := by
  norm_num [ratCellWeightArgument3289, record2680CenterRat3279,
    ratTaylorInterval3283, ratTaylorSum3283, ratTaylorError3283]

theorem ratCellWeightIntervalEndpointAbsBound3357_cell0 :
    ratIntervalEndpointAbsBound3325
      (ratCellWeightInterval3289 0) ≤ 32 := by
  have hTaylorLo := ratCellWeightTaylorLoNonneg3357_cell0
  have hTaylorHi := ratCellWeightTaylorHiNonneg3357_cell0
  have hTaylorOrder := ratCellWeightTaylorOrder3357_cell0
  rw [ratCellWeightInterval3289]
  unfold ratIntervalEndpointAbsBound3325
  rw [ratInterval_powNat_hi_eq_pow_of_nonneg3345
    (ratTaylorInterval3283 (ratCellWeightArgument3289 0))
    hTaylorLo hTaylorHi hTaylorOrder]
  have hpow :
      0 ≤ (ratTaylorInterval3283 (ratCellWeightArgument3289 0)).hi ^ 60 := by
    positivity
  have hpowLo :
      0 ≤ (RatInterval3276.powNat
        (ratTaylorInterval3283 (ratCellWeightArgument3289 0)) 60).lo := by
    exact ratInterval_powNat_lo_nonneg3344
      (ratTaylorInterval3283 (ratCellWeightArgument3289 0))
      hTaylorLo hTaylorHi 60
  have hpowOrder :
      (RatInterval3276.powNat
        (ratTaylorInterval3283 (ratCellWeightArgument3289 0)) 60).lo ≤
        (RatInterval3276.powNat
          (ratTaylorInterval3283 (ratCellWeightArgument3289 0)) 60).hi := by
    exact ratInterval_powNat_order3344
      (ratTaylorInterval3283 (ratCellWeightArgument3289 0)) 60
  apply max_le
  · rw [abs_of_nonneg hpowLo]
    exact le_trans hpowOrder (by
      rw [ratInterval_powNat_hi_eq_pow_of_nonneg3345
        (ratTaylorInterval3283 (ratCellWeightArgument3289 0))
        hTaylorLo hTaylorHi hTaylorOrder]
      norm_num [ratCellWeightArgument3289, record2680CenterRat3279,
        ratTaylorInterval3283, ratTaylorSum3283, ratTaylorError3283])
  · rw [abs_of_nonneg hpow]
    norm_num [ratCellWeightArgument3289, record2680CenterRat3279,
      ratTaylorInterval3283, ratTaylorSum3283, ratTaylorError3283]

end ConnesWeilRH.Dev
