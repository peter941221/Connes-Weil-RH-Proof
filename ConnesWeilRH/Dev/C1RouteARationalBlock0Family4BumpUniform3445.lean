import ConnesWeilRH.Dev.C1RouteARationalIntervalIdentity3442

namespace ConnesWeilRH.Dev

set_option maxHeartbeats 12000000 in
set_option maxRecDepth 500000 in
theorem record2680_block0_family4_bump_tail3445
    {index : ℕ} (hindex : index < 256) :
    ratCellBumpInterval3298 index 4 =
      ({lo := 0, hi := (RatInterval3276.powNat ratBaseInterval3284 188).hi} :
        RatInterval3276) := by
  interval_cases index <;>
    norm_num [ratCellBumpInterval3298, ratBumpT3286,
      ratBumpInterval3286, ratTailBumpInterval3298,
      storedWidthRat3287, record2680CenterRat3279,
      Matrix.cons_val_four]

end ConnesWeilRH.Dev
