import ConnesWeilRH.Dev.C1RouteARationalIntervalIdentity3442
import ConnesWeilRH.Dev.C1RouteARationalPhaseExactProbe3354

namespace ConnesWeilRH.Dev

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 1000000 in
theorem record2680_block0_family4_bump_tail3444
    {index : ℕ} (hindex : index < 256) :
    ratCellBumpInterval3298 index 4 =
      ({lo := 0, hi := (RatInterval3276.powNat ratBaseInterval3284 188).hi} :
        RatInterval3276) := by
  interval_cases index <;>
    norm_num [ratCellBumpInterval3298, ratBumpT3286,
      ratBumpInterval3286, ratTailBumpInterval3298,
      storedWidthRat3287, record2680CenterRat3279,
      Matrix.cons_val_four]

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 1000000 in
theorem record2680_block0_family4_phase_abs_le_2_3444
    {index : ℕ} (hindex : index < 256) :
    ratRectEndpointAbsBound3326
        (RatRect3276.powSq
          (ratPhaseRect3279
            (record2680PhaseAngleRat3279 index 4)) 9) ≤ 2 := by
  interval_cases index <;>
    norm_num [ratRectEndpointAbsBound3326, RatRect3276.powSq,
      RatRect3276.mul, RatInterval3276.mul, RatInterval3276.sub,
      RatInterval3276.add, ratPhaseRect3279, ratPhaseRe3279,
      ratPhaseIm3279, ratPhaseError3279, record2680PhaseAngleRat3279,
      record2680CenterRat3279, capturedModulationsRat3279,
      Matrix.cons_val_four]

end ConnesWeilRH.Dev
