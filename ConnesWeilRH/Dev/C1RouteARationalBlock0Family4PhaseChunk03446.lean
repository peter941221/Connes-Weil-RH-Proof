import ConnesWeilRH.Dev.C1RouteARationalPhaseExactProbe3354

namespace ConnesWeilRH.Dev

set_option maxHeartbeats 12000000 in
set_option maxRecDepth 500000 in
theorem record2680_block0_family4_phase_chunk0_abs_le_2_3446
    {index : ℕ} (hindex : index < 32) :
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
