import ConnesWeilRH.Dev.C1RouteARationalPhaseExactEndpoint3378

namespace ConnesWeilRH.Dev

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
 theorem phasePowSqEndpointAbsBound_threeHalves3403 :
    ratRectEndpointAbsBound3326
        (RatRect3276.powSq
          (ratPhaseRect3279
            (record2680PhaseAngleRat3279 1 4)) 9) ≤ 3 / 2 := by
  norm_num [ratRectEndpointAbsBound3326, RatRect3276.powSq,
    RatRect3276.mul, RatInterval3276.mul, RatInterval3276.sub,
    RatInterval3276.add, ratPhaseRect3279, ratPhaseRe3279,
    ratPhaseIm3279, ratPhaseError3279, record2680PhaseAngleRat3279,
    record2680CenterRat3279, capturedModulationsRat3279,
    Matrix.cons_val_four]

end ConnesWeilRH.Dev
