import ConnesWeilRH.Dev.C1RouteARationalComplexEndpointBounds3328
import ConnesWeilRH.Dev.C1RouteARationalPhase3279

namespace ConnesWeilRH.Dev

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem ratPhaseRectEndpointAbsBound3375_cell1_family4 :
    ratRectEndpointAbsBound3326
        (ratPhaseRect3279
          (record2680PhaseAngleRat3279 1 4)) ≤ 2 := by
  norm_num [ratRectEndpointAbsBound3326, ratPhaseRect3279,
    ratPhaseRe3279, ratPhaseIm3279, ratPhaseError3279,
    record2680PhaseAngleRat3279, record2680CenterRat3279,
    capturedModulationsRat3279, Matrix.cons_val_four]

end ConnesWeilRH.Dev
