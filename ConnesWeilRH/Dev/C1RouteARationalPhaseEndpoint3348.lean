import ConnesWeilRH.Dev.C1RouteARationalComplexEndpointBounds3328
import ConnesWeilRH.Dev.C1RouteARationalPhase3279

namespace ConnesWeilRH.Dev

theorem ratPhaseRectEndpointAbsBound3348_cell0_family4 :
    ratRectEndpointAbsBound3326
        (ratPhaseRect3279
          (record2680PhaseAngleRat3279 0 4)) ≤ 2 := by
  norm_num [ratRectEndpointAbsBound3326, ratPhaseRect3279,
    ratPhaseRe3279, ratPhaseIm3279, ratPhaseError3279,
    record2680PhaseAngleRat3279, record2680CenterRat3279,
    capturedModulationsRat3279, Matrix.cons_val_four]

end ConnesWeilRH.Dev
