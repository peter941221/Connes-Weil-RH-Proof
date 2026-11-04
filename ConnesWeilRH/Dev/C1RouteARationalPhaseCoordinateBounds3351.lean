import ConnesWeilRH.Dev.C1RouteARationalPhaseEndpoint3348

namespace ConnesWeilRH.Dev

def ratPhaseRealEndpointAbsBound3351 (a : RatRect3276) : ℚ :=
  max |a.reLo| |a.reHi|

def ratPhaseImagEndpointAbsBound3351 (a : RatRect3276) : ℚ :=
  max |a.imLo| |a.imHi|

theorem ratPhaseRealEndpointAbsBound3351_cell0_family4 :
    ratPhaseRealEndpointAbsBound3351
        (ratPhaseRect3279
          (record2680PhaseAngleRat3279 0 4)) ≤ 1 := by
  norm_num [ratPhaseRealEndpointAbsBound3351, ratPhaseRect3279,
    ratPhaseRe3279, ratPhaseError3279, record2680PhaseAngleRat3279,
    record2680CenterRat3279, capturedModulationsRat3279,
    Matrix.cons_val_four]

theorem ratPhaseImagEndpointAbsBound3351_cell0_family4 :
    ratPhaseImagEndpointAbsBound3351
        (ratPhaseRect3279
          (record2680PhaseAngleRat3279 0 4)) ≤ 1 / 2 := by
  norm_num [ratPhaseImagEndpointAbsBound3351, ratPhaseRect3279,
    ratPhaseIm3279, ratPhaseError3279, record2680PhaseAngleRat3279,
    record2680CenterRat3279, capturedModulationsRat3279,
    Matrix.cons_val_four]

end ConnesWeilRH.Dev
