import ConnesWeilRH.Dev.C1RouteARationalWeightedPhaseOrientation3361
import ConnesWeilRH.Dev.C1RouteARationalRealScalingEndpoint3358
import ConnesWeilRH.Dev.C1RouteARationalPhaseExactEndpoint3378
import ConnesWeilRH.Dev.C1RouteARationalCellWeightEndpoint3377

namespace ConnesWeilRH.Dev

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem ratWeightedPhaseRect_cell1_family4_realAbs_le3379 :
    ratRectRealCoordinateAbsBound3356
      (ratWeightedPhaseRect3310 1 4) ≤ 64 := by
  rw [ratWeightedPhaseRect_orientation3361]
  have hweightLo : 0 ≤ (ratCellWeightInterval3289 1).lo := by
    exact ratInterval_powNat_lo_nonneg3344
      (ratTaylorInterval3283 (ratCellWeightArgument3289 1))
      ratCellWeightTaylorLoNonneg3377_cell1
      ratCellWeightTaylorHiNonneg3377_cell1 60
  have hweightHi : 0 ≤ (ratCellWeightInterval3289 1).hi := by
    exact ratInterval_powNat_hi_nonneg3344
      (ratTaylorInterval3283 (ratCellWeightArgument3289 1))
      ratCellWeightTaylorLoNonneg3377_cell1
      ratCellWeightTaylorHiNonneg3377_cell1 60
  have hweightOrder :
      (ratCellWeightInterval3289 1).lo ≤
        (ratCellWeightInterval3289 1).hi := by
    exact ratInterval_powNat_order3344
      (ratTaylorInterval3283 (ratCellWeightArgument3289 1)) 60
  have hscaled := ratRect_mul_real_coordinate_abs_bound3358
    (RatRect3276.powSq
      (ratPhaseRect3279
        (record2680PhaseAngleRat3279 1 4)) 9)
    (ratCellWeightInterval3289 1)
    hweightLo hweightHi hweightOrder
  have hphase :
      ratRectRealCoordinateAbsBound3356
        (RatRect3276.powSq
          (ratPhaseRect3279
            (record2680PhaseAngleRat3279 1 4)) 9) ≤ 2 := by
    unfold ratRectRealCoordinateAbsBound3356
    calc
      max
          |(RatRect3276.powSq
              (ratPhaseRect3279
                (record2680PhaseAngleRat3279 1 4)) 9).reLo|
          |(RatRect3276.powSq
              (ratPhaseRect3279
                (record2680PhaseAngleRat3279 1 4)) 9).reHi| ≤
          ratRectEndpointAbsBound3326
            (RatRect3276.powSq
              (ratPhaseRect3279
                (record2680PhaseAngleRat3279 1 4)) 9) := by
            unfold ratRectEndpointAbsBound3326
            exact le_max_left _ _
      _ ≤ 2 := ratPhasePowSqEndpointAbsBound3378_cell1_family4_nine
  have hweight :
      (ratCellWeightInterval3289 1).hi ≤ 32 := by
    exact le_trans (le_abs_self _)
      (le_trans
        (le_max_right |(ratCellWeightInterval3289 1).lo|
          |(ratCellWeightInterval3289 1).hi|)
        ratCellWeightIntervalEndpointAbsBound3377_cell1)
  calc
    ratRectRealCoordinateAbsBound3356
        (RatRect3276.mul
          (RatRect3276.powSq
            (ratPhaseRect3279
              (record2680PhaseAngleRat3279 1 4)) 9)
          (ratRealRect3281 (ratCellWeightInterval3289 1))) ≤
        2 * (ratCellWeightInterval3289 1).hi := by
      exact le_trans hscaled
        (mul_le_mul_of_nonneg_right hphase hweightHi)
    _ ≤ 2 * 32 := by
      exact mul_le_mul_of_nonneg_left hweight (by norm_num)
    _ ≤ 64 := by norm_num

end ConnesWeilRH.Dev
