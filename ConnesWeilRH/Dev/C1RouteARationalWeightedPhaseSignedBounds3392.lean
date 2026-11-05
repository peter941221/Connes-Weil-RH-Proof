import ConnesWeilRH.Dev.C1RouteARationalRealScalingSignedBounds3391
import ConnesWeilRH.Dev.C1RouteARationalPhaseExactEndpoint3378
import ConnesWeilRH.Dev.C1RouteARationalCellWeightEndpoint3377
import ConnesWeilRH.Dev.C1RouteARationalWeightedPhaseOrientation3361

namespace ConnesWeilRH.Dev

theorem ratWeightedPhaseRect_cell1_family4_reLo_ge3392 :
    -(64 : ℚ) ≤ (ratWeightedPhaseRect3310 1 4).reLo := by
  rw [ratWeightedPhaseRect_orientation3361]
  have hlo := ratInterval_powNat_lo_nonneg3344
    (ratTaylorInterval3283 (ratCellWeightArgument3289 1))
    ratCellWeightTaylorLoNonneg3377_cell1
    ratCellWeightTaylorHiNonneg3377_cell1 60
  have hhi := ratInterval_powNat_hi_nonneg3344
    (ratTaylorInterval3283 (ratCellWeightArgument3289 1))
    ratCellWeightTaylorLoNonneg3377_cell1
    ratCellWeightTaylorHiNonneg3377_cell1 60
  have horder := ratInterval_powNat_order3344
    (ratTaylorInterval3283 (ratCellWeightArgument3289 1)) 60
  have hscale := ratRect_mul_real_reLo_ge_coordinate_bound3391
    (RatRect3276.powSq
      (ratPhaseRect3279
        (record2680PhaseAngleRat3279 1 4)) 9)
    (ratCellWeightInterval3289 1) hlo hhi horder
  have hphase : ratRectRealCoordinateAbsBound3356
      (RatRect3276.powSq
        (ratPhaseRect3279
          (record2680PhaseAngleRat3279 1 4)) 9) ≤ 2 := by
    unfold ratRectRealCoordinateAbsBound3356
    exact le_trans (le_max_left _ _)
      ratPhasePowSqEndpointAbsBound3378_cell1_family4_nine
  have hweight : (ratCellWeightInterval3289 1).hi ≤ 32 := by
    exact le_trans (le_abs_self _)
      (le_trans (le_max_right _ _)
        ratCellWeightIntervalEndpointAbsBound3377_cell1)
  have hweightHi : 0 ≤ (ratCellWeightInterval3289 1).hi := hhi
  calc
    -(64 : ℚ) ≤ -(ratRectRealCoordinateAbsBound3356
        (RatRect3276.powSq
          (ratPhaseRect3279
            (record2680PhaseAngleRat3279 1 4)) 9) *
        (ratCellWeightInterval3289 1).hi) := by
      nlinarith
    _ ≤ (RatRect3276.mul
        (RatRect3276.powSq
          (ratPhaseRect3279
            (record2680PhaseAngleRat3279 1 4)) 9)
        (ratRealRect3281 (ratCellWeightInterval3289 1))).reLo := hscale

theorem ratWeightedPhaseRect_cell1_family4_imHi_le3392 :
    (ratWeightedPhaseRect3310 1 4).imHi ≤ 64 := by
  rw [ratWeightedPhaseRect_orientation3361]
  have hlo := ratInterval_powNat_lo_nonneg3344
    (ratTaylorInterval3283 (ratCellWeightArgument3289 1))
    ratCellWeightTaylorLoNonneg3377_cell1
    ratCellWeightTaylorHiNonneg3377_cell1 60
  have hhi := ratInterval_powNat_hi_nonneg3344
    (ratTaylorInterval3283 (ratCellWeightArgument3289 1))
    ratCellWeightTaylorLoNonneg3377_cell1
    ratCellWeightTaylorHiNonneg3377_cell1 60
  have horder := ratInterval_powNat_order3344
    (ratTaylorInterval3283 (ratCellWeightArgument3289 1)) 60
  have hscale := ratRect_mul_real_imHi_le_coordinate_bound3391
    (RatRect3276.powSq
      (ratPhaseRect3279
        (record2680PhaseAngleRat3279 1 4)) 9)
    (ratCellWeightInterval3289 1) hlo hhi horder
  have hphase : ratRectImagCoordinateAbsBound3391
      (RatRect3276.powSq
        (ratPhaseRect3279
          (record2680PhaseAngleRat3279 1 4)) 9) ≤ 2 := by
    unfold ratRectImagCoordinateAbsBound3391
    exact le_trans (le_max_right _ _)
      ratPhasePowSqEndpointAbsBound3378_cell1_family4_nine
  have hweight : (ratCellWeightInterval3289 1).hi ≤ 32 := by
    exact le_trans (le_abs_self _)
      (le_trans (le_max_right _ _)
        ratCellWeightIntervalEndpointAbsBound3377_cell1)
  have hweightHi : 0 ≤ (ratCellWeightInterval3289 1).hi := hhi
  calc
    (RatRect3276.mul
        (RatRect3276.powSq
          (ratPhaseRect3279
            (record2680PhaseAngleRat3279 1 4)) 9)
        (ratRealRect3281 (ratCellWeightInterval3289 1))).imHi ≤
      ratRectImagCoordinateAbsBound3391
        (RatRect3276.powSq
          (ratPhaseRect3279
            (record2680PhaseAngleRat3279 1 4)) 9) *
        (ratCellWeightInterval3289 1).hi := hscale
    _ ≤ 64 := by nlinarith

end ConnesWeilRH.Dev
