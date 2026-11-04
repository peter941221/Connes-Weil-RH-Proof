import ConnesWeilRH.Dev.C1RouteARationalWeightedPhaseEndpoint3379
import ConnesWeilRH.Dev.C1RouteARationalBumpEndpoint3382
import ConnesWeilRH.Dev.C1RouteARationalComplexEndpointBounds3349

namespace ConnesWeilRH.Dev

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem signed_jet_endpoint3383_cell1_order2_index1_family4_reHi_le :
    (ratWeightedUnitJetRect3310 2 1 1 4).reHi ≤ 1 / 10 ^ 26 := by
  have hlambdaOrder :
      (ratWeightedLambdaRect3310 4).reLo ≤
          (ratWeightedLambdaRect3310 4).reHi ∧
        (ratWeightedLambdaRect3310 4).imLo ≤
          (ratWeightedLambdaRect3310 4).imHi := by
    norm_num [ratWeightedLambdaRect3310]
  have hscalar : ∀ a : RatRect3276,
      a.reLo ≤ a.reHi -> a.imLo ≤ a.imHi ->
      RatRect3276.mul (ratScalarRect3310 1) a = a := by
    intro a hRe hIm
    rcases a with ⟨reLo, reHi, imLo, imHi⟩
    simp [ratScalarRect3310, RatRect3276.mul, RatInterval3276.mul,
      RatInterval3276.sub, RatInterval3276.add, min_eq_left hRe,
      max_eq_right hRe, min_eq_left hIm, max_eq_right hIm]
  have hpow :
      ratRectPowNat3310 (ratWeightedLambdaRect3310 4) 1 =
        ratWeightedLambdaRect3310 4 := by
    rw [ratRectPowNat3310]
    exact hscalar _ hlambdaOrder.1 hlambdaOrder.2
  have hlambda :
      ratRectEndpointAbsBound3326 (ratWeightedLambdaRect3310 4) ≤ 40 := by
    norm_num [ratRectEndpointAbsBound3326, ratWeightedLambdaRect3310,
      capturedModulationsRat3279, Matrix.cons_val_four]
  have hweight :
      ratRectEndpointAbsBound3326
        (ratRealRect3281 (ratCellWeightInterval3289 1)) ≤ 32 := by
    unfold ratRectEndpointAbsBound3326 ratRealRect3281
    have h := ratCellWeightIntervalEndpointAbsBound3377_cell1
    change max (max |(ratCellWeightInterval3289 1).lo|
      |(ratCellWeightInterval3289 1).hi|) (max |(0 : ℚ)| |(0 : ℚ)|) ≤ 32
    exact max_le h (by norm_num)
  have hphaseFull :
      ratRectEndpointAbsBound3326 (ratWeightedPhaseRect3310 1 4) ≤ 128 := by
    rw [ratWeightedPhaseRect_orientation3361]
    have hmul := ratRect_mul_endpointAbsBound3349
      (RatRect3276.powSq
        (ratPhaseRect3279
          (record2680PhaseAngleRat3279 1 4)) 9)
      (ratRealRect3281 (ratCellWeightInterval3289 1))
    have hphasePow :
        ratRectEndpointAbsBound3326
          (RatRect3276.powSq
            (ratPhaseRect3279
              (record2680PhaseAngleRat3279 1 4)) 9) ≤ 2 := by
      exact ratPhasePowSqEndpointAbsBound3378_cell1_family4_nine
    calc
      ratRectEndpointAbsBound3326
          ((RatRect3276.powSq
            (ratPhaseRect3279
              (record2680PhaseAngleRat3279 1 4)) 9).mul
            (ratRealRect3281 (ratCellWeightInterval3289 1))) ≤
          2 * ratRectEndpointAbsBound3326
            (RatRect3276.powSq
              (ratPhaseRect3279
                (record2680PhaseAngleRat3279 1 4)) 9) *
            ratRectEndpointAbsBound3326
              (ratRealRect3281 (ratCellWeightInterval3289 1)) := hmul
      _ ≤ 2 * 2 * 32 := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hphasePow (by norm_num))
          hweight (ratRectEndpointAbsBound3326_nonneg _) (by norm_num)
      _ ≤ 128 := by norm_num
  have hinner :
      ratRectEndpointAbsBound3326
        (RatRect3276.mul
          (ratWeightedLambdaRect3310 4)
          (ratWeightedPhaseRect3310 1 4)) ≤ 10240 := by
    calc
      ratRectEndpointAbsBound3326
          (RatRect3276.mul
            (ratWeightedLambdaRect3310 4)
            (ratWeightedPhaseRect3310 1 4)) ≤
          2 * ratRectEndpointAbsBound3326
            (ratWeightedLambdaRect3310 4) *
            ratRectEndpointAbsBound3326 (ratWeightedPhaseRect3310 1 4) :=
        ratRect_mul_endpointAbsBound3349 _ _
      _ ≤ 2 * 40 * 128 := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hlambda (by norm_num))
          hphaseFull (ratRectEndpointAbsBound3326_nonneg _) (by norm_num)
      _ ≤ 10240 := by norm_num
  have hcore :
      ratRectEndpointAbsBound3326
        (RatRect3276.mul
          (ratScalarRect3310 2)
          (RatRect3276.mul
            (ratWeightedLambdaRect3310 4)
            (ratWeightedPhaseRect3310 1 4))) ≤ 65536 := by
    have hscalar2 :
        ratRectEndpointAbsBound3326 (ratScalarRect3310 2) = 2 := by
      norm_num [ratRectEndpointAbsBound3326, ratScalarRect3310]
    have hmul := ratRect_mul_endpointAbsBound3349
      (ratScalarRect3310 2)
      (RatRect3276.mul
        (ratWeightedLambdaRect3310 4)
        (ratWeightedPhaseRect3310 1 4))
    calc
      ratRectEndpointAbsBound3326
          (RatRect3276.mul
            (ratScalarRect3310 2)
            (RatRect3276.mul
              (ratWeightedLambdaRect3310 4)
              (ratWeightedPhaseRect3310 1 4))) ≤
          2 * ratRectEndpointAbsBound3326 (ratScalarRect3310 2) *
            ratRectEndpointAbsBound3326
              (RatRect3276.mul
                (ratWeightedLambdaRect3310 4)
                (ratWeightedPhaseRect3310 1 4)) := hmul
      _ ≤ 2 * 2 * 10240 := by
        rw [hscalar2]
        exact mul_le_mul_of_nonneg_left hinner (by norm_num)
      _ ≤ 65536 := by norm_num
  have hcoreCoord :
      ratRectRealCoordinateAbsBound3356
        (RatRect3276.mul
          (ratScalarRect3310 2)
          (RatRect3276.mul
            (ratWeightedLambdaRect3310 4)
            (ratWeightedPhaseRect3310 1 4))) ≤ 65536 := by
    unfold ratRectEndpointAbsBound3326 at hcore
    exact le_trans (le_max_left _ _) hcore
  have hbumpLo : 0 ≤ (ratBumpJetInterval3310 1
      (storedWidthRat3287 4 ^ 2) (record2680CenterRat3279 1)).lo := by
    rw [signed_bump_endpoint3382_cell1_order1_family4_reLo_eq_zero]
  have hbumpHi : 0 ≤ (ratBumpJetInterval3310 1
      (storedWidthRat3287 4 ^ 2) (record2680CenterRat3279 1)).hi := by
    rw [signed_bump_endpoint3382_cell1_order1_family4_hi_eq]
    exact mul_nonneg (ratBaseInterval3284_powNat_hi_nonneg3344 188) (by
      norm_num [ratBumpNumerator3310, record2680CenterRat3279,
        storedWidthRat3287, Matrix.cons_val_four])
  have hbumpOrder :
      (ratBumpJetInterval3310 1
        (storedWidthRat3287 4 ^ 2) (record2680CenterRat3279 1)).lo ≤
      (ratBumpJetInterval3310 1
        (storedWidthRat3287 4 ^ 2) (record2680CenterRat3279 1)).hi := by
    rw [signed_bump_endpoint3382_cell1_order1_family4_reLo_eq_zero]
    exact hbumpHi
  have hbump :
      (ratBumpJetInterval3310 1
        (storedWidthRat3287 4 ^ 2) (record2680CenterRat3279 1)).hi ≤
      1 / 10 ^ 31 := by
    rw [signed_bump_endpoint3382_cell1_order1_family4_hi_eq]
    rw [ratBaseInterval3284_powNat_hi_eq_pow3346]
    norm_num (config := { maxSteps := 2000000000 }) [
      ratBaseInterval3284, ratTaylorInterval3283, ratTaylorSum3283,
      ratTaylorError3283, storedWidthRat3287, record2680CenterRat3279,
      ratBumpNumerator3310, Matrix.cons_val_four]
  rw [ratWeightedUnitJetRect3310]
  rw [show (Nat.choose 2 1 : ℚ) = 2 by norm_num, hpow]
  calc
    (RatRect3276.mul
      (RatRect3276.mul
        (ratScalarRect3310 2)
        (RatRect3276.mul
          (ratWeightedLambdaRect3310 4)
          (ratWeightedPhaseRect3310 1 4)))
      (ratBumpRect3310 1 1 4)).reHi ≤
        65536 * (ratBumpJetInterval3310 1
          (storedWidthRat3287 4 ^ 2) (record2680CenterRat3279 1)).hi := by
      have hbridge := ratRect_mul_real_hi_le_coordinate_bound3358
        (RatRect3276.mul
          (ratScalarRect3310 2)
          (RatRect3276.mul
            (ratWeightedLambdaRect3310 4)
            (ratWeightedPhaseRect3310 1 4)))
        (ratBumpJetInterval3310 1
          (storedWidthRat3287 4 ^ 2) (record2680CenterRat3279 1))
        hbumpLo hbumpHi hbumpOrder
      have hbridge2 :
          (RatRect3276.mul
            (RatRect3276.mul
              (ratScalarRect3310 2)
              (RatRect3276.mul
                (ratWeightedLambdaRect3310 4)
                (ratWeightedPhaseRect3310 1 4)))
            (ratBumpRect3310 1 1 4)).reHi ≤
            ratRectRealCoordinateAbsBound3356
              (RatRect3276.mul
                (ratScalarRect3310 2)
                (RatRect3276.mul
                  (ratWeightedLambdaRect3310 4)
                  (ratWeightedPhaseRect3310 1 4))) *
              (ratBumpJetInterval3310 1
                (storedWidthRat3287 4 ^ 2) (record2680CenterRat3279 1)).hi := by
        simpa [ratBumpRect3310] using hbridge
      exact le_trans hbridge2
        (mul_le_mul_of_nonneg_right hcoreCoord hbumpHi)
    _ ≤ 65536 * (1 / 10 ^ 31) := by
      exact mul_le_mul_of_nonneg_left hbump (by norm_num)
    _ ≤ 1 / 10 ^ 26 := by norm_num

end ConnesWeilRH.Dev
