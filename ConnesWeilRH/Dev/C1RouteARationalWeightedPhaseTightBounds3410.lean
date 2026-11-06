import ConnesWeilRH.Dev.C1RouteARationalPhaseExactEndpoint3409
import ConnesWeilRH.Dev.C1RouteARationalWeightedPhaseSignedBounds3392
import ConnesWeilRH.Dev.C1RouteARationalWeightedPhaseOrientation3361
import ConnesWeilRH.Dev.C1RouteARationalRealScalingEndpoint3358

namespace ConnesWeilRH.Dev

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem ratWeightedPhaseRect_cell1_family4_realAbs_le3410 :
    ratRectRealCoordinateAbsBound3356
      (ratWeightedPhaseRect3310 1 4) ≤ 32 := by
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
  have hscale := ratRect_mul_real_coordinate_abs_bound3358
    (RatRect3276.powSq
      (ratPhaseRect3279 (record2680PhaseAngleRat3279 1 4)) 9)
    (ratCellWeightInterval3289 1) hlo hhi horder
  have hphase : ratRectRealCoordinateAbsBound3356
      (RatRect3276.powSq
        (ratPhaseRect3279 (record2680PhaseAngleRat3279 1 4)) 9) ≤ 1 := by
    unfold ratRectRealCoordinateAbsBound3356
    exact le_trans (le_max_left _ _)
      ratPhasePowSqEndpointAbsBound3409_cell1_family4_nine
  have hweight : (ratCellWeightInterval3289 1).hi ≤ 32 := by
    exact le_trans (le_abs_self _)
      (le_trans (le_max_right _ _)
        ratCellWeightIntervalEndpointAbsBound3377_cell1)
  calc
    _ ≤ 1 * (ratCellWeightInterval3289 1).hi := by
      exact le_trans hscale (mul_le_mul_of_nonneg_right hphase hhi)
    _ ≤ 32 := by simpa using hweight

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem ratWeightedPhaseRect_cell1_family4_imagAbs_le3410 :
    ratRectImagCoordinateAbsBound3391
      (ratWeightedPhaseRect3310 1 4) ≤ 32 := by
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
  have hbase : ratRectImagCoordinateAbsBound3391
      (RatRect3276.powSq
        (ratPhaseRect3279 (record2680PhaseAngleRat3279 1 4)) 9) ≤ 1 := by
    unfold ratRectImagCoordinateAbsBound3391
    exact le_trans (le_max_right _ _)
      ratPhasePowSqEndpointAbsBound3409_cell1_family4_nine
  have hlo' := ratRect_mul_real_imLo_ge_coordinate_bound3391
    (RatRect3276.powSq
      (ratPhaseRect3279 (record2680PhaseAngleRat3279 1 4)) 9)
    (ratCellWeightInterval3289 1) hlo hhi horder
  have hhi' := ratRect_mul_real_imHi_le_coordinate_bound3391
    (RatRect3276.powSq
      (ratPhaseRect3279 (record2680PhaseAngleRat3279 1 4)) 9)
    (ratCellWeightInterval3289 1) hlo hhi horder
  have hweight : (ratCellWeightInterval3289 1).hi ≤ 32 := by
    exact le_trans (le_abs_self _)
      (le_trans (le_max_right _ _)
        ratCellWeightIntervalEndpointAbsBound3377_cell1)
  have hphaseOrder :
      (ratWeightedPhaseRect3310 1 4).imLo ≤
        (ratWeightedPhaseRect3310 1 4).imHi := by
    have hactive : |record2680Center3212 1| <
        C1RouteAOwnerScaleAudit.storedWidth 4 ^ 2 := by
      have hq : |record2680CenterRat3279 1| < storedWidthRat3287 4 ^ 2 := by
        norm_num [record2680CenterRat3279, storedWidthRat3287,
          Matrix.cons_val_four]
      have hc := record2680CenterRat_cast3279 1
      have hr : ((storedWidthRat3287 4 ^ 2 : ℚ) : ℝ) =
          C1RouteAOwnerScaleAudit.storedWidth 4 ^ 2 := by
        norm_num [Rat.cast_pow, storedWidthRat_cast3287]
      rw [← hc, ← hr]
      exact_mod_cast hq
    have hm := ratWeightedPhaseRect_mem3310 (by norm_num) 4 hactive
    unfold RatRect3276.Mem RatRect3276.toReal ComplexRect2427.Mem at hm
    have hx := le_trans hm.2.2.1 hm.2.2.2
    change ((ratWeightedPhaseRect3310 1 4).imLo : ℝ) ≤
      (ratWeightedPhaseRect3310 1 4).imHi at hx
    exact_mod_cast hx
  have hprodOrder :
      (RatRect3276.mul
        (RatRect3276.powSq
          (ratPhaseRect3279 (record2680PhaseAngleRat3279 1 4)) 9)
        (ratRealRect3281 (ratCellWeightInterval3289 1))).imLo ≤
      (RatRect3276.mul
        (RatRect3276.powSq
          (ratPhaseRect3279 (record2680PhaseAngleRat3279 1 4)) 9)
        (ratRealRect3281 (ratCellWeightInterval3289 1))).imHi := by
    simpa [ratWeightedPhaseRect_orientation3361] using hphaseOrder
  have hbaseMul :
      ratRectImagCoordinateAbsBound3391
          (RatRect3276.powSq
            (ratPhaseRect3279 (record2680PhaseAngleRat3279 1 4)) 9) *
        (ratCellWeightInterval3289 1).hi ≤ 32 := by
    calc
      _ ≤ 1 * (ratCellWeightInterval3289 1).hi :=
        mul_le_mul_of_nonneg_right hbase hhi
      _ ≤ 32 := by simpa using hweight
  unfold ratRectImagCoordinateAbsBound3391
  apply max_le
  · apply (abs_le).2
    constructor
    · exact le_trans (neg_le_neg hbaseMul) hlo'
    · exact le_trans hprodOrder (hhi'.trans hbaseMul)
  · apply (abs_le).2
    constructor
    · exact le_trans (le_trans (neg_le_neg hbaseMul) hlo') hprodOrder
    · exact hhi'.trans hbaseMul

theorem ratWeightedPhaseRect_cell1_family4_ordered3410 :
    (ratWeightedPhaseRect3310 1 4).reLo ≤ (ratWeightedPhaseRect3310 1 4).reHi ∧
    (ratWeightedPhaseRect3310 1 4).imLo ≤ (ratWeightedPhaseRect3310 1 4).imHi := by
  have hactive : |record2680Center3212 1| < C1RouteAOwnerScaleAudit.storedWidth 4 ^ 2 := by
    have hq : |record2680CenterRat3279 1| < storedWidthRat3287 4 ^ 2 := by
      norm_num [record2680CenterRat3279, storedWidthRat3287, Matrix.cons_val_four]
    have hc := record2680CenterRat_cast3279 1
    have hr : ((storedWidthRat3287 4 ^ 2 : ℚ) : ℝ) = C1RouteAOwnerScaleAudit.storedWidth 4 ^ 2 := by
      norm_num [Rat.cast_pow, storedWidthRat_cast3287]
    rw [← hc, ← hr]
    exact_mod_cast hq
  have hm := ratWeightedPhaseRect_mem3310 (by norm_num) 4 hactive
  unfold RatRect3276.Mem RatRect3276.toReal ComplexRect2427.Mem at hm
  change ((ratWeightedPhaseRect3310 1 4).reLo : ℝ) ≤ _ ∧ _ ≤ ((ratWeightedPhaseRect3310 1 4).reHi : ℝ) ∧
    ((ratWeightedPhaseRect3310 1 4).imLo : ℝ) ≤ _ ∧ _ ≤ ((ratWeightedPhaseRect3310 1 4).imHi : ℝ) at hm
  constructor
  · exact_mod_cast le_trans hm.1 hm.2.1
  · exact_mod_cast le_trans hm.2.2.1 hm.2.2.2

end ConnesWeilRH.Dev






