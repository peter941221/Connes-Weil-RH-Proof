import ConnesWeilRH.Dev.C1RouteARationalWeightedPhaseTightBounds3410
import ConnesWeilRH.Dev.C1RouteARationalWeightedPhaseOrientation3361
import ConnesWeilRH.Dev.C1RouteARationalBumpTightEndpoint3423
import ConnesWeilRH.Dev.C1RouteARationalBumpEndpoint3347
import ConnesWeilRH.Dev.C1RouteARationalRealScalingSignedBounds3391

namespace ConnesWeilRH.Dev

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem signed_coordinate_jet_endpoint3424_cell1_order2_index0_family4_reLo_ge :
    -(32 / 10 ^ 18 : ℚ) ≤ (ratWeightedUnitJetRect3310 2 0 1 4).reLo := by
  have hphaseOrder :
      (ratWeightedPhaseRect3310 1 4).reLo ≤
          (ratWeightedPhaseRect3310 1 4).reHi ∧
        (ratWeightedPhaseRect3310 1 4).imLo ≤
          (ratWeightedPhaseRect3310 1 4).imHi := by
    have hactive : |record2680Center3212 1| <
        C1RouteAOwnerScaleAudit.storedWidth 4 ^ 2 := by
      have hq : |record2680CenterRat3279 1| < storedWidthRat3287 4 ^ 2 := by
        norm_num [record2680CenterRat3279, storedWidthRat3287, Matrix.cons_val_four]
      have hc := record2680CenterRat_cast3279 1
      have hr : ((storedWidthRat3287 4 ^ 2 : ℚ) : ℝ) =
          C1RouteAOwnerScaleAudit.storedWidth 4 ^ 2 := by
        norm_num [Rat.cast_pow, storedWidthRat_cast3287]
      rw [← hc, ← hr]
      exact_mod_cast hq
    have hm := ratWeightedPhaseRect_mem3310 (by norm_num) 4 hactive
    unfold RatRect3276.Mem RatRect3276.toReal ComplexRect2427.Mem at hm
    change ((ratWeightedPhaseRect3310 1 4).reLo : ℝ) ≤ _ ∧
      _ ≤ ((ratWeightedPhaseRect3310 1 4).reHi : ℝ) ∧
      ((ratWeightedPhaseRect3310 1 4).imLo : ℝ) ≤ _ ∧
      _ ≤ ((ratWeightedPhaseRect3310 1 4).imHi : ℝ) at hm
    constructor
    · exact_mod_cast le_trans hm.1 hm.2.1
    · exact_mod_cast le_trans hm.2.2.1 hm.2.2.2
  have hscalar : ∀ a : RatRect3276,
      a.reLo ≤ a.reHi -> a.imLo ≤ a.imHi ->
      RatRect3276.mul (ratScalarRect3310 1) a = a := by
    intro a hRe hIm
    rcases a with ⟨reLo, reHi, imLo, imHi⟩
    simp [ratScalarRect3310, RatRect3276.mul, RatInterval3276.mul,
      RatInterval3276.sub, RatInterval3276.add, min_eq_left hRe,
      max_eq_right hRe, min_eq_left hIm, max_eq_right hIm]
  have hleft :
      RatRect3276.mul (ratScalarRect3310 (Nat.choose 2 0 : ℚ))
          (RatRect3276.mul
            (ratRectPowNat3310 (ratWeightedLambdaRect3310 4) 0)
            (ratWeightedPhaseRect3310 1 4)) =
        ratWeightedPhaseRect3310 1 4 := by
    rw [show (Nat.choose 2 0 : ℚ) = 1 by norm_num]
    rw [show ratRectPowNat3310 (ratWeightedLambdaRect3310 4) 0 =
      ratScalarRect3310 1 by rfl]
    rw [hscalar _ hphaseOrder.1 hphaseOrder.2]
    exact hscalar _ hphaseOrder.1 hphaseOrder.2
  rw [ratWeightedUnitJetRect3310, hleft]
  have hbumpLo : 0 ≤ (ratBumpJetInterval3310 2
      (storedWidthRat3287 4 ^ 2) (record2680CenterRat3279 1)).lo := by
    rw [signed_bump_endpoint3380_cell1_order2_family4_reLo_eq_zero]
  have hbumpHi : 0 ≤ (ratBumpJetInterval3310 2
      (storedWidthRat3287 4 ^ 2) (record2680CenterRat3279 1)).hi := by
    rw [signed_bump_endpoint3380_cell1_order2_family4_hi_eq]
    exact mul_nonneg (ratBaseInterval3284_powNat_hi_nonneg3344 188) (by
      norm_num [ratBumpNumerator3310, record2680CenterRat3279,
        storedWidthRat3287, Matrix.cons_val_four])
  have hbumpOrder :
      (ratBumpJetInterval3310 2 (storedWidthRat3287 4 ^ 2)
        (record2680CenterRat3279 1)).lo ≤
      (ratBumpJetInterval3310 2 (storedWidthRat3287 4 ^ 2)
        (record2680CenterRat3279 1)).hi := by
    rw [signed_bump_endpoint3380_cell1_order2_family4_reLo_eq_zero]
    exact hbumpHi
  have hphase := ratWeightedPhaseRect_cell1_family4_realAbs_le3410
  have hbump := signed_bump_endpoint_cell1_order2_family4_hi_le3423
  have hbridge := ratRect_mul_real_reLo_ge_coordinate_bound3391
    (ratWeightedPhaseRect3310 1 4)
    (ratBumpJetInterval3310 2 (storedWidthRat3287 4 ^ 2)
      (record2680CenterRat3279 1)) hbumpLo hbumpHi hbumpOrder
  calc
    -(32 / 10 ^ 18 : ℚ) ≤ -(32 : ℚ) *
        (ratBumpJetInterval3310 2 (storedWidthRat3287 4 ^ 2)
          (record2680CenterRat3279 1)).hi := by
      nlinarith [hphase, hbumpHi, hbump]
    _ ≤ -(ratRectRealCoordinateAbsBound3356 (ratWeightedPhaseRect3310 1 4) *
        (ratBumpJetInterval3310 2 (storedWidthRat3287 4 ^ 2)
          (record2680CenterRat3279 1)).hi) := by nlinarith
    _ ≤ (RatRect3276.mul (ratWeightedPhaseRect3310 1 4)
        (ratBumpRect3310 2 1 4)).reLo := by simpa [ratBumpRect3310] using hbridge

end ConnesWeilRH.Dev

