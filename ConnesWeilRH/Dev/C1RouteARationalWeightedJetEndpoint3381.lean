import ConnesWeilRH.Dev.C1RouteARationalWeightedPhaseEndpoint3379
import ConnesWeilRH.Dev.C1RouteARationalBumpEndpoint3380
import ConnesWeilRH.Dev.C1RouteARationalBumpEndpoint3347

namespace ConnesWeilRH.Dev

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem signed_jet_endpoint3381_cell1_order2_index0_family4_reHi_le :
    (ratWeightedUnitJetRect3310 2 0 1 4).reHi ≤ 64 / 10 ^ 16 := by
  have hphaseOrder :
      (ratWeightedPhaseRect3310 1 4).reLo ≤
          (ratWeightedPhaseRect3310 1 4).reHi ∧
        (ratWeightedPhaseRect3310 1 4).imLo ≤
          (ratWeightedPhaseRect3310 1 4).imHi := by
    have hactive : |record2680Center3212 1| <
        C1RouteAOwnerScaleAudit.storedWidth 4 ^ 2 := by
      have hq : |record2680CenterRat3279 1| <
          storedWidthRat3287 4 ^ 2 := by
        norm_num [record2680CenterRat3279, storedWidthRat3287,
          Matrix.cons_val_four]
      have hcenter := record2680CenterRat_cast3279 1
      have hradius :
          ((storedWidthRat3287 4 ^ 2 : ℚ) : ℝ) =
            C1RouteAOwnerScaleAudit.storedWidth 4 ^ 2 := by
        norm_num [Rat.cast_pow, storedWidthRat_cast3287]
      rw [← hcenter, ← hradius]
      exact_mod_cast hq
    have hmem := ratWeightedPhaseRect_mem3310 (by norm_num) 4 hactive
    unfold RatRect3276.Mem RatRect3276.toReal ComplexRect2427.Mem at hmem
    change ((ratWeightedPhaseRect3310 1 4).reLo : ℝ) ≤ _ ∧
      _ ≤ ((ratWeightedPhaseRect3310 1 4).reHi : ℝ) ∧
      ((ratWeightedPhaseRect3310 1 4).imLo : ℝ) ≤ _ ∧
      _ ≤ ((ratWeightedPhaseRect3310 1 4).imHi : ℝ) at hmem
    constructor
    · exact_mod_cast le_trans hmem.1 hmem.2.1
    · exact_mod_cast le_trans hmem.2.2.1 hmem.2.2.2
  have hscalar : ∀ a : RatRect3276,
      a.reLo ≤ a.reHi -> a.imLo ≤ a.imHi ->
      RatRect3276.mul (ratScalarRect3310 1) a = a := by
    intro a hRe hIm
    rcases a with ⟨reLo, reHi, imLo, imHi⟩
    simp [ratScalarRect3310, RatRect3276.mul, RatInterval3276.mul,
      RatInterval3276.sub, RatInterval3276.add, min_eq_left hRe,
      max_eq_right hRe, min_eq_left hIm, max_eq_right hIm]
  have hleft :
      RatRect3276.mul
          (ratScalarRect3310 (Nat.choose 2 0 : ℚ))
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
      (ratBumpJetInterval3310 2
        (storedWidthRat3287 4 ^ 2) (record2680CenterRat3279 1)).lo ≤
      (ratBumpJetInterval3310 2
        (storedWidthRat3287 4 ^ 2) (record2680CenterRat3279 1)).hi := by
    rw [signed_bump_endpoint3380_cell1_order2_family4_reLo_eq_zero]
    exact hbumpHi
  have hphase :
      ratRectRealCoordinateAbsBound3356 (ratWeightedPhaseRect3310 1 4) ≤ 64 := by
    exact ratWeightedPhaseRect_cell1_family4_realAbs_le3379
  have hbump :
      (ratBumpJetInterval3310 2
        (storedWidthRat3287 4 ^ 2) (record2680CenterRat3279 1)).hi ≤
      1 / 10 ^ 16 := signed_bump_endpoint3380_cell1_order2_family4_hi_le
  calc
    (RatRect3276.mul (ratWeightedPhaseRect3310 1 4)
        (ratBumpRect3310 2 1 4)).reHi ≤
        ratRectRealCoordinateAbsBound3356 (ratWeightedPhaseRect3310 1 4) *
          (ratBumpJetInterval3310 2
            (storedWidthRat3287 4 ^ 2) (record2680CenterRat3279 1)).hi := by
      exact ratRect_mul_real_hi_le_coordinate_bound3358
        (ratWeightedPhaseRect3310 1 4)
        (ratBumpJetInterval3310 2
          (storedWidthRat3287 4 ^ 2) (record2680CenterRat3279 1))
        hbumpLo hbumpHi hbumpOrder
    _ ≤ 64 * (1 / 10 ^ 16) := by
      exact mul_le_mul hphase hbump hbumpHi (by norm_num)
    _ ≤ 64 / 10 ^ 16 := by norm_num

end ConnesWeilRH.Dev
