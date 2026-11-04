import ConnesWeilRH.Dev.C1RouteARationalWeightedJetEndpoint3363
import ConnesWeilRH.Dev.C1RouteARationalWeightedJetEndpoint3365
import ConnesWeilRH.Dev.C1RouteARationalWeightedJetEndpoint3367
import ConnesWeilRH.Dev.C1RouteARationalComplexEndpointBounds3349
import ConnesWeilRH.Dev.C1RouteARationalWeightedPhaseEndpoint3362
import ConnesWeilRH.Dev.C1RouteARationalBumpEndpoint3347
import ConnesWeilRH.Dev.C1RouteARationalBumpSmallBound3355
import ConnesWeilRH.Dev.C1RouteARationalBumpSmallBound3364
import ConnesWeilRH.Dev.C1RouteARationalBumpSmallBound3366
import ConnesWeilRH.Dev.C1RouteARationalSignedJetRect3310
import ConnesWeilRH.Dev.C1RouteARationalImaginaryEndpointBudget3371

namespace ConnesWeilRH.Dev

theorem ratWeightedPhaseRect_cell0_family4_endpointAbs_le3372 :
    ratRectEndpointAbsBound3326 (ratWeightedPhaseRect3310 0 4) ≤ 128 := by
  rw [ratWeightedPhaseRect_orientation3361]
  have hweight :
      ratRectEndpointAbsBound3326
        (ratRealRect3281 (ratCellWeightInterval3289 0)) ≤ 32 := by
    unfold ratRectEndpointAbsBound3326 ratRealRect3281
    have h := ratCellWeightIntervalEndpointAbsBound3357_cell0
    change max (max |(ratCellWeightInterval3289 0).lo|
      |(ratCellWeightInterval3289 0).hi|) (max |(0 : ℚ)| |(0 : ℚ)|) ≤ 32
    exact max_le h (by norm_num)
  have hphasePow :
      ratRectEndpointAbsBound3326
        (RatRect3276.powSq
          (ratPhaseRect3279
            (record2680PhaseAngleRat3279 0 4)) 9) ≤ 2 := by
    exact ratPhasePowSqEndpointAbsBound3354_cell0_family4_nine
  calc
    ratRectEndpointAbsBound3326
        ((RatRect3276.powSq
          (ratPhaseRect3279
            (record2680PhaseAngleRat3279 0 4)) 9).mul
          (ratRealRect3281 (ratCellWeightInterval3289 0))) ≤
        2 * ratRectEndpointAbsBound3326
          (RatRect3276.powSq
            (ratPhaseRect3279
              (record2680PhaseAngleRat3279 0 4)) 9) *
          ratRectEndpointAbsBound3326
            (ratRealRect3281 (ratCellWeightInterval3289 0)) :=
      ratRect_mul_endpointAbsBound3349 _ _
    _ ≤ 2 * 2 * 32 := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hphasePow (by norm_num))
        hweight (ratRectEndpointAbsBound3326_nonneg _) (by norm_num)
    _ ≤ 128 := by norm_num

theorem ratWeightedBumpRect_endpointAbs_le_hi3372
    (order : ℕ)
    (hlo : (ratBumpJetInterval3310 order
      (storedWidthRat3287 4 ^ 2) (record2680CenterRat3279 0)).lo = 0)
    (hhi : 0 ≤ (ratBumpJetInterval3310 order
      (storedWidthRat3287 4 ^ 2) (record2680CenterRat3279 0)).hi) :
    ratRectEndpointAbsBound3326 (ratBumpRect3310 order 0 4) ≤
      (ratBumpJetInterval3310 order
        (storedWidthRat3287 4 ^ 2) (record2680CenterRat3279 0)).hi := by
  unfold ratRectEndpointAbsBound3326 ratBumpRect3310 ratRealRect3281
  rw [hlo, abs_of_nonneg hhi]
  simp [hhi]

set_option maxHeartbeats 10000000 in
theorem ratWeightedUnitJetRect_cell0_order2_index0_family4_endpointAbs_le3372 :
    ratRectEndpointAbsBound3326 (ratWeightedUnitJetRect3310 2 0 0 4) ≤
      3 / 10 ^ 14 := by
  have hphase := ratWeightedPhaseRect_cell0_family4_endpointAbs_le3372
  have hbumpLo : 0 ≤ (ratBumpJetInterval3310 2
      (storedWidthRat3287 4 ^ 2) (record2680CenterRat3279 0)).lo := by
    rw [signed_bump_endpoint3337_cell0_order2_family4_reLo_eq_zero]
  have hbumpHi : 0 ≤ (ratBumpJetInterval3310 2
      (storedWidthRat3287 4 ^ 2) (record2680CenterRat3279 0)).hi := by
    rw [signed_bump_endpoint3347_cell0_order2_family4_hi_eq]
    exact mul_nonneg (ratBaseInterval3284_powNat_hi_nonneg3344 188) (by
      norm_num [ratBumpNumerator3310, record2680CenterRat3279,
        storedWidthRat3287, Matrix.cons_val_four])
  have hbump := signed_bump_endpoint3355_cell0_order2_family4_hi_le
  have hbumpAbs := ratWeightedBumpRect_endpointAbs_le_hi3372 2
    (signed_bump_endpoint3337_cell0_order2_family4_reLo_eq_zero) hbumpHi
  have hbumpAbs' := le_trans hbumpAbs hbump
  have hscalar : ∀ a : RatRect3276,
      a.reLo ≤ a.reHi -> a.imLo ≤ a.imHi ->
      RatRect3276.mul (ratScalarRect3310 1) a = a := by
    intro a hRe hIm
    rcases a with ⟨reLo, reHi, imLo, imHi⟩
    simp [ratScalarRect3310, RatRect3276.mul, RatInterval3276.mul,
      RatInterval3276.sub, RatInterval3276.add, min_eq_left hRe,
      max_eq_right hRe, min_eq_left hIm, max_eq_right hIm]
  have hphaseOrder :
      (ratWeightedPhaseRect3310 0 4).reLo ≤
          (ratWeightedPhaseRect3310 0 4).reHi ∧
        (ratWeightedPhaseRect3310 0 4).imLo ≤
          (ratWeightedPhaseRect3310 0 4).imHi := by
    have hactive : |record2680Center3212 0| <
        C1RouteAOwnerScaleAudit.storedWidth 4 ^ 2 := by
      have hq : |record2680CenterRat3279 0| <
          storedWidthRat3287 4 ^ 2 := by
        norm_num [record2680CenterRat3279, storedWidthRat3287,
          Matrix.cons_val_four]
      have hcenter := record2680CenterRat_cast3279 0
      have hradius :
          ((storedWidthRat3287 4 ^ 2 : ℚ) : ℝ) =
            C1RouteAOwnerScaleAudit.storedWidth 4 ^ 2 := by
        norm_num [Rat.cast_pow, storedWidthRat_cast3287]
      rw [← hcenter, ← hradius]
      exact_mod_cast hq
    have hmem := ratWeightedPhaseRect_mem3310 (by norm_num) 4 hactive
    unfold RatRect3276.Mem RatRect3276.toReal ComplexRect2427.Mem at hmem
    change ((ratWeightedPhaseRect3310 0 4).reLo : ℝ) ≤ _ ∧
      _ ≤ ((ratWeightedPhaseRect3310 0 4).reHi : ℝ) ∧
      ((ratWeightedPhaseRect3310 0 4).imLo : ℝ) ≤ _ ∧
      _ ≤ ((ratWeightedPhaseRect3310 0 4).imHi : ℝ) at hmem
    constructor
    · exact_mod_cast le_trans hmem.1 hmem.2.1
    · exact_mod_cast le_trans hmem.2.2.1 hmem.2.2.2
  have hleft :
      RatRect3276.mul
          (ratScalarRect3310 (Nat.choose 2 0 : ℚ))
          (RatRect3276.mul
            (ratRectPowNat3310 (ratWeightedLambdaRect3310 4) 0)
            (ratWeightedPhaseRect3310 0 4)) =
        ratWeightedPhaseRect3310 0 4 := by
    rw [show (Nat.choose 2 0 : ℚ) = 1 by norm_num]
    rw [show ratRectPowNat3310 (ratWeightedLambdaRect3310 4) 0 =
      ratScalarRect3310 1 by rfl]
    rw [hscalar _ hphaseOrder.1 hphaseOrder.2]
    exact hscalar _ hphaseOrder.1 hphaseOrder.2
  rw [ratWeightedUnitJetRect3310, hleft]
  calc
    ratRectEndpointAbsBound3326
        (RatRect3276.mul (ratWeightedPhaseRect3310 0 4)
          (ratBumpRect3310 2 0 4)) ≤
        2 * ratRectEndpointAbsBound3326 (ratWeightedPhaseRect3310 0 4) *
          ratRectEndpointAbsBound3326 (ratBumpRect3310 2 0 4) :=
      ratRect_mul_endpointAbsBound3349 _ _
    _ ≤ 2 * 128 * (1 / 10 ^ 16) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hphase (by norm_num))
        hbumpAbs' (ratRectEndpointAbsBound3326_nonneg _) (by norm_num)
    _ ≤ 3 / 10 ^ 14 := by norm_num

set_option maxHeartbeats 10000000 in
theorem ratWeightedUnitJetRect_cell0_order2_index1_family4_endpointAbs_le3372 :
    ratRectEndpointAbsBound3326 (ratWeightedUnitJetRect3310 2 1 0 4) ≤
      1 / 10 ^ 25 := by
  have hphase := ratWeightedPhaseRect_cell0_family4_endpointAbs_le3372
  have hlambdaOrder :
      (ratWeightedLambdaRect3310 4).reLo ≤
          (ratWeightedLambdaRect3310 4).reHi ∧
        (ratWeightedLambdaRect3310 4).imLo ≤
          (ratWeightedLambdaRect3310 4).imHi := by
    norm_num [ratWeightedLambdaRect3310]
  have hscalarOne : ∀ a : RatRect3276,
      a.reLo ≤ a.reHi -> a.imLo ≤ a.imHi ->
      RatRect3276.mul (ratScalarRect3310 1) a = a := by
    intro a hRe hIm
    rcases a with ⟨reLo, reHi, imLo, imHi⟩
    simp [ratScalarRect3310, RatRect3276.mul, RatInterval3276.mul,
      RatInterval3276.sub, RatInterval3276.add, min_eq_left hRe,
      max_eq_right hRe, min_eq_left hIm, max_eq_right hIm]
  have hpow1 :
      ratRectPowNat3310 (ratWeightedLambdaRect3310 4) 1 =
        ratWeightedLambdaRect3310 4 := by
    rw [ratRectPowNat3310]
    exact hscalarOne _ hlambdaOrder.1 hlambdaOrder.2
  have hlambda : ratRectEndpointAbsBound3326
      (ratWeightedLambdaRect3310 4) ≤ 40 := by
    norm_num [ratRectEndpointAbsBound3326, ratWeightedLambdaRect3310,
      capturedModulationsRat3279, Matrix.cons_val_four]
  have hinner : ratRectEndpointAbsBound3326
      (RatRect3276.mul (ratWeightedLambdaRect3310 4)
        (ratWeightedPhaseRect3310 0 4)) ≤ 10240 := by
    calc
      _ ≤ 2 * ratRectEndpointAbsBound3326 (ratWeightedLambdaRect3310 4) *
          ratRectEndpointAbsBound3326 (ratWeightedPhaseRect3310 0 4) :=
        ratRect_mul_endpointAbsBound3349 _ _
      _ ≤ 2 * 40 * 128 := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hlambda (by norm_num)) hphase
          (ratRectEndpointAbsBound3326_nonneg _) (by norm_num)
      _ ≤ 10240 := by norm_num
  have hcore : ratRectEndpointAbsBound3326
      (RatRect3276.mul (ratScalarRect3310 2)
        (RatRect3276.mul (ratWeightedLambdaRect3310 4)
          (ratWeightedPhaseRect3310 0 4))) ≤ 65536 := by
    have hscalar : ratRectEndpointAbsBound3326 (ratScalarRect3310 2) = 2 := by
      norm_num [ratRectEndpointAbsBound3326, ratScalarRect3310]
    calc
      _ ≤ 2 * ratRectEndpointAbsBound3326 (ratScalarRect3310 2) *
          ratRectEndpointAbsBound3326
            (RatRect3276.mul (ratWeightedLambdaRect3310 4)
              (ratWeightedPhaseRect3310 0 4)) :=
        ratRect_mul_endpointAbsBound3349 _ _
      _ ≤ 2 * 2 * 10240 := by
        rw [hscalar]
        exact mul_le_mul_of_nonneg_left hinner (by norm_num)
      _ ≤ 65536 := by norm_num
  have hbumpHi : 0 ≤ (ratBumpJetInterval3310 1
      (storedWidthRat3287 4 ^ 2) (record2680CenterRat3279 0)).hi := by
    rw [signed_bump_endpoint3347_cell0_order1_family4_hi_eq]
    exact mul_nonneg (ratBaseInterval3284_powNat_hi_nonneg3344 188) (by
      norm_num [ratBumpNumerator3310, record2680CenterRat3279,
        storedWidthRat3287, Matrix.cons_val_four])
  have hbumpAbs := ratWeightedBumpRect_endpointAbs_le_hi3372 1
    (signed_bump_endpoint3340_cell0_order1_family4_reLo_eq_zero) hbumpHi
  have hbump :
      (ratBumpJetInterval3310 1
        (storedWidthRat3287 4 ^ 2) (record2680CenterRat3279 0)).hi ≤
      1 / 10 ^ 31 := signed_bump_endpoint3364_cell0_order1_family4_hi_le
  have hbumpAbs' := le_trans hbumpAbs hbump
  rw [ratWeightedUnitJetRect3310]
  rw [show (Nat.choose 2 1 : ℚ) = 2 by norm_num]
  rw [hpow1]
  rw [show 2 - 1 = 1 by norm_num]
  calc
    ratRectEndpointAbsBound3326
        (RatRect3276.mul
          (RatRect3276.mul (ratScalarRect3310 2)
            (RatRect3276.mul (ratWeightedLambdaRect3310 4)
              (ratWeightedPhaseRect3310 0 4)))
          (ratBumpRect3310 1 0 4)) ≤
        2 * 65536 * (1 / 10 ^ 31) := by
      calc
        ratRectEndpointAbsBound3326
            (RatRect3276.mul
              (RatRect3276.mul (ratScalarRect3310 2)
                (RatRect3276.mul (ratWeightedLambdaRect3310 4)
                  (ratWeightedPhaseRect3310 0 4)))
              (ratBumpRect3310 1 0 4)) ≤
            2 * ratRectEndpointAbsBound3326
              (RatRect3276.mul (ratScalarRect3310 2)
                (RatRect3276.mul (ratWeightedLambdaRect3310 4)
                  (ratWeightedPhaseRect3310 0 4))) *
              ratRectEndpointAbsBound3326 (ratBumpRect3310 1 0 4) :=
          ratRect_mul_endpointAbsBound3349 _ _
        _ ≤ 2 * 65536 * (1 / 10 ^ 31) := by
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left hcore (by norm_num))
            hbumpAbs' (ratRectEndpointAbsBound3326_nonneg _) (by norm_num)
    _ ≤ 1 / 10 ^ 25 := by norm_num

set_option maxHeartbeats 10000000 in
theorem ratWeightedUnitJetRect_cell0_order2_index2_family4_endpointAbs_le3372 :
    ratRectEndpointAbsBound3326 (ratWeightedUnitJetRect3310 2 2 0 4) ≤
      1 / 10 ^ 33 := by
  have hphase := ratWeightedPhaseRect_cell0_family4_endpointAbs_le3372
  have hlambda : ratRectEndpointAbsBound3326
      (ratWeightedLambdaRect3310 4) ≤ 40 := by
    norm_num [ratRectEndpointAbsBound3326, ratWeightedLambdaRect3310,
      capturedModulationsRat3279, Matrix.cons_val_four]
  have hlambdaSq : ratRectEndpointAbsBound3326
      (RatRect3276.mul (ratWeightedLambdaRect3310 4)
        (ratWeightedLambdaRect3310 4)) ≤ 3200 := by
    calc
      _ ≤ 2 * ratRectEndpointAbsBound3326 (ratWeightedLambdaRect3310 4) *
          ratRectEndpointAbsBound3326 (ratWeightedLambdaRect3310 4) :=
        ratRect_mul_endpointAbsBound3349 _ _
      _ ≤ 2 * 40 * 40 := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hlambda (by norm_num)) hlambda
          (ratRectEndpointAbsBound3326_nonneg _) (by norm_num)
      _ ≤ 3200 := by norm_num
  have hinner : ratRectEndpointAbsBound3326
      (RatRect3276.mul
        (RatRect3276.mul (ratWeightedLambdaRect3310 4)
          (ratWeightedLambdaRect3310 4))
        (ratWeightedPhaseRect3310 0 4)) ≤ 819200 := by
    calc
      _ ≤ 2 * ratRectEndpointAbsBound3326
          (RatRect3276.mul (ratWeightedLambdaRect3310 4)
            (ratWeightedLambdaRect3310 4)) *
          ratRectEndpointAbsBound3326 (ratWeightedPhaseRect3310 0 4) :=
        ratRect_mul_endpointAbsBound3349 _ _
      _ ≤ 2 * 3200 * 128 := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hlambdaSq (by norm_num)) hphase
          (ratRectEndpointAbsBound3326_nonneg _) (by norm_num)
      _ ≤ 819200 := by norm_num
  have hcore : ratRectEndpointAbsBound3326
      (RatRect3276.mul (ratScalarRect3310 1)
        (RatRect3276.mul
          (RatRect3276.mul (ratWeightedLambdaRect3310 4)
            (ratWeightedLambdaRect3310 4))
          (ratWeightedPhaseRect3310 0 4))) ≤ 2097152 := by
    have hscalar : ratRectEndpointAbsBound3326 (ratScalarRect3310 1) = 1 := by
      norm_num [ratRectEndpointAbsBound3326, ratScalarRect3310]
    calc
      _ ≤ 2 * ratRectEndpointAbsBound3326 (ratScalarRect3310 1) *
          ratRectEndpointAbsBound3326
            (RatRect3276.mul
              (RatRect3276.mul (ratWeightedLambdaRect3310 4)
                (ratWeightedLambdaRect3310 4))
              (ratWeightedPhaseRect3310 0 4)) :=
        ratRect_mul_endpointAbsBound3349 _ _
      _ ≤ 2 * 1 * 819200 := by
        rw [hscalar]
        exact mul_le_mul_of_nonneg_left hinner (by norm_num)
      _ ≤ 2097152 := by norm_num
  have hbumpHi : 0 ≤ (ratBumpJetInterval3310 0
      (storedWidthRat3287 4 ^ 2) (record2680CenterRat3279 0)).hi := by
    rw [signed_bump_endpoint3347_cell0_order0_family4_hi_eq]
    exact ratBaseInterval3284_powNat_hi_nonneg3344 188
  have hbumpAbs := ratWeightedBumpRect_endpointAbs_le_hi3372 0
    (signed_bump_endpoint3339_cell0_order0_family4_reLo_eq_zero) hbumpHi
  have hbump :
      (ratBumpJetInterval3310 0
        (storedWidthRat3287 4 ^ 2) (record2680CenterRat3279 0)).hi ≤
      1 / 10 ^ 40 := signed_bump_endpoint3366_cell0_order0_family4_hi_le
  have hbumpAbs' := le_trans hbumpAbs hbump
  have hlambdaOrder :
      (ratWeightedLambdaRect3310 4).reLo ≤
          (ratWeightedLambdaRect3310 4).reHi ∧
        (ratWeightedLambdaRect3310 4).imLo ≤
          (ratWeightedLambdaRect3310 4).imHi := by
    norm_num [ratWeightedLambdaRect3310]
  have hscalarOne : ∀ a : RatRect3276,
      a.reLo ≤ a.reHi -> a.imLo ≤ a.imHi ->
      RatRect3276.mul (ratScalarRect3310 1) a = a := by
    intro a hRe hIm
    rcases a with ⟨reLo, reHi, imLo, imHi⟩
    simp [ratScalarRect3310, RatRect3276.mul, RatInterval3276.mul,
      RatInterval3276.sub, RatInterval3276.add, min_eq_left hRe,
      max_eq_right hRe, min_eq_left hIm, max_eq_right hIm]
  have hpow1 :
      ratRectPowNat3310 (ratWeightedLambdaRect3310 4) 1 =
        ratWeightedLambdaRect3310 4 := by
    rw [ratRectPowNat3310]
    exact hscalarOne _ hlambdaOrder.1 hlambdaOrder.2
  rw [ratWeightedUnitJetRect3310]
  rw [show (Nat.choose 2 2 : ℚ) = 1 by norm_num]
  rw [show ratRectPowNat3310 (ratWeightedLambdaRect3310 4) 2 =
    RatRect3276.mul (ratWeightedLambdaRect3310 4)
      (ratWeightedLambdaRect3310 4) by
        rw [ratRectPowNat3310, hpow1]]
  calc
    ratRectEndpointAbsBound3326
        (RatRect3276.mul
          (RatRect3276.mul (ratScalarRect3310 1)
            (RatRect3276.mul
              (RatRect3276.mul (ratWeightedLambdaRect3310 4)
                (ratWeightedLambdaRect3310 4))
              (ratWeightedPhaseRect3310 0 4)))
          (ratBumpRect3310 0 0 4)) ≤
        2 * 2097152 * (1 / 10 ^ 40) := by
      calc
        _ ≤ 2 * ratRectEndpointAbsBound3326
            (RatRect3276.mul (ratScalarRect3310 1)
              (RatRect3276.mul
                (RatRect3276.mul (ratWeightedLambdaRect3310 4)
                  (ratWeightedLambdaRect3310 4))
                (ratWeightedPhaseRect3310 0 4))) *
            ratRectEndpointAbsBound3326 (ratBumpRect3310 0 0 4) :=
          ratRect_mul_endpointAbsBound3349 _ _
        _ ≤ 2 * 2097152 * (1 / 10 ^ 40) := by
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left hcore (by norm_num))
            hbumpAbs' (ratRectEndpointAbsBound3326_nonneg _) (by norm_num)
    _ ≤ 1 / 10 ^ 33 := by norm_num

theorem ratWeightedUnitJetSumRect_cell0_order2_family4_endpointAbs_le3372 :
    ratRectEndpointAbsBound3326
      (RatRect3276.add
        (RatRect3276.add
          (ratWeightedUnitJetRect3310 2 0 0 4)
          (ratWeightedUnitJetRect3310 2 1 0 4))
        (ratWeightedUnitJetRect3310 2 2 0 4)) ≤
      31 / 10 ^ 15 := by
  calc
    _ ≤ ratRectEndpointAbsBound3326 (ratWeightedUnitJetRect3310 2 0 0 4) +
        ratRectEndpointAbsBound3326 (ratWeightedUnitJetRect3310 2 1 0 4) +
        ratRectEndpointAbsBound3326 (ratWeightedUnitJetRect3310 2 2 0 4) := by
      exact le_trans
        (ratRect_add_endpointAbsBound_le_sum3328
          (RatRect3276.add
            (ratWeightedUnitJetRect3310 2 0 0 4)
            (ratWeightedUnitJetRect3310 2 1 0 4))
          (ratWeightedUnitJetRect3310 2 2 0 4))
        (add_le_add
          (ratRect_add_endpointAbsBound_le_sum3328 _ _)
          (le_refl _))
    _ ≤ 3 / 10 ^ 14 + 1 / 10 ^ 25 + 1 / 10 ^ 33 := by
      exact add_le_add (add_le_add
        ratWeightedUnitJetRect_cell0_order2_index0_family4_endpointAbs_le3372
        ratWeightedUnitJetRect_cell0_order2_index1_family4_endpointAbs_le3372)
        ratWeightedUnitJetRect_cell0_order2_index2_family4_endpointAbs_le3372
    _ ≤ 31 / 10 ^ 15 := by norm_num

end ConnesWeilRH.Dev
