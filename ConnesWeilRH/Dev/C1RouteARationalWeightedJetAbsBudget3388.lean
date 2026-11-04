import ConnesWeilRH.Dev.C1RouteARationalWeightedPhaseEndpoint3379
import ConnesWeilRH.Dev.C1RouteARationalBumpEndpoint3382
import ConnesWeilRH.Dev.C1RouteARationalBumpSmallBound3384
import ConnesWeilRH.Dev.C1RouteARationalComplexEndpointBounds3349
import ConnesWeilRH.Dev.C1RouteARationalWeightedJetSumEndpoint3386
import ConnesWeilRH.Dev.C1RouteARationalWeightedJetEndpoint3383
import ConnesWeilRH.Dev.C1RouteARationalWeightedJetEndpoint3385

namespace ConnesWeilRH.Dev

theorem ratWeightedPhaseRect_cell1_family4_endpointAbs_le3388 :
    ratRectEndpointAbsBound3326 (ratWeightedPhaseRect3310 1 4) ≤ 128 := by
  rw [ratWeightedPhaseRect_orientation3361]
  have hweight :
      ratRectEndpointAbsBound3326
        (ratRealRect3281 (ratCellWeightInterval3289 1)) ≤ 32 := by
    unfold ratRectEndpointAbsBound3326 ratRealRect3281
    have h := ratCellWeightIntervalEndpointAbsBound3377_cell1
    change max (max |(ratCellWeightInterval3289 1).lo|
      |(ratCellWeightInterval3289 1).hi|) (max |(0 : ℚ)| |(0 : ℚ)|) ≤ 32
    exact max_le h (by norm_num)
  have hphasePow :
      ratRectEndpointAbsBound3326
        (RatRect3276.powSq
          (ratPhaseRect3279
            (record2680PhaseAngleRat3279 1 4)) 9) ≤ 2 :=
    ratPhasePowSqEndpointAbsBound3378_cell1_family4_nine
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
            (ratRealRect3281 (ratCellWeightInterval3289 1)) :=
      ratRect_mul_endpointAbsBound3349 _ _
    _ ≤ 2 * 2 * 32 := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hphasePow (by norm_num))
        hweight (ratRectEndpointAbsBound3326_nonneg _) (by norm_num)
    _ ≤ 128 := by norm_num

theorem ratWeightedBumpRect_endpointAbs_le_hi3388
    (order : ℕ)
    (hlo : (ratBumpJetInterval3310 order
      (storedWidthRat3287 4 ^ 2) (record2680CenterRat3279 1)).lo = 0)
    (hhi : 0 ≤ (ratBumpJetInterval3310 order
      (storedWidthRat3287 4 ^ 2) (record2680CenterRat3279 1)).hi) :
    ratRectEndpointAbsBound3326 (ratBumpRect3310 order 1 4) ≤
      (ratBumpJetInterval3310 order
        (storedWidthRat3287 4 ^ 2) (record2680CenterRat3279 1)).hi := by
  unfold ratRectEndpointAbsBound3326 ratBumpRect3310 ratRealRect3281
  rw [hlo, abs_of_nonneg hhi]
  simp [hhi]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem ratWeightedUnitJetRect_cell1_order2_index0_family4_endpointAbs_le3388 :
    ratRectEndpointAbsBound3326 (ratWeightedUnitJetRect3310 2 0 1 4) ≤
      26 / 10 ^ 15 := by
  have hphaseBound :
      ratRectEndpointAbsBound3326 (ratWeightedPhaseRect3310 1 4) ≤ 128 :=
    ratWeightedPhaseRect_cell1_family4_endpointAbs_le3388
  have hbumpHi : 0 ≤ (ratBumpJetInterval3310 2
      (storedWidthRat3287 4 ^ 2) (record2680CenterRat3279 1)).hi := by
    rw [signed_bump_endpoint3380_cell1_order2_family4_hi_eq]
    exact mul_nonneg (ratBaseInterval3284_powNat_hi_nonneg3344 188) (by
      norm_num [ratBumpNumerator3310, record2680CenterRat3279,
        storedWidthRat3287, Matrix.cons_val_four])
  have hbump := ratWeightedBumpRect_endpointAbs_le_hi3388 2
    (signed_bump_endpoint3380_cell1_order2_family4_reLo_eq_zero) hbumpHi
  have hbump' := le_trans hbump
    (signed_bump_endpoint3380_cell1_order2_family4_hi_le)
  have hbumpHiSmall := signed_bump_endpoint3380_cell1_order2_family4_hi_le
  have hscalar : ratRectEndpointAbsBound3326 (ratScalarRect3310 1) = 1 := by
    norm_num [ratRectEndpointAbsBound3326, ratScalarRect3310]
  have hphaseOrder :
      (ratWeightedPhaseRect3310 1 4).reLo ≤
          (ratWeightedPhaseRect3310 1 4).reHi ∧
        (ratWeightedPhaseRect3310 1 4).imLo ≤
          (ratWeightedPhaseRect3310 1 4).imHi := by
    rw [ratWeightedPhaseRect_orientation3361]
    norm_num [RatRect3276.mul, RatInterval3276.mul, RatInterval3276.sub,
      RatInterval3276.add, ratRealRect3281, ratCellWeightInterval3289,
      ratPhaseRect3279, record2680PhaseAngleRat3279,
      record2680CenterRat3279, storedWidthRat3287, Matrix.cons_val_four]
  have hscalarOne : ∀ a : RatRect3276,
      a.reLo ≤ a.reHi -> a.imLo ≤ a.imHi ->
      RatRect3276.mul (ratScalarRect3310 1) a = a := by
    intro a hRe hIm
    rcases a with ⟨reLo, reHi, imLo, imHi⟩
    simp [ratScalarRect3310, RatRect3276.mul, RatInterval3276.mul,
      RatInterval3276.sub, RatInterval3276.add, min_eq_left hRe,
      max_eq_right hRe, min_eq_left hIm, max_eq_right hIm]
  have hscalarPhase :
      RatRect3276.mul (ratScalarRect3310 1)
        (ratWeightedPhaseRect3310 1 4) = ratWeightedPhaseRect3310 1 4 :=
    hscalarOne _ hphaseOrder.1 hphaseOrder.2
  have hinner : ratRectEndpointAbsBound3326
      (RatRect3276.mul (ratScalarRect3310 1)
        (ratWeightedPhaseRect3310 1 4)) ≤ 128 := by
    rw [hscalarPhase]
    exact hphaseBound
  have hcore : ratRectEndpointAbsBound3326
      (RatRect3276.mul
        (ratScalarRect3310 1)
        (RatRect3276.mul (ratScalarRect3310 1)
          (ratWeightedPhaseRect3310 1 4))) ≤ 128 := by
    rw [hscalarPhase, hscalarPhase]
    exact hphaseBound
  rw [ratWeightedUnitJetRect3310]
  rw [show (Nat.choose 2 0 : ℚ) = 1 by norm_num]
  rw [show ratRectPowNat3310 (ratWeightedLambdaRect3310 4) 0 =
    ratScalarRect3310 1 by rfl]
  calc
    ratRectEndpointAbsBound3326
        (RatRect3276.mul
          (RatRect3276.mul
            (ratScalarRect3310 1)
            (RatRect3276.mul
              (ratScalarRect3310 1)
              (ratWeightedPhaseRect3310 1 4)))
          (ratBumpRect3310 2 1 4)) ≤
        2 * 128 * ratRectEndpointAbsBound3326
          (ratBumpRect3310 2 1 4) := by
      exact le_trans (ratRect_mul_endpointAbsBound3349 _ _)
        (by
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left hcore (by norm_num))
            (le_refl _) (ratRectEndpointAbsBound3326_nonneg _) (by norm_num))
    _ ≤ 2 * 128 * (ratBumpJetInterval3310 2
          (storedWidthRat3287 4 ^ 2) (record2680CenterRat3279 1)).hi := by
      exact mul_le_mul_of_nonneg_left hbump (by norm_num)
    _ ≤ 2 * 128 * (1 / 10 ^ 16) := by
      exact mul_le_mul_of_nonneg_left hbumpHiSmall (by norm_num)
    _ ≤ 26 / 10 ^ 15 := by norm_num

theorem ratWeightedUnitJetSumRect_cell1_order2_family4_endpointAbs_le3388 :
    ratRectEndpointAbsBound3326
      (ratWeightedJetSumRect_cell1_order2_family4_3386) ≤
      27 / 10 ^ 15 := by
  have h0 := ratWeightedUnitJetRect_cell1_order2_index0_family4_endpointAbs_le3388
  have hphaseBound :
      ratRectEndpointAbsBound3326 (ratWeightedPhaseRect3310 1 4) ≤ 128 :=
    ratWeightedPhaseRect_cell1_family4_endpointAbs_le3388
  have h1 : ratRectEndpointAbsBound3326
      (ratWeightedUnitJetRect3310 2 1 1 4) ≤ 1 / 10 ^ 25 := by
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
    have hpow1 : ratRectPowNat3310 (ratWeightedLambdaRect3310 4) 1 =
        ratWeightedLambdaRect3310 4 := by
      rw [ratRectPowNat3310]
      exact hscalarOne _ hlambdaOrder.1 hlambdaOrder.2
    have hlambda : ratRectEndpointAbsBound3326
        (ratWeightedLambdaRect3310 4) ≤ 40 := by
      norm_num [ratRectEndpointAbsBound3326, ratWeightedLambdaRect3310,
        capturedModulationsRat3279, Matrix.cons_val_four]
    have hinner : ratRectEndpointAbsBound3326
        (RatRect3276.mul (ratWeightedLambdaRect3310 4)
          (ratWeightedPhaseRect3310 1 4)) ≤ 10240 := by
      calc
        _ ≤ 2 * ratRectEndpointAbsBound3326 (ratWeightedLambdaRect3310 4) *
            ratRectEndpointAbsBound3326 (ratWeightedPhaseRect3310 1 4) :=
          ratRect_mul_endpointAbsBound3349 _ _
        _ ≤ 2 * 40 * 128 := by
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left hlambda (by norm_num)) hphaseBound
            (ratRectEndpointAbsBound3326_nonneg _) (by norm_num)
        _ ≤ 10240 := by norm_num
    have hscalar2 : ratRectEndpointAbsBound3326 (ratScalarRect3310 2) = 2 := by
      norm_num [ratRectEndpointAbsBound3326, ratScalarRect3310]
    have hcore : ratRectEndpointAbsBound3326
        (RatRect3276.mul (ratScalarRect3310 2)
          (RatRect3276.mul (ratWeightedLambdaRect3310 4)
            (ratWeightedPhaseRect3310 1 4))) ≤ 65536 := by
      calc
        _ ≤ 2 * ratRectEndpointAbsBound3326 (ratScalarRect3310 2) *
            ratRectEndpointAbsBound3326
              (RatRect3276.mul (ratWeightedLambdaRect3310 4)
                (ratWeightedPhaseRect3310 1 4)) :=
          ratRect_mul_endpointAbsBound3349 _ _
        _ ≤ 2 * 2 * 10240 := by
          rw [hscalar2]
          exact mul_le_mul_of_nonneg_left hinner (by norm_num)
        _ ≤ 65536 := by norm_num
    have hbumpHi : 0 ≤ (ratBumpJetInterval3310 1
        (storedWidthRat3287 4 ^ 2) (record2680CenterRat3279 1)).hi := by
      rw [signed_bump_endpoint3382_cell1_order1_family4_hi_eq]
      exact mul_nonneg (ratBaseInterval3284_powNat_hi_nonneg3344 188) (by
        norm_num [ratBumpNumerator3310, record2680CenterRat3279,
          storedWidthRat3287, Matrix.cons_val_four])
    have hbump := ratWeightedBumpRect_endpointAbs_le_hi3388 1
      (signed_bump_endpoint3382_cell1_order1_family4_reLo_eq_zero) hbumpHi
    have hbumpHiSmall :
        (ratBumpJetInterval3310 1 (storedWidthRat3287 4 ^ 2)
          (record2680CenterRat3279 1)).hi ≤ 1 / 10 ^ 31 := by
      rw [signed_bump_endpoint3382_cell1_order1_family4_hi_eq]
      rw [ratBaseInterval3284_powNat_hi_eq_pow3346]
      norm_num (config := { maxSteps := 2000000000 }) [
        ratBaseInterval3284, ratTaylorInterval3283, ratTaylorSum3283,
        ratTaylorError3283, storedWidthRat3287, record2680CenterRat3279,
        ratBumpNumerator3310, Matrix.cons_val_four]
    rw [ratWeightedUnitJetRect3310]
    rw [show (Nat.choose 2 1 : ℚ) = 2 by norm_num]
    rw [hpow1]
    have hmul := ratRect_mul_endpointAbsBound3349
      (RatRect3276.mul (ratScalarRect3310 2)
        (RatRect3276.mul (ratWeightedLambdaRect3310 4)
          (ratWeightedPhaseRect3310 1 4)))
      (ratBumpRect3310 1 1 4)
    calc
      _ ≤ 2 * 65536 * ratRectEndpointAbsBound3326
          (ratBumpRect3310 1 1 4) := by
        calc
          _ ≤ 2 * ratRectEndpointAbsBound3326
              (RatRect3276.mul (ratScalarRect3310 2)
                (RatRect3276.mul (ratWeightedLambdaRect3310 4)
                  (ratWeightedPhaseRect3310 1 4))) *
              ratRectEndpointAbsBound3326 (ratBumpRect3310 1 1 4) := hmul
          _ ≤ 2 * 65536 * ratRectEndpointAbsBound3326
              (ratBumpRect3310 1 1 4) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hcore (by norm_num))
              (ratRectEndpointAbsBound3326_nonneg _)
      _ ≤ 2 * 65536 * (1 / 10 ^ 31) := by
        exact mul_le_mul_of_nonneg_left (le_trans hbump hbumpHiSmall)
          (by norm_num)
      _ ≤ 1 / 10 ^ 25 := by norm_num
  have h2 : ratRectEndpointAbsBound3326
      (ratWeightedUnitJetRect3310 2 2 1 4) ≤ 1 / 10 ^ 33 := by
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
          (ratWeightedPhaseRect3310 1 4)) ≤ 819200 := by
      calc
        _ ≤ 2 * ratRectEndpointAbsBound3326
            (RatRect3276.mul (ratWeightedLambdaRect3310 4)
              (ratWeightedLambdaRect3310 4)) *
            ratRectEndpointAbsBound3326 (ratWeightedPhaseRect3310 1 4) :=
          ratRect_mul_endpointAbsBound3349 _ _
        _ ≤ 2 * 3200 * 128 := by
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left hlambdaSq (by norm_num)) hphaseBound
            (ratRectEndpointAbsBound3326_nonneg _) (by norm_num)
        _ ≤ 819200 := by norm_num
    have hcore : ratRectEndpointAbsBound3326
        (RatRect3276.mul (ratScalarRect3310 1)
          (RatRect3276.mul
            (RatRect3276.mul (ratWeightedLambdaRect3310 4)
              (ratWeightedLambdaRect3310 4))
            (ratWeightedPhaseRect3310 1 4))) ≤ 2097152 := by
      have hscalar : ratRectEndpointAbsBound3326 (ratScalarRect3310 1) = 1 := by
        norm_num [ratRectEndpointAbsBound3326, ratScalarRect3310]
      calc
        _ ≤ 2 * ratRectEndpointAbsBound3326 (ratScalarRect3310 1) *
            ratRectEndpointAbsBound3326
              (RatRect3276.mul
                (RatRect3276.mul (ratWeightedLambdaRect3310 4)
                  (ratWeightedLambdaRect3310 4))
                (ratWeightedPhaseRect3310 1 4)) :=
          ratRect_mul_endpointAbsBound3349 _ _
        _ ≤ 2 * 1 * 819200 := by
          rw [hscalar]
          exact mul_le_mul_of_nonneg_left hinner (by norm_num)
        _ ≤ 2097152 := by norm_num
    have hbumpHi : 0 ≤ (ratBumpJetInterval3310 0
        (storedWidthRat3287 4 ^ 2) (record2680CenterRat3279 1)).hi := by
      rw [signed_bump_endpoint3382_cell1_order0_family4_hi_eq]
      exact ratBaseInterval3284_powNat_hi_nonneg3344 188
    have hbump := ratWeightedBumpRect_endpointAbs_le_hi3388 0
      (signed_bump_endpoint3382_cell1_order0_family4_reLo_eq_zero) hbumpHi
    have hbumpHiSmall := signed_bump_endpoint3384_cell1_order0_family4_hi_le
    rw [ratWeightedUnitJetRect3310]
    rw [show (Nat.choose 2 2 : ℚ) = 1 by norm_num]
    rw [show ratRectPowNat3310 (ratWeightedLambdaRect3310 4) 2 =
      RatRect3276.mul (ratWeightedLambdaRect3310 4)
        (ratWeightedLambdaRect3310 4) by
          rw [ratRectPowNat3310]
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
          exact congrArg (fun x => RatRect3276.mul x
            (ratWeightedLambdaRect3310 4))
            (hscalarOne _ hlambdaOrder.1 hlambdaOrder.2)]
    have hmul := ratRect_mul_endpointAbsBound3349
      (RatRect3276.mul (ratScalarRect3310 1)
        (RatRect3276.mul
          (RatRect3276.mul (ratWeightedLambdaRect3310 4)
            (ratWeightedLambdaRect3310 4))
          (ratWeightedPhaseRect3310 1 4)))
      (ratBumpRect3310 0 1 4)
    calc
      _ ≤ 2 * 2097152 * ratRectEndpointAbsBound3326
          (ratBumpRect3310 0 1 4) := by
        calc
          _ ≤ 2 * ratRectEndpointAbsBound3326
              (RatRect3276.mul (ratScalarRect3310 1)
                (RatRect3276.mul
                  (RatRect3276.mul (ratWeightedLambdaRect3310 4)
                    (ratWeightedLambdaRect3310 4))
                  (ratWeightedPhaseRect3310 1 4))) *
              ratRectEndpointAbsBound3326 (ratBumpRect3310 0 1 4) := hmul
          _ ≤ 2 * 2097152 * ratRectEndpointAbsBound3326
              (ratBumpRect3310 0 1 4) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hcore (by norm_num))
              (ratRectEndpointAbsBound3326_nonneg _)
      _ ≤ 2 * 2097152 * (1 / 10 ^ 40) := by
        exact mul_le_mul_of_nonneg_left (le_trans hbump hbumpHiSmall)
          (by norm_num)
      _ ≤ 1 / 10 ^ 33 := by norm_num
  unfold ratWeightedJetSumRect_cell1_order2_family4_3386
  exact le_trans
    (ratRect_add_endpointAbsBound_le_sum3328
      (RatRect3276.add
        (ratWeightedUnitJetRect3310 2 0 1 4)
        (ratWeightedUnitJetRect3310 2 1 1 4))
      (ratWeightedUnitJetRect3310 2 2 1 4))
    (by
      calc
        _ ≤ ratRectEndpointAbsBound3326
              (ratWeightedUnitJetRect3310 2 0 1 4) +
            ratRectEndpointAbsBound3326
              (ratWeightedUnitJetRect3310 2 1 1 4) +
            ratRectEndpointAbsBound3326
              (ratWeightedUnitJetRect3310 2 2 1 4) := by
          exact add_le_add
            (ratRect_add_endpointAbsBound_le_sum3328 _ _) (le_refl _)
        _ ≤ 26 / 10 ^ 15 + 1 / 10 ^ 25 + 1 / 10 ^ 33 := by
          exact add_le_add (add_le_add h0 h1) h2
        _ ≤ 27 / 10 ^ 15 := by norm_num)

end ConnesWeilRH.Dev
