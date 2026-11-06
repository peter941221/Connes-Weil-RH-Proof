import ConnesWeilRH.Dev.C1RouteARationalCellEndpoint3441
import ConnesWeilRH.Dev.C1RouteARationalComplexEndpointBounds3349
import ConnesWeilRH.Dev.C1RouteARationalPhaseExactProbe3354

namespace ConnesWeilRH.Dev

theorem ratInterval_mul_singleton_one3442
    (a : RatInterval3276)
    (haLo : 0 ≤ a.lo)
    (haOrder : a.lo ≤ a.hi) :
    RatInterval3276.mul a ({lo := 1, hi := 1} : RatInterval3276) = a := by
  cases a with
  | mk lo hi =>
      simp only [RatInterval3276.mul, one_mul, mul_one]
      simp [min_eq_left haOrder, max_eq_right haOrder]

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 1000000 in
theorem record2680_cell0_family4_bump_tail3442 :
    ratCellBumpInterval3298 0 4 =
      ({lo := 0, hi := (RatInterval3276.powNat ratBaseInterval3284 188).hi} :
        RatInterval3276) := by
  norm_num [ratCellBumpInterval3298, ratBumpT3286,
    ratTailBumpInterval3298, storedWidthRat3287,
    record2680CenterRat3279, Matrix.cons_val_four]

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 1000000 in
theorem record2680_cell0_family4_bump_hi_le_1_40_3442 :
    (ratCellBumpInterval3298 0 4).hi ≤ 1 / 10 ^ 40 := by
  rw [record2680_cell0_family4_bump_tail3442]
  rw [ratBaseInterval3284_powNat_hi_eq_pow3346]
  norm_num [ratBaseInterval3284, ratTaylorInterval3283,
    ratTaylorSum3283, ratTaylorError3283, storedWidthRat3287,
    record2680CenterRat3279, ratBumpNumerator3310,
    Matrix.cons_val_four]

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 1000000 in
theorem record2680_cell0_family4_real_abs_le_1_20_3442 :
    ratIntervalEndpointAbsBound3325
      (ratCellRealFamilyInterval3298 0 4) ≤ (1 / 10 ^ 20 : ℚ) := by
  let coefficient : RatRect3276 := ratCoefficientRect3282 4
  let phase : RatRect3276 :=
    RatRect3276.powSq
      (ratPhaseRect3279 (record2680PhaseAngleRat3279 0 4)) 9
  let projected : RatInterval3276 :=
    ratCoefficientPhaseRealInterval3298 coefficient phase
  have hcoeff : ratRectEndpointAbsBound3326 coefficient ≤ 2 * 10 ^ 14 := by
    norm_num [coefficient, ratCoefficientRect3282,
      ratRectEndpointAbsBound3326, Matrix.cons_val_four]
  have hphase : ratRectEndpointAbsBound3326 phase ≤ 2 := by
    simpa [phase] using ratPhasePowSqEndpointAbsBound3354_cell0_family4_nine
  have hprod : ratRectEndpointAbsBound3326
      (RatRect3276.mul coefficient phase) ≤ 2 * (2 * 10 ^ 14) * 2 := by
    calc
      ratRectEndpointAbsBound3326 (RatRect3276.mul coefficient phase) ≤
          2 * ratRectEndpointAbsBound3326 coefficient *
            ratRectEndpointAbsBound3326 phase :=
        ratRect_mul_endpointAbsBound3349 coefficient phase
      _ ≤ 2 * (2 * 10 ^ 14) * 2 := by
        calc
          2 * ratRectEndpointAbsBound3326 coefficient *
              ratRectEndpointAbsBound3326 phase ≤
              2 * ratRectEndpointAbsBound3326 coefficient * 2 := by
            exact mul_le_mul_of_nonneg_left hphase
              (mul_nonneg (by norm_num)
                (ratRectEndpointAbsBound3326_nonneg coefficient))
          _ ≤ 2 * (2 * 10 ^ 14) * 2 := by
            calc
              2 * ratRectEndpointAbsBound3326 coefficient * 2 ≤
                  2 * (2 * 10 ^ 14) * 2 := by
                exact mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hcoeff (by norm_num))
                  (by norm_num)
              _ = 2 * (2 * 10 ^ 14) * 2 := by rfl
  have hprod_hi : (RatRect3276.mul coefficient phase).reHi ≤
      2 * (2 * 10 ^ 14) * 2 := by
    have h := hprod
    unfold ratRectEndpointAbsBound3326 at h
    exact le_trans (le_trans (le_abs_self _) (le_max_right _ _))
      (le_trans (le_max_left _ _) h)
  have hprod_lo : -(2 * (2 * 10 ^ 14) * 2) ≤
      (RatRect3276.mul coefficient phase).reLo := by
    have h := hprod
    unfold ratRectEndpointAbsBound3326 at h
    have habs : |(RatRect3276.mul coefficient phase).reLo| ≤
        2 * (2 * 10 ^ 14) * 2 :=
      le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) h
    exact neg_le_of_abs_le habs
  have hprod_reLo_le : (RatRect3276.mul coefficient phase).reLo ≤
      2 * (2 * 10 ^ 14) * 2 := by
    exact le_trans (le_abs_self _) (by
      have h := hprod
      unfold ratRectEndpointAbsBound3326 at h
      exact le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) h)
  have hprod_reHi_abs : |(RatRect3276.mul coefficient phase).reHi| ≤
      2 * (2 * 10 ^ 14) * 2 := by
    have h := hprod
    unfold ratRectEndpointAbsBound3326 at h
    exact le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) h
  have hprojected_lo : -(2 * (2 * 10 ^ 14) * 2) ≤ projected.lo := by
    change -(2 * (2 * 10 ^ 14) * 2) ≤
      (RatRect3276.mul coefficient phase).reLo
    exact hprod_lo
  have hprojected_hi : projected.hi ≤ 2 * (2 * 10 ^ 14) * 2 := by
    change (RatRect3276.mul coefficient phase).reHi ≤
      2 * (2 * 10 ^ 14) * 2
    exact hprod_hi
  have hprojected_abs :
      ratIntervalEndpointAbsBound3325 projected ≤
        2 * (2 * 10 ^ 14) * 2 := by
    unfold ratIntervalEndpointAbsBound3325
    apply max_le
    · exact (abs_le).2 ⟨hprojected_lo, hprod_reLo_le⟩
    · exact (abs_le).2 ⟨neg_le_of_abs_le hprod_reHi_abs, hprojected_hi⟩
  have hbump_abs : ratIntervalEndpointAbsBound3325
      (ratCellBumpInterval3298 0 4) ≤ 1 / 10 ^ 40 := by
    rw [record2680_cell0_family4_bump_tail3442]
    have hpow_hi : (RatInterval3276.powNat ratBaseInterval3284 188).hi ≤
        1 / 10 ^ 40 := by
      simpa [record2680_cell0_family4_bump_tail3442] using
        record2680_cell0_family4_bump_hi_le_1_40_3442
    have hpow_nonneg : 0 ≤
        (RatInterval3276.powNat ratBaseInterval3284 188).hi :=
      ratBaseInterval3284_powNat_hi_nonneg3344 188
    unfold ratIntervalEndpointAbsBound3325
    apply max_le
    · norm_num
    · simpa [abs_of_nonneg hpow_nonneg] using hpow_hi
  have hmul := ratInterval_mul_hi_le_abs_bound3325
    (ratCellBumpInterval3298 0 4) projected
  have hmul_product_bound :
      ratIntervalEndpointAbsBound3325 (ratCellBumpInterval3298 0 4) *
          ratIntervalEndpointAbsBound3325 projected ≤
        (1 / 10 ^ 40) * (2 * (2 * 10 ^ 14) * 2) := by
    exact calc
      ratIntervalEndpointAbsBound3325 (ratCellBumpInterval3298 0 4) *
          ratIntervalEndpointAbsBound3325 projected ≤
          (1 / 10 ^ 40) *
            ratIntervalEndpointAbsBound3325 projected := by
            exact mul_le_mul_of_nonneg_right hbump_abs
              (ratIntervalEndpointAbsBound3325_nonneg projected)
      _ ≤ (1 / 10 ^ 40) * (2 * (2 * 10 ^ 14) * 2) := by
        exact mul_le_mul_of_nonneg_left hprojected_abs (by positivity)
  have hmul_hi_bound : (ratCellRealFamilyInterval3298 0 4).hi ≤
      (1 / 10 ^ 40) * (2 * (2 * 10 ^ 14) * 2) := by
    exact le_trans hmul hmul_product_bound
  have hmul_lo := ratInterval_mul_lo_ge_neg_abs_bound3325
    (ratCellBumpInterval3298 0 4) projected
  have hmul_lo_bound :
      -(1 / 10 ^ 40) * (2 * (2 * 10 ^ 14) * 2) ≤
        (ratCellRealFamilyInterval3298 0 4).lo := by
    change -(1 / 10 ^ 40) * (2 * (2 * 10 ^ 14) * 2) ≤
      (RatInterval3276.mul (ratCellBumpInterval3298 0 4) projected).lo
    calc
      -(1 / 10 ^ 40) * (2 * (2 * 10 ^ 14) * 2) =
          -((1 / 10 ^ 40) * (2 * (2 * 10 ^ 14) * 2)) := by ring
      _ ≤ -(ratIntervalEndpointAbsBound3325
          (ratCellBumpInterval3298 0 4) *
          ratIntervalEndpointAbsBound3325 projected) :=
        neg_le_neg hmul_product_bound
      _ ≤ (RatInterval3276.mul
          (ratCellBumpInterval3298 0 4) projected).lo := hmul_lo
  have hmul_lo_upper :
      (ratCellRealFamilyInterval3298 0 4).lo ≤
        (1 / 10 ^ 40) * (2 * (2 * 10 ^ 14) * 2) := by
    have horder := ratInterval_mul_order3344
      (ratCellBumpInterval3298 0 4) projected
    exact le_trans horder hmul_hi_bound
  have habs_mul :
      ratIntervalEndpointAbsBound3325
          (RatInterval3276.mul (ratCellBumpInterval3298 0 4) projected) ≤
        (1 / 10 ^ 40) * (2 * (2 * 10 ^ 14) * 2) := by
    unfold ratIntervalEndpointAbsBound3325
    have hmul_lo_bound' :
        -(1 / 10 ^ 40) * (2 * (2 * 10 ^ 14) * 2) ≤
          (RatInterval3276.mul (ratCellBumpInterval3298 0 4) projected).lo := by
      simpa [ratCellRealFamilyInterval3298, ratRealFamilyInterval3298,
        projected] using hmul_lo_bound
    have hmul_lo_bound'' :
        -(1 / 10 ^ 40 * (2 * (2 * 10 ^ 14) * 2)) ≤
          (RatInterval3276.mul (ratCellBumpInterval3298 0 4) projected).lo := by
      calc
        -(1 / 10 ^ 40 * (2 * (2 * 10 ^ 14) * 2)) =
            -(1 / 10 ^ 40) * (2 * (2 * 10 ^ 14) * 2) := by ring
        _ ≤ (RatInterval3276.mul
            (ratCellBumpInterval3298 0 4) projected).lo := hmul_lo_bound'
    have hmul_hi_bound' :
        (RatInterval3276.mul (ratCellBumpInterval3298 0 4) projected).hi ≤
          (1 / 10 ^ 40) * (2 * (2 * 10 ^ 14) * 2) := by
      simpa [ratCellRealFamilyInterval3298, ratRealFamilyInterval3298,
        projected] using hmul_hi_bound
    have horder := ratInterval_mul_order3344
      (ratCellBumpInterval3298 0 4) projected
    apply max_le
    · exact (abs_le).2 ⟨hmul_lo_bound'', hmul_lo_upper⟩
    · exact (abs_le).2 ⟨le_trans hmul_lo_bound'' horder, hmul_hi_bound'⟩
  calc
    ratIntervalEndpointAbsBound3325
        (ratCellRealFamilyInterval3298 0 4) ≤
        (1 / 10 ^ 40) * (2 * (2 * 10 ^ 14) * 2) := by
      simpa [ratCellRealFamilyInterval3298, ratRealFamilyInterval3298,
        projected] using habs_mul
    _ ≤ (1 / 10 ^ 20 : ℚ) := by norm_num

end ConnesWeilRH.Dev
