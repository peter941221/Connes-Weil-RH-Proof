import ConnesWeilRH.Dev.C1RouteARationalBlock0Family4Uniform3454
import ConnesWeilRH.Dev.C1RouteARationalComplexEndpointBounds3349

namespace ConnesWeilRH.Dev

theorem ratInterval_mul_endpointAbsBound3455
    (a b : RatInterval3276) :
    ratIntervalEndpointAbsBound3325 (RatInterval3276.mul a b) ≤
      ratIntervalEndpointAbsBound3325 a *
        ratIntervalEndpointAbsBound3325 b := by
  have hhi := ratInterval_mul_hi_le_abs_bound3325 a b
  have hlo := ratInterval_mul_lo_ge_neg_abs_bound3325 a b
  have horder := ratInterval_mul_order3344 a b
  have hhi' : (RatInterval3276.mul a b).hi ≤
      ratIntervalEndpointAbsBound3325 a *
        ratIntervalEndpointAbsBound3325 b := hhi
  have hlo' : -(ratIntervalEndpointAbsBound3325 a *
      ratIntervalEndpointAbsBound3325 b) ≤
      (RatInterval3276.mul a b).lo := hlo
  unfold ratIntervalEndpointAbsBound3325
  apply max_le
  · exact (abs_le).2 ⟨hlo', le_trans horder hhi'⟩
  · exact (abs_le).2 ⟨le_trans hlo' horder, hhi'⟩

theorem record2680_block0_family4_bump_hi_le_1_40_3455
    {index : ℕ} (hindex : index < 256) :
    (ratCellBumpInterval3298 index 4).hi ≤ 1 / 10 ^ 40 := by
  rw [record2680_block0_family4_bump_tail3454 hindex]
  have h0 := record2680_cell0_family4_bump_hi_le_1_40_3442
  simpa [record2680_cell0_family4_bump_tail3442] using h0

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 1000000 in
theorem record2680_block0_family4_real_abs_le_1_20_3455
    {index : ℕ} (hindex : index < 256) :
    ratIntervalEndpointAbsBound3325
      (ratCellRealFamilyInterval3298 index 4) ≤
        (1 / 10 ^ 20 : ℚ) := by
  let coefficient : RatRect3276 := ratCoefficientRect3282 4
  let phase : RatRect3276 :=
    RatRect3276.powSq
      (ratPhaseRect3279 (record2680PhaseAngleRat3279 index 4)) 9
  let projected : RatInterval3276 :=
    ratCoefficientPhaseRealInterval3298 coefficient phase
  have hcoeff : ratRectEndpointAbsBound3326 coefficient ≤ 2 * 10 ^ 14 := by
    norm_num [coefficient, ratCoefficientRect3282,
      ratRectEndpointAbsBound3326, Matrix.cons_val_four]
  have hphase : ratRectEndpointAbsBound3326 phase ≤ 2 := by
    simpa [phase] using
      record2680_block0_family4_phase_abs_le_2_3454 hindex
  have hprod : ratRectEndpointAbsBound3326
      (RatRect3276.mul coefficient phase) ≤ 2 * (2 * 10 ^ 14) * 2 := by
    have hcoeff_nonneg : 0 ≤ ratRectEndpointAbsBound3326 coefficient :=
      ratRectEndpointAbsBound3326_nonneg coefficient
    calc
      ratRectEndpointAbsBound3326 (RatRect3276.mul coefficient phase) ≤
          2 * ratRectEndpointAbsBound3326 coefficient *
            ratRectEndpointAbsBound3326 phase :=
        ratRect_mul_endpointAbsBound3349 coefficient phase
      _ ≤ 2 * ratRectEndpointAbsBound3326 coefficient * 2 := by
        exact mul_le_mul_of_nonneg_left hphase
          (mul_nonneg (by norm_num) hcoeff_nonneg)
      _ ≤ 2 * (2 * 10 ^ 14) * 2 := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hcoeff (by norm_num)) (by norm_num)
  have hprojected : ratIntervalEndpointAbsBound3325 projected ≤
      2 * (2 * 10 ^ 14) * 2 := by
    have h := hprod
    unfold ratRectEndpointAbsBound3326 at h
    have hlo : -(2 * (2 * 10 ^ 14) * 2) ≤ projected.lo := by
      change -(2 * (2 * 10 ^ 14) * 2) ≤
        (RatRect3276.mul coefficient phase).reLo
      exact neg_le_of_abs_le (le_trans
        (le_trans (le_max_left _ _) (le_max_left _ _)) h)
    have hhi : projected.hi ≤ 2 * (2 * 10 ^ 14) * 2 := by
      change (RatRect3276.mul coefficient phase).reHi ≤ _
      exact le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) h
    have hlo_abs : |projected.lo| ≤ 2 * (2 * 10 ^ 14) * 2 := by
      change |(RatRect3276.mul coefficient phase).reLo| ≤ _
      exact le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) h
    have hhi_abs : |projected.hi| ≤ 2 * (2 * 10 ^ 14) * 2 := by
      change |(RatRect3276.mul coefficient phase).reHi| ≤ _
      exact le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) h
    unfold ratIntervalEndpointAbsBound3325
    exact max_le hlo_abs hhi_abs
  have hbump : ratIntervalEndpointAbsBound3325
      (ratCellBumpInterval3298 index 4) ≤ 1 / 10 ^ 40 := by
    rw [record2680_block0_family4_bump_tail3454 hindex]
    have hpow : 0 ≤
        (RatInterval3276.powNat ratBaseInterval3284 188).hi :=
      ratBaseInterval3284_powNat_hi_nonneg3344 188
    unfold ratIntervalEndpointAbsBound3325
    apply max_le
    · norm_num
    · simpa [abs_of_nonneg hpow] using
        record2680_block0_family4_bump_hi_le_1_40_3455 hindex
  have hmul := ratInterval_mul_endpointAbsBound3455
    (ratCellBumpInterval3298 index 4) projected
  calc
    ratIntervalEndpointAbsBound3325
        (ratCellRealFamilyInterval3298 index 4) ≤
        ratIntervalEndpointAbsBound3325
          (RatInterval3276.mul (ratCellBumpInterval3298 index 4) projected) := by
      simpa [ratCellRealFamilyInterval3298, ratRealFamilyInterval3298,
        projected]
    _ ≤ (1 / 10 ^ 40) * (2 * (2 * 10 ^ 14) * 2) := by
      calc
        ratIntervalEndpointAbsBound3325
            (RatInterval3276.mul (ratCellBumpInterval3298 index 4) projected) ≤
            ratIntervalEndpointAbsBound3325 (ratCellBumpInterval3298 index 4) *
              ratIntervalEndpointAbsBound3325 projected := hmul
        _ ≤ (1 / 10 ^ 40) * (2 * (2 * 10 ^ 14) * 2) := by
          exact mul_le_mul hbump hprojected
            (ratIntervalEndpointAbsBound3325_nonneg projected)
            (by positivity)
    _ ≤ (1 / 10 ^ 20 : ℚ) := by norm_num

end ConnesWeilRH.Dev
