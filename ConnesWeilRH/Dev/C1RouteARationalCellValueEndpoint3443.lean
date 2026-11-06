import ConnesWeilRH.Dev.C1RouteARationalIntervalIdentity3442
import ConnesWeilRH.Dev.C1RouteARationalCellWeightEndpoint3357

namespace ConnesWeilRH.Dev

theorem record2680_cell0_real_sum_abs_le_1_20_3443 :
    ratIntervalEndpointAbsBound3325 (ratCellRealSum3298 0) ≤
      (1 / 10 ^ 20 : ℚ) := by
  rw [record2680_block0_real_sum_eq_family4_3441 (by norm_num)]
  simpa using record2680_cell0_family4_real_abs_le_1_20_3442

theorem record2680_cell0_weight_abs_le_27_3443 :
    ratIntervalEndpointAbsBound3325 (ratCellWeightInterval3289 0) ≤
      (27 : ℚ) := by
  have hweight_hi := record2680_cell0_weight_hi_le_27_3441
  have hTaylorLo := ratCellWeightTaylorLoNonneg3357_cell0
  have hTaylorHi := ratCellWeightTaylorHiNonneg3357_cell0
  have hTaylorOrder := ratCellWeightTaylorOrder3357_cell0
  have hweight_lo : 0 ≤ (ratCellWeightInterval3289 0).lo := by
    simpa [ratCellWeightInterval3289] using
      ratInterval_powNat_lo_nonneg3344
        (ratTaylorInterval3283 (ratCellWeightArgument3289 0))
        hTaylorLo hTaylorHi 60
  have hweight_order : (ratCellWeightInterval3289 0).lo ≤
      (ratCellWeightInterval3289 0).hi := by
    simpa [ratCellWeightInterval3289] using
      ratInterval_powNat_order3344
        (ratTaylorInterval3283 (ratCellWeightArgument3289 0)) 60
  have hweight_hi_nonneg : 0 ≤ (ratCellWeightInterval3289 0).hi :=
    le_trans hweight_lo hweight_order
  unfold ratIntervalEndpointAbsBound3325
  apply max_le
  · calc
      |(ratCellWeightInterval3289 0).lo| =
          (ratCellWeightInterval3289 0).lo := abs_of_nonneg hweight_lo
      _ ≤ (ratCellWeightInterval3289 0).hi := hweight_order
      _ ≤ 27 := hweight_hi
  · simpa [abs_of_nonneg hweight_hi_nonneg] using hweight_hi

theorem record2680_cell0_value_upper_le_1_18_3443 :
    ratCellValueUpperTight3298 0 ≤ (1 / 10 ^ 18 : ℝ) := by
  have hweight := record2680_cell0_weight_abs_le_27_3443
  have hsum := record2680_cell0_real_sum_abs_le_1_20_3443
  have hmul := ratInterval_mul_hi_le_abs_bound3325
    (ratCellWeightInterval3289 0) (ratCellRealSum3298 0)
  have hproduct :
      ratIntervalEndpointAbsBound3325 (ratCellWeightInterval3289 0) *
          ratIntervalEndpointAbsBound3325 (ratCellRealSum3298 0) ≤
        (27 : ℚ) * (1 / 10 ^ 20) := by
    exact mul_le_mul hweight hsum
      (ratIntervalEndpointAbsBound3325_nonneg (ratCellRealSum3298 0))
      (by norm_num)
  have hupper :
      (RatInterval3276.mul (ratCellWeightInterval3289 0)
        (ratCellRealSum3298 0)).hi ≤
        (1 / 10 ^ 18 : ℚ) := by
    calc
      (RatInterval3276.mul (ratCellWeightInterval3289 0)
          (ratCellRealSum3298 0)).hi ≤
          ratIntervalEndpointAbsBound3325 (ratCellWeightInterval3289 0) *
            ratIntervalEndpointAbsBound3325 (ratCellRealSum3298 0) := hmul
      _ ≤ (27 : ℚ) * (1 / 10 ^ 20) := hproduct
      _ ≤ (1 / 10 ^ 18 : ℚ) := by norm_num
  unfold ratCellValueUpperTight3298
  have hupper_real :
      (((RatInterval3276.mul (ratCellWeightInterval3289 0)
        (ratCellRealSum3298 0)).hi : ℚ) : ℝ) ≤
        ((1 / 10 ^ 18 : ℚ) : ℝ) :=
    Rat.cast_le.mpr hupper
  simpa using hupper_real

end ConnesWeilRH.Dev
