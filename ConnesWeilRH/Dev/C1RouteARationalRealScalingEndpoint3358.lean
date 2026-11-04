import ConnesWeilRH.Dev.C1RouteARationalRealProductEndpoint3356
import ConnesWeilRH.Dev.C1RouteARationalCellWeightEndpoint3357
import ConnesWeilRH.Dev.C1RouteARationalPhaseExactProbe3354

namespace ConnesWeilRH.Dev

theorem ratRect_mul_real_hi_le_coordinate_bound3358
    (a : RatRect3276) (b : RatInterval3276)
    (hbLo : 0 ≤ b.lo) (hbHi : 0 ≤ b.hi)
    (hbOrder : b.lo ≤ b.hi) :
    (RatRect3276.mul a (ratRealRect3281 b)).reHi ≤
      ratRectRealCoordinateAbsBound3356 a * b.hi := by
  unfold RatRect3276.mul RatInterval3276.mul RatInterval3276.sub
    RatInterval3276.add ratRealRect3281
    ratRectRealCoordinateAbsBound3356
  have hAlo : a.reLo ≤ max |a.reLo| |a.reHi| := by
    exact le_trans (le_abs_self _) (le_max_left _ _)
  have hAhi : a.reHi ≤ max |a.reLo| |a.reHi| := by
    exact le_trans (le_abs_self _) (le_max_right _ _)
  have hLo : a.reLo * b.lo ≤
      max |a.reLo| |a.reHi| * b.hi := by
    by_cases h : 0 ≤ a.reLo
    · exact le_trans (mul_le_mul_of_nonneg_left hbOrder h)
        (mul_le_mul_of_nonneg_right hAlo hbHi)
    · exact le_trans (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge h) hbLo)
        (mul_nonneg
          (le_trans (abs_nonneg _) (le_max_left _ _)) hbHi)
  have hHi : a.reHi * b.hi ≤
      max |a.reLo| |a.reHi| * b.hi := by
    exact mul_le_mul_of_nonneg_right hAhi hbHi
  have hLoHi : a.reLo * b.hi ≤
      max |a.reLo| |a.reHi| * b.hi := by
    exact mul_le_mul_of_nonneg_right hAlo hbHi
  have hHiLo : a.reHi * b.lo ≤
      max |a.reLo| |a.reHi| * b.hi := by
    by_cases h : 0 ≤ a.reHi
    · exact le_trans (mul_le_mul_of_nonneg_left hbOrder h)
        (mul_le_mul_of_nonneg_right hAhi hbHi)
    · exact le_trans (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge h) hbLo)
        (mul_nonneg
          (le_trans (abs_nonneg _) (le_max_left _ _)) hbHi)
  simp only [mul_zero, min_self, sub_zero]
  exact max_le (max_le hLo hLoHi) (max_le hHiLo hHi)

theorem ratCellWeightRealScalingEndpoint3358_cell0 :
    (RatRect3276.mul
      (RatRect3276.powSq
        (ratPhaseRect3279
          (record2680PhaseAngleRat3279 0 4)) 9)
      (ratRealRect3281 (ratCellWeightInterval3289 0))).reHi ≤ 64 := by
  apply le_trans
    (ratRect_mul_real_hi_le_coordinate_bound3358 _ _
      (by
        exact ratInterval_powNat_lo_nonneg3344
          (ratTaylorInterval3283 (ratCellWeightArgument3289 0))
          ratCellWeightTaylorLoNonneg3357_cell0
          ratCellWeightTaylorHiNonneg3357_cell0 60)
      (by
        exact ratInterval_powNat_hi_nonneg3344
          (ratTaylorInterval3283 (ratCellWeightArgument3289 0))
          ratCellWeightTaylorLoNonneg3357_cell0
          ratCellWeightTaylorHiNonneg3357_cell0 60)
      (ratInterval_powNat_order3344
        (ratTaylorInterval3283 (ratCellWeightArgument3289 0)) 60))
  have hphase :
      ratRectRealCoordinateAbsBound3356
        (RatRect3276.powSq
          (ratPhaseRect3279
            (record2680PhaseAngleRat3279 0 4)) 9) ≤ 2 := by
    unfold ratRectRealCoordinateAbsBound3356
    calc
      max
          |(RatRect3276.powSq
              (ratPhaseRect3279
                (record2680PhaseAngleRat3279 0 4)) 9).reLo|
          |(RatRect3276.powSq
              (ratPhaseRect3279
                (record2680PhaseAngleRat3279 0 4)) 9).reHi| ≤
          ratRectEndpointAbsBound3326
            (RatRect3276.powSq
              (ratPhaseRect3279
                (record2680PhaseAngleRat3279 0 4)) 9) := by
            unfold ratRectEndpointAbsBound3326
            exact le_max_left _ _
      _ ≤ 2 := ratPhasePowSqEndpointAbsBound3354_cell0_family4_nine
  have hweight :
      (ratCellWeightInterval3289 0).hi ≤ 32 := by
    exact le_trans (le_abs_self _)
      (le_trans
        (le_max_right |(ratCellWeightInterval3289 0).lo|
          |(ratCellWeightInterval3289 0).hi|)
        ratCellWeightIntervalEndpointAbsBound3357_cell0)
  have hweightHi : 0 ≤ (ratCellWeightInterval3289 0).hi := by
    exact ratInterval_powNat_hi_nonneg3344
      (ratTaylorInterval3283 (ratCellWeightArgument3289 0))
      ratCellWeightTaylorLoNonneg3357_cell0
      ratCellWeightTaylorHiNonneg3357_cell0 60
  change ratRectRealCoordinateAbsBound3356
      (RatRect3276.powSq
        (ratPhaseRect3279
          (record2680PhaseAngleRat3279 0 4)) 9) *
        (ratCellWeightInterval3289 0).hi ≤ 64
  calc
    ratRectRealCoordinateAbsBound3356
        (RatRect3276.powSq
          (ratPhaseRect3279
            (record2680PhaseAngleRat3279 0 4)) 9) *
        (ratCellWeightInterval3289 0).hi ≤
        2 * (ratCellWeightInterval3289 0).hi := by
          exact mul_le_mul_of_nonneg_right hphase hweightHi
    _ ≤ 2 * 32 := by
      exact mul_le_mul_of_nonneg_left hweight (by norm_num)
    _ ≤ 64 := by norm_num

theorem ratRect_mul_real_coordinate_abs_bound3358
    (a : RatRect3276) (b : RatInterval3276)
    (hbLo : 0 ≤ b.lo) (hbHi : 0 ≤ b.hi)
    (hbOrder : b.lo ≤ b.hi) :
    ratRectRealCoordinateAbsBound3356
        (RatRect3276.mul a (ratRealRect3281 b)) ≤
      ratRectRealCoordinateAbsBound3356 a * b.hi := by
  let ar : RatInterval3276 := ⟨a.reLo, a.reHi⟩
  let br : RatInterval3276 := ⟨b.lo, b.hi⟩
  have hB : ratIntervalEndpointAbsBound3325 br = b.hi := by
    unfold ratIntervalEndpointAbsBound3325 br
    rw [abs_of_nonneg hbLo, abs_of_nonneg hbHi]
    exact max_eq_right hbOrder
  have hA : ratIntervalEndpointAbsBound3325 ar ≤
      ratRectRealCoordinateAbsBound3356 a := by
    unfold ratIntervalEndpointAbsBound3325 ar
    rfl
  have hhi := ratInterval_mul_hi_le_abs_bound3325 ar br
  have hlo := ratInterval_mul_lo_ge_neg_abs_bound3325 ar br
  have hhi' : (RatInterval3276.mul ar br).hi ≤
      ratRectRealCoordinateAbsBound3356 a * b.hi := by
    rw [hB] at hhi
    exact le_trans hhi
      (mul_le_mul_of_nonneg_right hA hbHi)
  have hlo' : -(ratRectRealCoordinateAbsBound3356 a * b.hi) ≤
      (RatInterval3276.mul ar br).lo := by
    rw [hB] at hlo
    exact le_trans
      (neg_le_neg (mul_le_mul_of_nonneg_right hA hbHi)) hlo
  have hprodOrder :
      (RatInterval3276.mul ar br).lo ≤
        (RatInterval3276.mul ar br).hi := by
    unfold RatInterval3276.mul
    calc
      min (min (ar.lo * br.lo) (ar.lo * br.hi))
          (min (ar.hi * br.lo) (ar.hi * br.hi)) ≤
          min (ar.lo * br.lo) (ar.lo * br.hi) := min_le_left _ _
      _ ≤ max (ar.lo * br.lo) (ar.lo * br.hi) := by
        exact le_trans (min_le_left _ _) (le_max_left _ _)
      _ ≤ max (max (ar.lo * br.lo) (ar.lo * br.hi))
          (max (ar.hi * br.lo) (ar.hi * br.hi)) := le_max_left _ _
  have hloUpper :
      (RatInterval3276.mul ar br).lo ≤
        ratRectRealCoordinateAbsBound3356 a * b.hi :=
    le_trans hprodOrder hhi'
  have hhiLower :
      -(ratRectRealCoordinateAbsBound3356 a * b.hi) ≤
        (RatInterval3276.mul ar br).hi :=
    le_trans hlo' hprodOrder
  have hReLo :
      (RatRect3276.mul a (ratRealRect3281 b)).reLo =
        (RatInterval3276.mul ar br).lo := by
    simp [RatRect3276.mul, RatInterval3276.mul,
      RatInterval3276.sub, RatInterval3276.add, ratRealRect3281,
      ar, br]
  have hReHi :
      (RatRect3276.mul a (ratRealRect3281 b)).reHi =
        (RatInterval3276.mul ar br).hi := by
    simp [RatRect3276.mul, RatInterval3276.mul,
      RatInterval3276.sub, RatInterval3276.add, ratRealRect3281,
      ar, br]
  unfold ratRectRealCoordinateAbsBound3356
  rw [hReLo, hReHi]
  change max |(RatInterval3276.mul ar br).lo|
      |(RatInterval3276.mul ar br).hi| ≤
    max |a.reLo| |a.reHi| * b.hi
  apply max_le
  · exact abs_le.mpr ⟨hlo', hloUpper⟩
  · exact abs_le.mpr ⟨hhiLower, hhi'⟩

end ConnesWeilRH.Dev
