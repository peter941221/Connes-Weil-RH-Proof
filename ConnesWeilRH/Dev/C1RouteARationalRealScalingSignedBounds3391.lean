import ConnesWeilRH.Dev.C1RouteARationalRealProductEndpoint3356

namespace ConnesWeilRH.Dev

def ratRectImagCoordinateAbsBound3391 (a : RatRect3276) : ℚ :=
  max |a.imLo| |a.imHi|


theorem ratRect_mul_real_reLo_ge_coordinate_bound3391
    (a : RatRect3276) (b : RatInterval3276)
    (hbLo : 0 ≤ b.lo) (hbHi : 0 ≤ b.hi) (hbOrder : b.lo ≤ b.hi) :
    -(ratRectRealCoordinateAbsBound3356 a * b.hi) ≤
      (RatRect3276.mul a (ratRealRect3281 b)).reLo := by
  unfold RatRect3276.mul RatInterval3276.mul RatInterval3276.sub
    RatInterval3276.add ratRealRect3281
    ratRectRealCoordinateAbsBound3356
  simp only [zero_mul, min_self, max_self, sub_zero]
  have hreLo :
      -(max |a.reLo| |a.reHi| * b.hi) ≤ a.reLo * b.hi := by
    have h := (neg_le_neg (le_max_left |a.reLo| |a.reHi|)).trans
      (neg_abs_le a.reLo)
    simpa [neg_mul] using mul_le_mul_of_nonneg_right h hbHi
  have hreHi :
      -(max |a.reLo| |a.reHi| * b.hi) ≤ a.reHi * b.hi := by
    have h := (neg_le_neg (le_max_right |a.reLo| |a.reHi|)).trans
      (neg_abs_le a.reHi)
    simpa [neg_mul] using mul_le_mul_of_nonneg_right h hbHi
  have hzero :
      -(max |a.reLo| |a.reHi| * b.hi) ≤ 0 := by
    exact neg_nonpos.mpr (mul_nonneg
      (le_trans (abs_nonneg _) (le_max_left _ _)) hbHi)
  have hreLoLo :
      -(max |a.reLo| |a.reHi| * b.hi) ≤ a.reLo * b.lo := by
    by_cases h : 0 ≤ a.reLo
    · exact le_trans (neg_nonpos.mpr (mul_nonneg
          (le_trans (abs_nonneg _) (le_max_left _ _)) hbHi))
        (mul_nonneg h hbLo)
    · have hscale :
          -(max |a.reLo| |a.reHi| * b.hi) ≤
            -(max |a.reLo| |a.reHi| * b.lo) := by
        have hA : 0 ≤ max |a.reLo| |a.reHi| :=
          le_trans (abs_nonneg _) (le_max_left _ _)
        simpa [neg_mul] using
          (mul_le_mul_of_nonpos_left hbOrder (neg_nonpos.mpr hA))
      exact hscale.trans (by
        simpa [neg_mul] using mul_le_mul_of_nonneg_right
          ((neg_le_neg (le_max_left |a.reLo| |a.reHi|)).trans
            (neg_abs_le a.reLo)) hbLo)
  have hreHiLo :
      -(max |a.reLo| |a.reHi| * b.hi) ≤ a.reHi * b.lo := by
    by_cases h : 0 ≤ a.reHi
    · exact le_trans (neg_nonpos.mpr (mul_nonneg
          (le_trans (abs_nonneg _) (le_max_right _ _)) hbHi))
        (mul_nonneg h hbLo)
    · have hscale :
          -(max |a.reLo| |a.reHi| * b.hi) ≤
            -(max |a.reLo| |a.reHi| * b.lo) := by
        have hA : 0 ≤ max |a.reLo| |a.reHi| :=
          le_trans (abs_nonneg _) (le_max_right _ _)
        simpa [neg_mul] using
          (mul_le_mul_of_nonpos_left hbOrder (neg_nonpos.mpr hA))
      exact hscale.trans (by
        simpa [neg_mul] using mul_le_mul_of_nonneg_right
          ((neg_le_neg (le_max_right |a.reLo| |a.reHi|)).trans
            (neg_abs_le a.reHi)) hbLo)
  simpa [mul_zero, max_self, sub_zero] using le_min
    (le_min hreLoLo hreLo)
    (le_min hreHiLo hreHi)

theorem ratRect_mul_real_imHi_le_coordinate_bound3391
    (a : RatRect3276) (b : RatInterval3276)
    (hbLo : 0 ≤ b.lo) (hbHi : 0 ≤ b.hi) (hbOrder : b.lo ≤ b.hi) :
    (RatRect3276.mul a (ratRealRect3281 b)).imHi ≤
      ratRectImagCoordinateAbsBound3391 a * b.hi := by
  unfold RatRect3276.mul RatInterval3276.mul RatInterval3276.add
    ratRealRect3281
  simp only [zero_mul, min_self, max_self, add_zero]
  unfold ratRectImagCoordinateAbsBound3391
  have himLoLo :
      a.imLo * b.lo ≤ max |a.imLo| |a.imHi| * b.hi := by
    by_cases h : 0 ≤ a.imLo
    · exact le_trans (mul_le_mul_of_nonneg_left hbOrder h)
        (mul_le_mul_of_nonneg_right
          (le_trans (le_abs_self _) (le_max_left _ _)) hbHi)
    · exact le_trans (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge h) hbLo)
        (mul_nonneg (le_trans (abs_nonneg _) (le_max_left _ _)) hbHi)
  have himHiLo :
      a.imHi * b.lo ≤ max |a.imLo| |a.imHi| * b.hi := by
    by_cases h : 0 ≤ a.imHi
    · exact le_trans (mul_le_mul_of_nonneg_left hbOrder h)
        (mul_le_mul_of_nonneg_right
          (le_trans (le_abs_self _) (le_max_right _ _)) hbHi)
    · exact le_trans (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge h) hbLo)
        (mul_nonneg (le_trans (abs_nonneg _) (le_max_left _ _)) hbHi)
  have himLo :
      a.imLo * b.hi ≤ max |a.imLo| |a.imHi| * b.hi := by
    exact mul_le_mul_of_nonneg_right
      (le_trans (le_abs_self _) (le_max_left _ _)) hbHi
  have himHi :
      a.imHi * b.hi ≤ max |a.imLo| |a.imHi| * b.hi := by
    exact mul_le_mul_of_nonneg_right
      (le_trans (le_abs_self _) (le_max_right _ _)) hbHi
  have hzero :
      0 ≤ max |a.imLo| |a.imHi| * b.hi := by
    exact mul_nonneg
      (le_trans (abs_nonneg _) (le_max_left _ _)) hbHi
  simpa [zero_add] using (max_le
    (max_le himLoLo himLo) (max_le himHiLo himHi))


theorem ratRect_mul_real_imHi_le_coordinate_upper_bound3391
    (a : RatRect3276) (b : RatInterval3276) (bound : ℚ)
    (haImOrder : a.imLo ≤ a.imHi) (haImHi : a.imHi ≤ bound)
    (hbound : 0 ≤ bound)
    (hbLo : 0 ≤ b.lo) (hbHi : 0 ≤ b.hi) (hbOrder : b.lo ≤ b.hi) :
    (RatRect3276.mul a (ratRealRect3281 b)).imHi ≤ bound * b.hi := by
  unfold RatRect3276.mul RatInterval3276.mul RatInterval3276.add
    ratRealRect3281
  simp only [zero_mul, min_self, max_self, add_zero]
  have himLoLo : a.imLo * b.lo ≤ bound * b.hi := by
    exact (mul_le_mul_of_nonneg_right
      (haImOrder.trans haImHi) hbLo).trans
      (mul_le_mul_of_nonneg_left hbOrder hbound)
  have himHiLo : a.imHi * b.lo ≤ bound * b.hi := by
    exact (mul_le_mul_of_nonneg_right haImHi hbLo).trans
      (mul_le_mul_of_nonneg_left hbOrder hbound)
  have himLo : a.imLo * b.hi ≤ bound * b.hi := by
    exact mul_le_mul_of_nonneg_right (haImOrder.trans haImHi) hbHi
  have himHi : a.imHi * b.hi ≤ bound * b.hi := by
    exact mul_le_mul_of_nonneg_right haImHi hbHi
  simpa [zero_add] using (max_le
    (max_le himLoLo himLo) (max_le himHiLo himHi))


theorem ratRect_mul_real_imLo_ge_coordinate_bound3391
    (a : RatRect3276) (b : RatInterval3276)
    (hbLo : 0 ≤ b.lo) (hbHi : 0 ≤ b.hi) (hbOrder : b.lo ≤ b.hi) :
    -(ratRectImagCoordinateAbsBound3391 a * b.hi) ≤
      (RatRect3276.mul a (ratRealRect3281 b)).imLo := by
  unfold RatRect3276.mul RatInterval3276.mul RatInterval3276.add
    ratRealRect3281 ratRectImagCoordinateAbsBound3391
  simp only [zero_mul, min_self, max_self, add_zero]
  have hA : 0 ≤ max |a.imLo| |a.imHi| :=
    le_trans (abs_nonneg _) (le_max_left _ _)
  have himLo :
      -(max |a.imLo| |a.imHi| * b.hi) ≤ a.imLo * b.hi := by
    simpa [neg_mul] using
      mul_le_mul_of_nonneg_right
        ((neg_le_neg (le_max_left |a.imLo| |a.imHi|)).trans
          (neg_abs_le a.imLo)) hbHi
  have himHi :
      -(max |a.imLo| |a.imHi| * b.hi) ≤ a.imHi * b.hi := by
    simpa [neg_mul] using
      mul_le_mul_of_nonneg_right
        ((neg_le_neg (le_max_right |a.imLo| |a.imHi|)).trans
          (neg_abs_le a.imHi)) hbHi
  have himLoLo :
      -(max |a.imLo| |a.imHi| * b.hi) ≤ a.imLo * b.lo := by
    have hscale :
        -(max |a.imLo| |a.imHi| * b.hi) ≤
          -(max |a.imLo| |a.imHi| * b.lo) := by
      simpa [neg_mul] using
        mul_le_mul_of_nonpos_left hbOrder (neg_nonpos.mpr hA)
    exact hscale.trans (by
      simpa [neg_mul] using
        mul_le_mul_of_nonneg_right
          ((neg_le_neg (le_max_left |a.imLo| |a.imHi|)).trans
            (neg_abs_le a.imLo)) hbLo)
  have himHiLo :
      -(max |a.imLo| |a.imHi| * b.hi) ≤ a.imHi * b.lo := by
    have hscale :
        -(max |a.imLo| |a.imHi| * b.hi) ≤
          -(max |a.imLo| |a.imHi| * b.lo) := by
      simpa [neg_mul] using
        mul_le_mul_of_nonpos_left hbOrder (neg_nonpos.mpr hA)
    exact hscale.trans (by
      simpa [neg_mul] using
        mul_le_mul_of_nonneg_right
          ((neg_le_neg (le_max_right |a.imLo| |a.imHi|)).trans
            (neg_abs_le a.imHi)) hbLo)
  simpa [zero_add] using (le_min
    (le_min himLoLo himLo) (le_min himHiLo himHi))end ConnesWeilRH.Dev
