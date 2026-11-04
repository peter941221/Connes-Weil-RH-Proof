import ConnesWeilRH.Dev.C1RouteARationalComplexEndpointBounds3349

namespace ConnesWeilRH.Dev

def ratRectRealCoordinateAbsBound3356 (a : RatRect3276) : ℚ :=
  max |a.reLo| |a.reHi|

theorem ratRect_mul_real_hi_le_coordinate_bound3356
    (a : RatRect3276) (b : RatInterval3276)
    (hbLo : b.lo = 0) (hbHi : 0 ≤ b.hi) :
    (RatRect3276.mul a (ratRealRect3281 b)).reHi ≤
      ratRectRealCoordinateAbsBound3356 a * b.hi := by
  unfold RatRect3276.mul RatInterval3276.mul RatInterval3276.sub
    RatInterval3276.add ratRealRect3281
    ratRectRealCoordinateAbsBound3356
  rw [hbLo]
  simp only [mul_zero, zero_mul, min_self, max_self, sub_zero]
  have hreLo : a.reLo * b.hi ≤
      ratRectRealCoordinateAbsBound3356 a * b.hi := by
    exact (mul_le_mul_of_nonneg_right
      (le_trans (le_abs_self _) (le_max_left _ _)) hbHi)
  have hreHi : a.reHi * b.hi ≤
      ratRectRealCoordinateAbsBound3356 a * b.hi := by
    exact (mul_le_mul_of_nonneg_right
      (le_trans (le_abs_self _) (le_max_right _ _)) hbHi)
  have hzero : (0 : ℚ) ≤
      ratRectRealCoordinateAbsBound3356 a * b.hi := by
    exact mul_nonneg
      (le_trans (abs_nonneg _) (le_max_left _ _)) hbHi
  apply max_le
  · exact max_le hzero hreLo
  · exact max_le hzero hreHi

end ConnesWeilRH.Dev
