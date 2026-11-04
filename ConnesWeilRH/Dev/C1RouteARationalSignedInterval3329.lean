import ConnesWeilRH.Dev.C1RouteARationalEndpointBounds3325

namespace ConnesWeilRH.Dev

theorem ratInterval_mul_singleton_nonneg_hi3329
    (c : ℚ) (b : RatInterval3276)
    (hc : 0 ≤ c) (hb : b.lo ≤ b.hi) :
    (RatInterval3276.mul ({ lo := c, hi := c } : RatInterval3276) b).hi =
      c * b.hi := by
  unfold RatInterval3276.mul
  simp only [max_self]
  rw [max_eq_right]
  exact mul_le_mul_of_nonneg_left hb hc

theorem ratInterval_mul_singleton_nonpos_hi3329
    (c : ℚ) (b : RatInterval3276)
    (hc : c ≤ 0) (hb : b.lo ≤ b.hi) :
    (RatInterval3276.mul ({ lo := c, hi := c } : RatInterval3276) b).hi =
      c * b.lo := by
  unfold RatInterval3276.mul
  simp only [max_self]
  rw [max_eq_left]
  exact mul_le_mul_of_nonpos_left hb hc

theorem ratInterval_mul_singleton_nonneg_lo3329
    (c : ℚ) (b : RatInterval3276)
    (hc : 0 ≤ c) (hb : b.lo ≤ b.hi) :
    (RatInterval3276.mul ({ lo := c, hi := c } : RatInterval3276) b).lo =
      c * b.lo := by
  unfold RatInterval3276.mul
  simp only [min_self]
  rw [min_eq_left]
  exact mul_le_mul_of_nonneg_left hb hc

theorem ratInterval_mul_singleton_nonpos_lo3329
    (c : ℚ) (b : RatInterval3276)
    (hc : c ≤ 0) (hb : b.lo ≤ b.hi) :
    (RatInterval3276.mul ({ lo := c, hi := c } : RatInterval3276) b).lo =
      c * b.hi := by
  unfold RatInterval3276.mul
  simp only [min_self]
  rw [min_eq_right]
  exact mul_le_mul_of_nonpos_left hb hc

end ConnesWeilRH.Dev
