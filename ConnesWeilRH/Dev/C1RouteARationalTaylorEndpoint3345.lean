import ConnesWeilRH.Dev.C1RouteARationalTaylorEndpoint3344

namespace ConnesWeilRH.Dev

theorem ratInterval_mul_hi_eq_hi_mul_hi_of_nonneg3345
    (a b : RatInterval3276)
    (haLo : 0 ≤ a.lo) (haHi : 0 ≤ a.hi)
    (hbLo : 0 ≤ b.lo) (hbHi : 0 ≤ b.hi)
    (haOrder : a.lo ≤ a.hi) (hbOrder : b.lo ≤ b.hi) :
    (RatInterval3276.mul a b).hi = a.hi * b.hi := by
  unfold RatInterval3276.mul
  apply le_antisymm
  · apply max_le
    · apply max_le
      · exact mul_le_mul haOrder hbOrder hbLo haHi
      · exact mul_le_mul haOrder (le_rfl) hbHi haHi
    · apply max_le
      · exact mul_le_mul (le_rfl) hbOrder hbLo haHi
      · exact le_rfl
  · exact le_max_right _ _ |>.trans (le_max_right _ _)

theorem ratInterval_powNat_hi_eq_pow_of_nonneg3345
    (a : RatInterval3276)
    (haLo : 0 ≤ a.lo) (haHi : 0 ≤ a.hi)
    (haOrder : a.lo ≤ a.hi) :
    ∀ n, (RatInterval3276.powNat a n).hi = a.hi ^ n
  | 0 => by norm_num [RatInterval3276.powNat]
  | n + 1 => by
      rw [RatInterval3276.powNat]
      rw [ratInterval_mul_hi_eq_hi_mul_hi_of_nonneg3345]
      · rw [ratInterval_powNat_hi_eq_pow_of_nonneg3345 a haLo haHi haOrder n]
        ring
      · exact ratInterval_powNat_lo_nonneg3344 a haLo haHi n
      · exact ratInterval_powNat_hi_nonneg3344 a haLo haHi n
      · exact haLo
      · exact haHi
      · exact ratInterval_powNat_order3344 a n
      · exact haOrder

end ConnesWeilRH.Dev
