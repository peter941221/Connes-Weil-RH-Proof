import ConnesWeilRH.Dev.C1RouteARationalBump3284

namespace ConnesWeilRH.Dev

theorem ratBaseInterval3284_lo_nonneg3344 :
    0 ≤ ratBaseInterval3284.lo := by
  norm_num [ratBaseInterval3284, ratTaylorInterval3283,
    ratTaylorSum3283, ratTaylorError3283]

theorem ratBaseInterval3284_hi_nonneg3344 :
    0 ≤ ratBaseInterval3284.hi := by
  norm_num [ratBaseInterval3284, ratTaylorInterval3283,
    ratTaylorSum3283, ratTaylorError3283]

theorem ratInterval_powNat_hi_nonneg3344
    (a : RatInterval3276) (hlo : 0 ≤ a.lo) (hhi : 0 ≤ a.hi) :
    ∀ n, 0 ≤ (RatInterval3276.powNat a n).hi
  | 0 => by norm_num [RatInterval3276.powNat]
  | n + 1 => by
      unfold RatInterval3276.powNat
      dsimp [RatInterval3276.mul]
      apply le_trans
        (mul_nonneg
          (ratInterval_powNat_hi_nonneg3344 a hlo hhi n) hlo)
      exact le_trans (le_max_left _ _) (le_max_right _ _)

theorem ratBaseInterval3284_powNat_hi_nonneg3344 (n : ℕ) :
    0 ≤ (RatInterval3276.powNat ratBaseInterval3284 n).hi := by
  exact ratInterval_powNat_hi_nonneg3344 ratBaseInterval3284
    ratBaseInterval3284_lo_nonneg3344 ratBaseInterval3284_hi_nonneg3344 n

theorem ratInterval_mul_order3344 (a b : RatInterval3276) :
    (RatInterval3276.mul a b).lo ≤
      (RatInterval3276.mul a b).hi := by
  unfold RatInterval3276.mul
  calc
    min
        (min (a.lo * b.lo) (a.lo * b.hi))
        (min (a.hi * b.lo) (a.hi * b.hi))
        ≤ min (a.lo * b.lo) (a.lo * b.hi) := min_le_left _ _
    _ ≤ max (a.lo * b.lo) (a.lo * b.hi) :=
      le_trans (min_le_left _ _) (le_max_left _ _)
    _ ≤ max
        (max (a.lo * b.lo) (a.lo * b.hi))
        (max (a.hi * b.lo) (a.hi * b.hi)) := le_max_left _ _

theorem ratInterval_powNat_lo_nonneg3344
    (a : RatInterval3276) (hlo : 0 ≤ a.lo) (hhi : 0 ≤ a.hi) :
    ∀ n, 0 ≤ (RatInterval3276.powNat a n).lo
  | 0 => by norm_num [RatInterval3276.powNat]
  | n + 1 => by
      unfold RatInterval3276.powNat
      dsimp [RatInterval3276.mul]
      apply le_min
      · apply le_min
        · exact mul_nonneg
            (ratInterval_powNat_lo_nonneg3344 a hlo hhi n) hlo
        · exact mul_nonneg
            (ratInterval_powNat_lo_nonneg3344 a hlo hhi n) hhi
      · apply le_min
        · exact mul_nonneg
            (ratInterval_powNat_hi_nonneg3344 a hlo hhi n) hlo
        · exact mul_nonneg
            (ratInterval_powNat_hi_nonneg3344 a hlo hhi n) hhi

theorem ratInterval_powNat_order3344
    (a : RatInterval3276) :
    ∀ n, (RatInterval3276.powNat a n).lo ≤
      (RatInterval3276.powNat a n).hi
  | 0 => by norm_num [RatInterval3276.powNat]
  | n + 1 => by
      unfold RatInterval3276.powNat
      exact ratInterval_mul_order3344 _ _

end ConnesWeilRH.Dev
