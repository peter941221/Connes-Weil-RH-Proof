import ConnesWeilRH.Dev.C1RouteARationalManifest3276

namespace ConnesWeilRH.Dev

def ratIntervalEndpointAbsBound3325 (a : RatInterval3276) : ℚ :=
  max |a.lo| |a.hi|

theorem ratIntervalEndpointAbsBound3325_nonneg (a : RatInterval3276) :
    0 ≤ ratIntervalEndpointAbsBound3325 a := by
  exact le_trans (abs_nonneg _) (le_max_left _ _)

theorem ratInterval_mul_hi_le_abs_bound3325
    (a b : RatInterval3276) :
    (RatInterval3276.mul a b).hi ≤
      ratIntervalEndpointAbsBound3325 a *
        ratIntervalEndpointAbsBound3325 b := by
  unfold RatInterval3276.mul ratIntervalEndpointAbsBound3325
  apply max_le
  · apply max_le
    · calc
        a.lo * b.lo ≤ |a.lo * b.lo| := le_abs_self _
        _ = |a.lo| * |b.lo| := abs_mul _ _
        _ ≤ max |a.lo| |a.hi| * max |b.lo| |b.hi| := by
          exact mul_le_mul (le_max_left _ _) (le_max_left _ _)
            (abs_nonneg _) (le_trans (abs_nonneg _) (le_max_left _ _))
    · calc
        a.lo * b.hi ≤ |a.lo * b.hi| := le_abs_self _
        _ = |a.lo| * |b.hi| := abs_mul _ _
        _ ≤ max |a.lo| |a.hi| * max |b.lo| |b.hi| := by
          exact mul_le_mul (le_max_left _ _) (le_max_right _ _)
            (abs_nonneg _) (le_trans (abs_nonneg _) (le_max_left _ _))
  · apply max_le
    · calc
        a.hi * b.lo ≤ |a.hi * b.lo| := le_abs_self _
        _ = |a.hi| * |b.lo| := abs_mul _ _
        _ ≤ max |a.lo| |a.hi| * max |b.lo| |b.hi| := by
          exact mul_le_mul (le_max_right _ _) (le_max_left _ _)
            (abs_nonneg _) (le_trans (abs_nonneg _) (le_max_left _ _))
    · calc
        a.hi * b.hi ≤ |a.hi * b.hi| := le_abs_self _
        _ = |a.hi| * |b.hi| := abs_mul _ _
        _ ≤ max |a.lo| |a.hi| * max |b.lo| |b.hi| := by
          exact mul_le_mul (le_max_right _ _) (le_max_right _ _)
            (abs_nonneg _) (le_trans (abs_nonneg _) (le_max_left _ _))

theorem ratInterval_mul_lo_ge_neg_abs_bound3325
    (a b : RatInterval3276) :
    -(ratIntervalEndpointAbsBound3325 a *
        ratIntervalEndpointAbsBound3325 b) ≤
      (RatInterval3276.mul a b).lo := by
  unfold RatInterval3276.mul ratIntervalEndpointAbsBound3325
  apply le_min
  · apply le_min
    · exact neg_le_of_abs_le (by
        rw [abs_mul]
        exact mul_le_mul (le_max_left _ _) (le_max_left _ _)
          (abs_nonneg _) (le_trans (abs_nonneg _) (le_max_left _ _)))
    · exact neg_le_of_abs_le (by
        rw [abs_mul]
        exact mul_le_mul (le_max_left _ _) (le_max_right _ _)
          (abs_nonneg _) (le_trans (abs_nonneg _) (le_max_left _ _)))
  · apply le_min
    · exact neg_le_of_abs_le (by
        rw [abs_mul]
        exact mul_le_mul (le_max_right _ _) (le_max_left _ _)
          (abs_nonneg _) (le_trans (abs_nonneg _) (le_max_left _ _)))
    · exact neg_le_of_abs_le (by
        rw [abs_mul]
        exact mul_le_mul (le_max_right _ _) (le_max_right _ _)
          (abs_nonneg _) (le_trans (abs_nonneg _) (le_max_left _ _)))

end ConnesWeilRH.Dev
