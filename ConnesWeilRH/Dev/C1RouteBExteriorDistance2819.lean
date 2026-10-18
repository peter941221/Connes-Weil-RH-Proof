import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed

theorem routeB_exterior_distance_lower_bound2819
    {t T y : ℝ} (hT : 0 < T) (hTt : T ≤ t) :
    t * (1 - |y| / T) ≤ |t - y| := by
  have ht : 0 ≤ t := le_trans (le_of_lt hT) hTt
  have hratio : |y| ≤ t * (|y| / T) := by
    have hmul : T * |y| ≤ t * |y| :=
      mul_le_mul_of_nonneg_right hTt (abs_nonneg y)
    calc
      |y| = (T * |y|) / T := by field_simp
      _ ≤ (t * |y|) / T := div_le_div_of_nonneg_right hmul (le_of_lt hT)
      _ = t * (|y| / T) := by ring
  have habs : t - |y| ≤ |t - y| := by
    simpa [abs_of_nonneg ht] using (abs_sub_abs_le_abs_sub t y)
  calc
    t * (1 - |y| / T) = t - t * (|y| / T) := by ring
    _ ≤ t - |y| := sub_le_sub_left hratio t
    _ ≤ |t - y| := habs

end ConnesWeilRH.Source.C1ExplicitSmoothSeed
