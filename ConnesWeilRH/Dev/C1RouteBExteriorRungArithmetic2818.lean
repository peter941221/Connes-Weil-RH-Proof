import Mathlib.Data.Int.Basic
import Mathlib.Tactic

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed

theorem routeB_exterior_degree_2818 (k : ℕ) :
    (55 : ℤ) + 2 - 10 * (k : ℤ) = 57 - 10 * (k : ℤ) := by ring

theorem routeB_exterior_degree_nonpositive_2818
    {k : ℕ} (hk : 6 ≤ k) :
    (55 : ℤ) + 2 - 10 * (k : ℤ) ≤ -3 := by
  have hkz : (6 : ℤ) ≤ k := by exact_mod_cast hk
  omega

theorem routeB_exterior_degree_positive_below_six_2818
    {k : ℕ} (hk : k ≤ 5) :
    0 < (55 : ℤ) + 2 - 10 * (k : ℤ) := by
  have hkz : (k : ℤ) ≤ 5 := by exact_mod_cast hk
  omega

end ConnesWeilRH.Source.C1ExplicitSmoothSeed
