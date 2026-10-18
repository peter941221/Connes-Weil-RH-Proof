import Mathlib.Data.Real.Basic

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed

theorem routeB_coefficient_quotient_bound2823
    {Y L D : ℝ} (hY : 0 ≤ Y) (hL : 0 < L) (hLD : L ≤ D) :
    Y / D ≤ Y / L := by
  have hD : 0 < D := lt_of_lt_of_le hL hLD
  exact div_le_div_of_nonneg_left hY hL hLD

theorem routeB_coefficient_scaled_quotient_bound2823
    {Y L D S : ℝ} (hY : 0 ≤ Y) (hS : 0 < S) (hL : 0 < L)
    (hLD : L ≤ D) :
    Y / (S * D) ≤ Y / (S * L) := by
  have hSD : 0 < S * D := mul_pos hS (lt_of_lt_of_le hL hLD)
  have hSL : 0 < S * L := mul_pos hS hL
  have hden : S * L ≤ S * D := mul_le_mul_of_nonneg_left hLD (le_of_lt hS)
  exact div_le_div_of_nonneg_left hY hSL hden

end ConnesWeilRH.Source.C1ExplicitSmoothSeed
