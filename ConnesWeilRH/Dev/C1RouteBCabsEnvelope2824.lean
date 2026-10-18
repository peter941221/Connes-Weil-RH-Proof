import ConnesWeilRH.Dev.C1RouteBCoefficientQuotientBound2823

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed

theorem routeB_cabs_envelope2824
    {y Y Q L S : ℝ}
    (hy : 0 ≤ Y) (hS : 0 < S) (hL : 0 < L)
    (hyY : |y| ≤ Y) (hLQ : L ≤ |Q|) :
    |y| / (S * |Q|) ≤ Y / (S * L) := by
  have hmain := routeB_coefficient_scaled_quotient_bound2823
    (Y := Y) (L := L) (D := |Q|) (S := S) hy hS hL hLQ
  have hQ : 0 < |Q| := lt_of_lt_of_le hL hLQ
  have hden : 0 < S * |Q| := mul_pos hS hQ
  exact le_trans ((div_le_div_iff_of_pos_right hden).2 hyY) hmain

end ConnesWeilRH.Source.C1ExplicitSmoothSeed
