import ConnesWeilRH.Dev.C1RouteAWeightedPartitionCell0Geometry2797

namespace ConnesWeilRH.Dev

theorem record2687Cell0BaseM0Rect_scalar_bounds2798 :
    (binary64Value2674 0x8000000000000005 : ℝ) ≤
        binary64Value2674 0x0000000000000005 ∧
      (binary64Value2674 0x8000000000000005 : ℝ) ≤
        binary64Value2674 0x0000000000000005 ∧
      0 < (binary64Value2674 0x1e66a09e667f3bcd : ℝ) ∧
      0 < (binary64Value2674 0x1e3eb0b757f44d24 : ℝ) := by
  constructor
  · norm_num [binary64Value2674, binary64ExponentBits2674,
      binary64Significand2674, binary64FractionBits2674, binary64Sign2674]
    have hp : 0 < (2 : ℝ) ^ 1074 := by positivity
    exact (div_le_div_iff_of_pos_right hp).mpr (by norm_num)
  constructor
  · norm_num [binary64Value2674, binary64ExponentBits2674,
      binary64Significand2674, binary64FractionBits2674, binary64Sign2674]
    have hp : 0 < (2 : ℝ) ^ 1074 := by positivity
    exact (div_le_div_iff_of_pos_right hp).mpr (by norm_num)
  constructor
  · norm_num [binary64Value2674, binary64ExponentBits2674,
      binary64Significand2674, binary64FractionBits2674, binary64Sign2674]
  · norm_num [binary64Value2674, binary64ExponentBits2674,
      binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

end ConnesWeilRH.Dev
