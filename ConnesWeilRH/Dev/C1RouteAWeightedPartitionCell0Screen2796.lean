import ConnesWeilRH.Dev.C1RouteAWeightedPartitionSum2687

set_option exponentiation.threshold 1000

namespace ConnesWeilRH.Dev

theorem record2687Cell0Charge_lt_40000_2796 :
    (binary64Value2674 0x1e5eb0b757f44d24 : ℝ) < 40000 := by
  rw [show (binary64Value2674 0x1e5eb0b757f44d24 : ℝ) =
      (8638550802451748 : ℝ) / (2 : ℝ) ^ 590 by
      norm_num [binary64Value2674, binary64ExponentBits2674,
        binary64Significand2674, binary64FractionBits2674, binary64Sign2674]]
  have hden : 0 < (2 : ℝ) ^ 590 := by positivity
  apply (div_lt_iff₀ hden).mpr
  norm_num

theorem record2687Cell0Charge_pos_2796 :
    0 < (binary64Value2674 0x1e5eb0b757f44d24 : ℝ) := by
  norm_num [binary64Value2674, binary64ExponentBits2674,
    binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

end ConnesWeilRH.Dev
