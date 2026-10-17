import ConnesWeilRH.Dev.C1RepairedOwnerCellChargePositivity2789

namespace ConnesWeilRH.Dev

theorem record2686RepairedOwnerCellCharge_constant_lt_10000_2790 :
    (binary64Value2674 0x40c1696a1ea9e753 : ℝ) < 10000 := by
  norm_num [binary64Value2674, binary64ExponentBits2674,
    binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

theorem record2686RepairedOwnerCellCharge_constant_pos_lt_10000_2790 :
    0 < (binary64Value2674 0x40c1696a1ea9e753 : ℝ) ∧
      (binary64Value2674 0x40c1696a1ea9e753 : ℝ) < 10000 := by
  exact ⟨record2686RepairedOwnerCellCharge_constant_pos2789,
    record2686RepairedOwnerCellCharge_constant_lt_10000_2790⟩

end ConnesWeilRH.Dev
