import ConnesWeilRH.Dev.C1RouteAWeightedPartitionSum2687

namespace ConnesWeilRH.Dev

theorem record2687Cell0_endpoint_order2797 :
    (binary64Value2674 0xc01a36e2eb1c4331 : ℝ) ≤
      binary64Value2674 0xc01a305532617c20 := by
  norm_num [binary64Value2674, binary64ExponentBits2674,
    binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

theorem record2687Cell0_width_pos2797 :
    0 < (binary64Value2674 0xc01a305532617c20 : ℝ) -
      binary64Value2674 0xc01a36e2eb1c4331 := by
  have h := record2687Cell0_endpoint_order2797
  have hne : (binary64Value2674 0xc01a36e2eb1c4331 : ℝ) ≠
      binary64Value2674 0xc01a305532617c20 := by
    norm_num [binary64Value2674, binary64ExponentBits2674,
      binary64Significand2674, binary64FractionBits2674, binary64Sign2674]
  have hlt : (binary64Value2674 0xc01a36e2eb1c4331 : ℝ) <
      binary64Value2674 0xc01a305532617c20 := lt_of_le_of_ne h hne
  exact sub_pos.mpr hlt

end ConnesWeilRH.Dev
