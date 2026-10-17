import ConnesWeilRH.Dev.C1D4D7EndpointChargeOrdering2787

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed

theorem d4d7_endpoint_charge_sum_le_twice_d7_2788 :
    seedEndpointCharge2733 4 + seedEndpointCharge2733 7 ≤
      2 * seedEndpointCharge2733 7 := by
  have h := d4_endpoint_charge_lt_d7_endpoint_charge2787
  linarith

theorem d4d7_endpoint_charge_sum_lt_twice_tiny2788 :
    seedEndpointCharge2733 4 + seedEndpointCharge2733 7 <
      2 * ((1 : ℝ) / (10 : ℝ) ^ 1000) := by
  exact lt_of_le_of_lt d4d7_endpoint_charge_sum_le_twice_d7_2788
    (mul_lt_mul_of_pos_left seedEndpointCharge_seven_lt2733 (by norm_num))

end ConnesWeilRH.Source.C1ExplicitSmoothSeed
