import ConnesWeilRH.Dev.C1D4D7EndpointCharges2756

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed

theorem d4d7_endpoint_charge_sum_lt2781 :
    seedEndpointCharge2733 4 + seedEndpointCharge2733 7 <
      (2 : ℝ) / (10 : ℝ) ^ 1000 := by
  have h4 := seedEndpointCharge_four_lt2733
  have h7 := seedEndpointCharge_seven_lt2733
  have hsum : seedEndpointCharge2733 4 + seedEndpointCharge2733 7 <
      (2 : ℝ) / (10 : ℝ) ^ 1000 := by
    convert add_lt_add h4 h7 using 1 <;> ring
  exact hsum

end ConnesWeilRH.Source.C1ExplicitSmoothSeed
