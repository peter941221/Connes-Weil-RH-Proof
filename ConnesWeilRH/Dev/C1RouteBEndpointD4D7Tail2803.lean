import ConnesWeilRH.Dev.C1D4D7EndpointChargeSum2781

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed

theorem routeB_endpoint_d4d7_integral_sum_lt2803 :
    4 * (∫ x in (0 : ℝ)..(1 / 4096),
      ‖iteratedDeriv 4 Real.smoothTransition x‖) +
    4 * (∫ x in (0 : ℝ)..(1 / 4096),
      ‖iteratedDeriv 7 Real.smoothTransition x‖) <
      (2 : ℝ) / (10 : ℝ) ^ 1000 := by
  have h4 := transition_endpoint_integral_le_charge2733 4 (by norm_num) (by norm_num)
  have h7 := transition_endpoint_integral_le_charge2733 7 (by norm_num) (by norm_num)
  have hsum := add_le_add h4 h7
  exact lt_of_le_of_lt hsum d4d7_endpoint_charge_sum_lt2781

end ConnesWeilRH.Source.C1ExplicitSmoothSeed
