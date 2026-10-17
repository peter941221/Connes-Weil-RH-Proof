import ConnesWeilRH.Dev.C1SeedEndpointChargeFactor2786

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed

theorem d4_endpoint_charge_lt_d7_endpoint_charge2787 :
    seedEndpointCharge2733 4 < seedEndpointCharge2733 7 := by
  rw [seedEndpointCharge_d4_d7_factor2786.1,
    seedEndpointCharge_d4_d7_factor2786.2]
  have hden : 0 < (2 : ℝ) ^ 4096 := by positivity
  apply (div_lt_div_iff_of_pos_right hden).mpr
  norm_num

theorem d4_d7_endpoint_charge_order_and_tiny2787 :
    seedEndpointCharge2733 4 < seedEndpointCharge2733 7 ∧
      seedEndpointCharge2733 7 < (1 : ℝ) / (10 : ℝ) ^ 1000 := by
  exact ⟨d4_endpoint_charge_lt_d7_endpoint_charge2787,
    seedEndpointCharge_seven_lt2733⟩

end ConnesWeilRH.Source.C1ExplicitSmoothSeed
