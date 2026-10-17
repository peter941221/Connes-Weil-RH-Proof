import ConnesWeilRH.Dev.C1D4D7EndpointTransitionCoef2784

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed

theorem d4d7_endpoint_charge_pos2785 :
    0 < seedEndpointCharge2733 4 ∧
      0 < seedEndpointCharge2733 7 := by
  constructor <;>
    unfold seedEndpointCharge2733 <;>
    norm_num [endpointTransitionCoef2732]

theorem d4d7_endpoint_charge_pos_and_tiny2785 :
    0 < seedEndpointCharge2733 4 ∧
      seedEndpointCharge2733 4 < (1 : ℝ) / (10 : ℝ) ^ 1000 ∧
    0 < seedEndpointCharge2733 7 ∧
      seedEndpointCharge2733 7 < (1 : ℝ) / (10 : ℝ) ^ 1000 := by
  exact ⟨d4d7_endpoint_charge_pos2785.1, seedEndpointCharge_four_lt2733,
    d4d7_endpoint_charge_pos2785.2, seedEndpointCharge_seven_lt2733⟩

end ConnesWeilRH.Source.C1ExplicitSmoothSeed
