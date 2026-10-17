import ConnesWeilRH.Dev.C1SeedEndpointIntegral2733

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed

noncomputable section

theorem d4d7_endpoint_integral_charges2756 :
    4 * (∫ x in (0 : ℝ)..(1 / 4096),
      ‖iteratedDeriv 4 Real.smoothTransition x‖) ≤ seedEndpointCharge2733 4 ∧
    4 * (∫ x in (0 : ℝ)..(1 / 4096),
      ‖iteratedDeriv 7 Real.smoothTransition x‖) ≤ seedEndpointCharge2733 7 := by
  constructor
  · exact transition_endpoint_integral_le_charge2733 4 (by norm_num) (by norm_num)
  · exact transition_endpoint_integral_le_charge2733 7 (by norm_num) (by norm_num)

theorem d4d7_endpoint_integral_charges_tiny2756 :
    seedEndpointCharge2733 4 < (1 : ℝ) / (10 : ℝ) ^ 1000 ∧
    seedEndpointCharge2733 7 < (1 : ℝ) / (10 : ℝ) ^ 1000 := by
  exact ⟨seedEndpointCharge_four_lt2733, seedEndpointCharge_seven_lt2733⟩

end
end ConnesWeilRH.Source.C1ExplicitSmoothSeed
