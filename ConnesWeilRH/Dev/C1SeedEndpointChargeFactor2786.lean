import ConnesWeilRH.Dev.C1D4D7EndpointChargePositivity2785

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed

theorem seedEndpointCharge_factor2786 (n : ℕ) :
    seedEndpointCharge2733 n =
      (1 / 128 : ℝ) * (endpointTransitionCoef2732 n : ℝ) *
        (4096 : ℝ) ^ (2 * n) / (2 : ℝ) ^ 4096 := by
  unfold seedEndpointCharge2733
  ring

theorem seedEndpointCharge_d4_d7_factor2786 :
    seedEndpointCharge2733 4 =
        (1 / 128 : ℝ) * 5856 * (4096 : ℝ) ^ 8 / (2 : ℝ) ^ 4096 ∧
      seedEndpointCharge2733 7 =
        (1 / 128 : ℝ) * 72179776 * (4096 : ℝ) ^ 14 / (2 : ℝ) ^ 4096 := by
  constructor
  · rw [seedEndpointCharge_factor2786]
    norm_num [endpointTransitionCoef2732]
  · rw [seedEndpointCharge_factor2786]
    norm_num [endpointTransitionCoef2732]

end ConnesWeilRH.Source.C1ExplicitSmoothSeed
