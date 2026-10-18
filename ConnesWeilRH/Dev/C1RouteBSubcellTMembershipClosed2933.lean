import ConnesWeilRH.Dev.C1RouteBSubcellTMembership2928
import ConnesWeilRH.Dev.C1RouteBLeftEndpointClosed2930
import ConnesWeilRH.Dev.C1RouteBLeftCosEndpointClosed2931
import ConnesWeilRH.Dev.C1RouteBRightEndpointsClosed2932

namespace ConnesWeilRH.Dev

theorem routeBSubcellTMembershipClosed2933 {θ : ℝ}
    (hθ : (107 : ℝ) * Real.pi / 64 ≤ θ)
    (hθ' : θ ≤ (107 : ℝ) * Real.pi / 64 + Real.pi / 1024) :
    ComplexRect2427.Mem
      ((1 / 20 : ℝ) * (Real.cos θ + Complex.I * Real.sin θ))
      routeBLocalStageTRect2910 := by
  exact routeBSubcellTMembership2928 hθ hθ'
    (routeBSinLeftEndpointClosed2930.1)
    (routeBSinRightEndpointClosed2932.2)
    (routeBCosLeftEndpointClosed2931.1)
    (routeBCosRightEndpointClosed2932.2)

end ConnesWeilRH.Dev
