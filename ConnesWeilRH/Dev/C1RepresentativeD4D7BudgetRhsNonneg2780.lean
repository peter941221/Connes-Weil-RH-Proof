import ConnesWeilRH.Dev.C1RepresentativeD4D7RationalBudget2762
import ConnesWeilRH.Dev.C1RepresentativeEndpointAbsMaxNonneg2779

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed

theorem representativeD4D7Budget_rhs_nonneg2780 :
    0 ≤ ((2047 : ℝ) / 33554432) * representativeD4Box2755.endpointAbsMax ∧
      0 ≤ ((2047 : ℝ) / 33554432) * representativeD7Box2755.endpointAbsMax := by
  have hw : 0 ≤ (2047 : ℝ) / 33554432 := by norm_num
  exact ⟨mul_nonneg hw representativeD4D7_endpointAbsMax_nonneg2779.1,
    mul_nonneg hw representativeD4D7_endpointAbsMax_nonneg2779.2⟩

end ConnesWeilRH.Source.C1ExplicitSmoothSeed
