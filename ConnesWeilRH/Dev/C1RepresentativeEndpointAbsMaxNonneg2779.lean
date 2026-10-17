import ConnesWeilRH.Dev.C1RepresentativeD4D7Boxes2755

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed

open ConnesWeilRH.Dev

theorem representativeD4D7_endpointAbsMax_nonneg2779 :
    0 ≤ representativeD4Box2755.endpointAbsMax ∧
      0 ≤ representativeD7Box2755.endpointAbsMax := by
  constructor <;> unfold RealInterval2429.endpointAbsMax <;>
    exact (abs_nonneg _).trans (le_max_left _ _)

end ConnesWeilRH.Source.C1ExplicitSmoothSeed
