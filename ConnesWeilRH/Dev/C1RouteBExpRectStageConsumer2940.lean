import ConnesWeilRH.Dev.C1RouteBComplexExpRectConsumer2937
import ConnesWeilRH.Dev.C1RouteBLocalStageExp2907

namespace ConnesWeilRH.Dev

theorem routeBSubcellExpRectMembership2940 {z : ℂ}
    (hreLo : routeBLocalStageExpRect2907.reLo ≤ Real.exp z.re * Real.cos z.im)
    (hreHi : Real.exp z.re * Real.cos z.im ≤ routeBLocalStageExpRect2907.reHi)
    (himLo : routeBLocalStageExpRect2907.imLo ≤ Real.exp z.re * Real.sin z.im)
    (himHi : Real.exp z.re * Real.sin z.im ≤ routeBLocalStageExpRect2907.imHi) :
    ComplexRect2427.Mem (Complex.exp z) routeBLocalStageExpRect2907 :=
  routeBComplexExp_mem_of_factor_bounds2937 routeBLocalStageExpRect2907
    hreLo hreHi himLo himHi

end ConnesWeilRH.Dev
