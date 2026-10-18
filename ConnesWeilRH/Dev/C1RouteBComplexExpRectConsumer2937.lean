import ConnesWeilRH.Dev.C1RouteBComplexExpCoordinate2936
import ConnesWeilRH.Dev.C1RouteAIntervalAlgebra

namespace ConnesWeilRH.Dev

theorem routeBComplexExp_mem_of_factor_bounds2937 {z : ℂ}
    (r : ComplexRect2427)
    (hreLo : r.reLo ≤ Real.exp z.re * Real.cos z.im)
    (hreHi : Real.exp z.re * Real.cos z.im ≤ r.reHi)
    (himLo : r.imLo ≤ Real.exp z.re * Real.sin z.im)
    (himHi : Real.exp z.re * Real.sin z.im ≤ r.imHi) :
    ComplexRect2427.Mem (Complex.exp z) r := by
  rw [ComplexRect2427.Mem]
  rw [routeBComplexExpReCoordinate2936, routeBComplexExpImCoordinate2936]
  exact ⟨hreLo, hreHi, himLo, himHi⟩

end ConnesWeilRH.Dev
