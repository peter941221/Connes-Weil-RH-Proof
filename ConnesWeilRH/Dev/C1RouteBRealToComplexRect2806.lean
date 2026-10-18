import ConnesWeilRH.Dev.C1RouteAIntervalAlgebra

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed

open ConnesWeilRH.Dev

theorem complexRect_mem_of_real_bounds2806
    {r : ComplexRect2427} {x : ℝ}
    (hreLo : r.reLo ≤ x) (hreHi : x ≤ r.reHi)
    (himLo : r.imLo ≤ 0) (himHi : 0 ≤ r.imHi) :
    r.Mem (x : ℂ) := by
  rw [ComplexRect2427.Mem]
  simpa using And.intro hreLo (And.intro hreHi (And.intro himLo himHi))

theorem norm_real_coe2806 (x : ℝ) : ‖(x : ℂ)‖ = |x| := by
  simpa using RCLike.norm_ofReal (K := ℂ) x

end ConnesWeilRH.Source.C1ExplicitSmoothSeed
