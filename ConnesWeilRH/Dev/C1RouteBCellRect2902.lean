import ConnesWeilRH.Dev.C1RouteANormBridge2453

namespace ConnesWeilRH.Dev

/- Representative 256-cell rectangle (cell 214), generated from the
   committed 2889 artifact.  Membership remains an explicit premise until
   interval soundness is formalized. -/
noncomputable def routeBCellRect2902 : ComplexRect2427 :=
  ComplexRect2427.mk ((12.38798369147758383550008930781557878573645385892358563185294828556948 : ℚ) : ℝ) ((13.75960204634963355062811181245732141228968461863747844108312595734489 : ℚ) : ℝ)
    ((-0.4018516673523189155353809936589514532296302852328021989462456756841968 : ℚ) : ℝ) ((0.7315648100385260157546419408619820736028488292369928838707634870253127 : ℚ) : ℝ)

theorem routeBCellRectNormBound2902 {z : ℂ}
    (hz : ComplexRect2427.Mem z routeBCellRect2902) :
    ‖z‖ ≤ 15 := by
  have h := norm_le_of_rect_mem_2453 routeBCellRect2902 hz
  norm_num [routeBCellRect2902, ComplexRect2427.mk] at h ⊢
  exact h.trans (by norm_num)

end ConnesWeilRH.Dev
