import ConnesWeilRH.Dev.C1RouteBCellRect2902

namespace ConnesWeilRH.Dev

noncomputable def routeBLocalStageExpRect2907 : ComplexRect2427 :=
  ComplexRect2427.mk ((1.0914 : ℚ) : ℝ) ((1.0923 : ℚ) : ℝ)
    ((-0.1893 : ℚ) : ℝ) ((-0.1887 : ℚ) : ℝ)

theorem routeBLocalStageExpNormBound2907 {z : ℂ}
    (hz : ComplexRect2427.Mem z routeBLocalStageExpRect2907) :
    ‖z‖ ≤ 2 := by
  apply norm_le_of_rect_mem_of_sq_bound2902 routeBLocalStageExpRect2907 hz (by norm_num)
  norm_num [routeBLocalStageExpRect2907, ComplexRect2427.mk]

end ConnesWeilRH.Dev
