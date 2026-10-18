import ConnesWeilRH.Dev.C1RouteBCellRect2902

namespace ConnesWeilRH.Dev

noncomputable def routeBLocalStageExpRect2907 : ComplexRect2427 :=
  ComplexRect2427.mk ((1.091471072801067889000601192512026918088241370040824172943979414318605 : ℚ) : ℝ) ((1.092114197122440176042205996111980717565067907651892845758453791382703 : ℚ) : ℝ)
    ((-0.189230662355657939656614582461383941758169632446291416828971793800962 : ℚ) : ℝ) ((-0.1887745065671433022932095141917248536749438215792154606779940876487567 : ℚ) : ℝ)

theorem routeBLocalStageExpNormBound2907 {z : ℂ}
    (hz : ComplexRect2427.Mem z routeBLocalStageExpRect2907) :
    ‖z‖ ≤ 2 := by
  apply norm_le_of_rect_mem_of_sq_bound2902 routeBLocalStageExpRect2907 hz (by norm_num)
  norm_num [routeBLocalStageExpRect2907, ComplexRect2427.mk]

end ConnesWeilRH.Dev
