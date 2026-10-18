import ConnesWeilRH.Dev.C1RouteBCellRect2902

namespace ConnesWeilRH.Dev

noncomputable def routeBLocalStageZRect2908 : ComplexRect2427 :=
  ComplexRect2427.mk ((1.987794698109531521319423660106520404133121413129593559369033550776606 : ℚ) : ℝ) ((2.013861574620613032648932693386981825796577911760516505483174440338523 : ℚ) : ℝ)
    ((-0.006708710493875596218744770411729341108042591851448337565211759477967063 : ℚ) : ℝ) ((0.009643062445654370475342615516971944180724636541596131025489457605677501 : ℚ) : ℝ)

theorem routeBLocalStageZNormBound2908 {z : ℂ}
    (hz : ComplexRect2427.Mem z routeBLocalStageZRect2908) :
    ‖z‖ ≤ 3 := by
  apply norm_le_of_rect_mem_of_sq_bound2902 routeBLocalStageZRect2908 hz (by norm_num)
  norm_num [routeBLocalStageZRect2908, ComplexRect2427.mk]
  nlinarith

end ConnesWeilRH.Dev
