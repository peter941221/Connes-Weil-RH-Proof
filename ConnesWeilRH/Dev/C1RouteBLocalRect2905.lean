import ConnesWeilRH.Dev.C1RouteBCellRect2902

namespace ConnesWeilRH.Dev

noncomputable def routeBLocalRect2905 : ComplexRect2427 :=
  ComplexRect2427.mk ((13.00405691538620049785047774525679132435710015900121128769491296583993 : ℚ) : ℝ) ((13.17125490723681143715907357676030107659197252297304341062383209459696 : ℚ) : ℝ)
    ((0.09438924251461978524203732310416612026741755764593763985531696446631966 : ℚ) : ℝ) ((0.2318279351908294256172323404692274367343334925322181357771819665281043 : ℚ) : ℝ)

theorem routeBLocalRectNormBound2905 {z : ℂ}
    (hz : ComplexRect2427.Mem z routeBLocalRect2905) :
    ‖z‖ ≤ (1377903608911727 : ℝ) / 10 ^ 14 := by
  apply norm_le_of_rect_mem_of_sq_bound2902 routeBLocalRect2905 hz (by norm_num)
  norm_num [routeBLocalRect2905, ComplexRect2427.mk]
  nlinarith

end ConnesWeilRH.Dev
