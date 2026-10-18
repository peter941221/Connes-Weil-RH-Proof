import ConnesWeilRH.Dev.C1RouteBCellRect2902

namespace ConnesWeilRH.Dev

noncomputable def routeBLocalStageARect2906 : ComplexRect2427 :=
  ComplexRect2427.mk ((0.05115918134672046541552174634792964215154386944411884193763650065071846 : ℚ) : ℝ) ((0.0514255263993234635341891718030249937983159592064787900616296416507478 : ℚ) : ℝ)
    ((-0.08578804744297659024143361682478817688357034125616904487990799395291663 : ℚ) : ℝ) ((-0.08562525278872790740078608676420769253073006717800133087639821109077198 : ℚ) : ℝ)

theorem routeBLocalStageANormBound2906 {z : ℂ}
    (hz : ComplexRect2427.Mem z routeBLocalStageARect2906) :
    ‖z‖ ≤ (40 : ℝ) / 399 := by
  apply norm_le_of_rect_mem_of_sq_bound2902 routeBLocalStageARect2906 hz (by norm_num)
  norm_num [routeBLocalStageARect2906, ComplexRect2427.mk]

end ConnesWeilRH.Dev
