import ConnesWeilRH.Dev.C1RouteBCauchyRemainder2891
import ConnesWeilRH.Dev.C1RouteBCellRect2902

namespace ConnesWeilRH.Dev

noncomputable def routeBLocalStageTRect2910 : ComplexRect2427 :=
  ComplexRect2427.mk ((0.02570513720966107516820004278618342597409060983959444748400594937896152 : ℚ) : ℝ) ((0.02583658995088249674157397224348267001664784960104077979755659774923487 : ℚ) : ℝ)
    ((-0.04288643050001361018504994356698145303925541636660252293124345724338597 : ℚ) : ℝ) ((-0.04280736641875972244182228337821014866472009833437509954950087520328394 : ℚ) : ℝ)

theorem routeBLocalStageTNormBound2910 {z : ℂ}
    (hz : ComplexRect2427.Mem z routeBLocalStageTRect2910) :
    ‖z‖ ≤ (1 : ℝ) / 20 := by
  apply norm_le_of_rect_mem_of_sq_bound2902 routeBLocalStageTRect2910 hz (by norm_num)
  norm_num [routeBLocalStageTRect2910, ComplexRect2427.mk]
  nlinarith

theorem routeBLocalArgumentNormBound2910 {z : ℂ}
    (hz : ComplexRect2427.Mem z routeBLocalStageTRect2910) :
    ‖2 * z / (1 - z ^ 2)‖ ≤ (40 : ℝ) / 399 := by
  exact routeBArgumentNormBound2900 z (routeBLocalStageTNormBound2910 hz)

end ConnesWeilRH.Dev
