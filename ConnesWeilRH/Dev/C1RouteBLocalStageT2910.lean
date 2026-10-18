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

theorem routeBLocalStageT_mem_of_trig_bounds2910 (θ : ℝ)
    (hcosLo : (25705137209661075168200042786183425 : ℝ) / 10 ^ 36 ≤ Real.cos θ)
    (hcosHi : Real.cos θ ≤ (25836589950882496741573972243482671 : ℝ) / 10 ^ 36)
    (hsinLo : (-42886430500013610185049943566981453 : ℝ) / 10 ^ 36 ≤ Real.sin θ)
    (hsinHi : Real.sin θ ≤ (-4280736641875972244182228337837814 : ℝ) / 10 ^ 35) :
    ComplexRect2427.Mem
      ((1 / 20 : ℝ) * (Real.cos θ + Complex.I * Real.sin θ))
      routeBLocalStageTRect2910 := by
  constructor
  · norm_num [routeBLocalStageTRect2910, ComplexRect2427.mk]
    nlinarith
  · norm_num [routeBLocalStageTRect2910, ComplexRect2427.mk]
    nlinarith
  · norm_num [routeBLocalStageTRect2910, ComplexRect2427.mk]
    nlinarith
  · norm_num [routeBLocalStageTRect2910, ComplexRect2427.mk]
    nlinarith

theorem routeB_sin_bounds_of_endpoint2911 {a b θ : ℝ}
    (ha : -(Real.pi / 2) ≤ a) (hb : b ≤ Real.pi / 2)
    (hat : a ≤ θ) (htb : θ ≤ b) :
    Real.sin a ≤ Real.sin θ ∧ Real.sin θ ≤ Real.sin b := by
  constructor
  · exact Real.monotoneOn_sin ⟨ha, htb.trans hb⟩ ⟨ha.trans hat, hb⟩ hat
  · exact Real.monotoneOn_sin ⟨ha, hat.trans htb |>.trans hb⟩ ⟨hat, hb⟩ htb

theorem routeB_cos_bounds_of_endpoint2911 {a b θ : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ Real.pi)
    (hat : a ≤ θ) (htb : θ ≤ b) :
    Real.cos b ≤ Real.cos θ ∧ Real.cos θ ≤ Real.cos a := by
  constructor
  · exact Real.antitoneOn_cos ⟨ha, htb.trans hb⟩ ⟨hat, hb⟩ htb
  · exact Real.antitoneOn_cos ⟨ha, hat.trans htb |>.trans hb⟩ ⟨ha, hat⟩ hat

end ConnesWeilRH.Dev
