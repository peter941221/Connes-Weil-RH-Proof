import ConnesWeilRH.Dev.C1RouteBCellRect2902

namespace ConnesWeilRH.Dev

noncomputable def routeBTSourceRect2968 : ComplexRect2427 :=
  ComplexRect2427.mk ((0.02570513720966107516820004278618342597409060983959444748400594937896152 : ℚ) : ℝ)
    ((0.02583658995088249674157397224348267001664784960104077979755659774923487 : ℚ) : ℝ)
    ((-0.04288643050001361018504994356698145303925541636660252293124345724338597 : ℚ) : ℝ)
    ((-0.04280736641875972244182228337821014866472009833437509954950087520328394 : ℚ) : ℝ)

theorem routeBTSourceNonzero2968 {t : ℂ}
    (ht : ComplexRect2427.Mem t routeBTSourceRect2968) : t ≠ 0 := by
  intro hzero
  have him := congrArg Complex.im hzero
  norm_num [routeBTSourceRect2968, ComplexRect2427.Mem] at ht him
  linarith [ht.2.2.1]

end ConnesWeilRH.Dev
