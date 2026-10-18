import ConnesWeilRH.Dev.C1RouteBExpFactorProducts2962
import ConnesWeilRH.Dev.C1RouteBExpRectStageConsumer2940

namespace ConnesWeilRH.Dev

theorem routeBSubcellExpRectMembership2963 {z : ℂ}
    (hreLo : (10231836241932215 : ℝ) / 10 ^ 17 ≤ z.re)
    (hreHi : z.re ≤ (103 : ℝ) / 1000)
    (himLo : (-1715760948859532 : ℝ) / 10 ^ 16 ≤ z.im)
    (himHi : z.im ≤ (-1712505045774558 : ℝ) / 10 ^ 16) :
    ComplexRect2427.Mem (Complex.exp z) routeBLocalStageExpRect2907 := by
  have hp := routeBExpFactorProducts2962 hreLo hreHi himLo himHi
  apply routeBSubcellExpRectMembership2940
  · norm_num [routeBLocalStageExpRect2907, ComplexRect2427.mk] at hp ⊢
    linarith [hp.1]
  · norm_num [routeBLocalStageExpRect2907, ComplexRect2427.mk] at hp ⊢
    linarith [hp.2.1]
  · norm_num [routeBLocalStageExpRect2907, ComplexRect2427.mk] at hp ⊢
    linarith [hp.2.2.1]
  · norm_num [routeBLocalStageExpRect2907, ComplexRect2427.mk] at hp ⊢
    linarith [hp.2.2.2]

end ConnesWeilRH.Dev
