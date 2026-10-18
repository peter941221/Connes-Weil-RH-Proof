import ConnesWeilRH.Dev.C1RouteBLocalStageExp2907
import ConnesWeilRH.Dev.C1RouteAIntervalAlgebra

namespace ConnesWeilRH.Dev

theorem routeBExpDenominatorNonzero2964 {w : ℂ}
    (hw : ComplexRect2427.Mem w routeBLocalStageExpRect2907) :
    w + 1 ≠ 0 := by
  intro hzero
  have hre := congrArg Complex.re hzero
  norm_num [Complex.add_re, routeBLocalStageExpRect2907,
    ComplexRect2427.Mem] at hw hre
  linarith [hw.1]

end ConnesWeilRH.Dev
