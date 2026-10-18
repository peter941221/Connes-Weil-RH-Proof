import ConnesWeilRH.Dev.C1RouteBExpDenominatorInverseRect2966
import ConnesWeilRH.Dev.C1RouteAIntervalAlgebra

namespace ConnesWeilRH.Dev

noncomputable def routeBExpMinusOneRect2967 : ComplexRect2427 :=
  ComplexRect2427.sub routeBLocalStageExpRect2907 (ComplexRect2427.point (1 : ℂ))

noncomputable def routeBExpCayleyRect2967 : ComplexRect2427 :=
  ComplexRect2427.mul routeBExpMinusOneRect2967
    routeBExpDenominatorInverseRect2966

theorem routeBExpCayleyRectMem2967 {w : ℂ}
    (hw : ComplexRect2427.Mem w routeBLocalStageExpRect2907) :
    ComplexRect2427.Mem
      ((w - 1) * (w + 1)⁻¹) routeBExpCayleyRect2967 := by
  have hminus := ComplexRect2427.mem_sub hw (ComplexRect2427.point_mem (1 : ℂ))
  have hinv := routeBExpDenominatorInverseRectMem2966 hw
  exact ComplexRect2427.mem_mul hminus hinv

end ConnesWeilRH.Dev
