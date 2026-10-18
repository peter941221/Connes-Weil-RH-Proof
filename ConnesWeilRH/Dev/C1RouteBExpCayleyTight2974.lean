import ConnesWeilRH.Dev.C1RouteBExpDenominatorInverseTight2971
import ConnesWeilRH.Dev.C1RouteAIntervalAlgebra

namespace ConnesWeilRH.Dev

noncomputable def routeBExpCayleyTightRect2974 : ComplexRect2427 :=
  ComplexRect2427.mk ((51 : ℝ) / 1000) ((53 : ℝ) / 1000)
    (-(88 : ℝ) / 1000) (-(85 : ℝ) / 1000)

theorem routeBExpCayleyTightRectMem2974 {w : ℂ}
    (hw : ComplexRect2427.Mem w routeBLocalStageExpRect2907) :
    ComplexRect2427.Mem
      ((w - 1) * (w + 1)⁻¹) routeBExpCayleyTightRect2974 := by
  have hminus := ComplexRect2427.mem_sub hw (ComplexRect2427.point_mem (1 : ℂ))
  have hinv := routeBExpDenominatorInverseTightRectMem2971 hw
  have hmul := ComplexRect2427.mem_mul hminus hinv
  change (51 : ℝ) / 1000 ≤
      ((w - 1) * (w + 1)⁻¹).re ∧
    ((w - 1) * (w + 1)⁻¹).re ≤ 53 / 1000 ∧
    (-(88 : ℝ) / 1000) ≤
      ((w - 1) * (w + 1)⁻¹).im ∧
    ((w - 1) * (w + 1)⁻¹).im ≤ -(85 : ℝ) / 1000
  norm_num [routeBExpCayleyTightRect2974, ComplexRect2427.mk,
    ComplexRect2427.Mem, ComplexRect2427.mul, ComplexRect2427.sub,
    ComplexRect2427.point, RealInterval2429.mul, RealInterval2429.sub,
    RealInterval2429.add,
    routeBLocalStageExpRect2907, routeBExpDenominatorInverseTightRect2971] at hmul ⊢
  constructor
  · nlinarith [hmul.1]
  constructor
  · nlinarith [hmul.2.1]
  constructor
  · nlinarith [hmul.2.2.1]
  · nlinarith [hmul.2.2.2]

end ConnesWeilRH.Dev
