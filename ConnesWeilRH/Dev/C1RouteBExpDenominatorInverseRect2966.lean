import ConnesWeilRH.Dev.C1RouteBExpDenominatorInverseNorm2965
import ConnesWeilRH.Dev.C1RouteAIntervalAlgebra

namespace ConnesWeilRH.Dev

noncomputable def routeBExpDenominatorInverseRect2966 : ComplexRect2427 :=
  ComplexRect2427.mk (-1) 1 (-1) 1

theorem routeBExpDenominatorInverseRectMem2966 {w : ℂ}
    (hw : ComplexRect2427.Mem w routeBLocalStageExpRect2907) :
    ComplexRect2427.Mem ((w + 1)⁻¹) routeBExpDenominatorInverseRect2966 := by
  have hn := routeBExpDenominatorInverseNorm2965 hw
  have hre := RCLike.abs_re_le_norm ((w + 1)⁻¹)
  have him := RCLike.abs_im_le_norm ((w + 1)⁻¹)
  rw [abs_le] at hre him
  change (-‖(w + 1)⁻¹‖ ≤ ((w + 1)⁻¹).re ∧
    ((w + 1)⁻¹).re ≤ ‖(w + 1)⁻¹‖) at hre
  change (-‖(w + 1)⁻¹‖ ≤ ((w + 1)⁻¹).im ∧
    ((w + 1)⁻¹).im ≤ ‖(w + 1)⁻¹‖) at him
  change (-1 : ℝ) ≤ ((w + 1)⁻¹).re ∧
    ((w + 1)⁻¹).re ≤ 1 ∧
    (-1 : ℝ) ≤ ((w + 1)⁻¹).im ∧
    ((w + 1)⁻¹).im ≤ 1
  refine ⟨?_, ?_, ?_, ?_⟩
  · linarith [hre.1, hn]
  · linarith [hre.2, hn]
  · linarith [him.1, hn]
  · linarith [him.2, hn]

end ConnesWeilRH.Dev
