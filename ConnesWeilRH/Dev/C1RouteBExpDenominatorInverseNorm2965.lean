import ConnesWeilRH.Dev.C1RouteBExpDenominatorNonzero2964
import Mathlib.Tactic

namespace ConnesWeilRH.Dev

theorem routeBExpDenominatorInverseNorm2965 {w : ℂ}
    (hw : ComplexRect2427.Mem w routeBLocalStageExpRect2907) :
    ‖(w + 1)⁻¹‖ ≤ 1 := by
  have hreal : (1 : ℝ) ≤ (w + 1).re := by
    norm_num [ComplexRect2427.Mem, routeBLocalStageExpRect2907] at hw ⊢
    linarith [hw.1]
  have hnorm : (1 : ℝ) ≤ ‖w + 1‖ := by
    have hsq : (1 : ℝ) ≤ ‖w + 1‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      nlinarith [sq_nonneg (w + 1).im, sq_nonneg ((w + 1).re - 1)]
    nlinarith [norm_nonneg (w + 1)]
  rw [norm_inv]
  exact (inv_le_one₀ (by positivity)).2 hnorm

end ConnesWeilRH.Dev
