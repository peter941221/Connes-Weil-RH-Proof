import Mathlib.Analysis.Complex.Trigonometric

/-!
# Route-A relative-rounding interface

This file does not model a machine or import an unsafe float implementation.
It proves the algebraic bridge that a future IEEE certificate must discharge:
a real relative error `e` with `|e| ≤ u` gives a complex norm radius `u * ‖x‖`.
-/

namespace ConnesWeilRH
namespace Source
namespace C1RouteAFloatRelativeError

theorem norm_real_relative_error_le {x : ℂ} {e u : ℝ}
    (he : |e| ≤ u) (hu : 0 ≤ u) :
    ‖((1 : ℂ) + (e : ℂ)) * x - x‖ ≤ u * ‖x‖ := by
  calc
    ‖((1 : ℂ) + (e : ℂ)) * x - x‖ = ‖(e : ℂ) * x‖ := by
      congr 1
      ring
    _ = ‖(e : ℂ)‖ * ‖x‖ := Complex.norm_mul _ _
    _ = |e| * ‖x‖ := by simp [Real.norm_eq_abs]
    _ ≤ u * ‖x‖ := by
      exact mul_le_mul_of_nonneg_right he (norm_nonneg x)

end C1RouteAFloatRelativeError
end Source
end ConnesWeilRH
