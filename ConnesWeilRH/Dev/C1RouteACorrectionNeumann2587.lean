import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

namespace ConnesWeilRH.Dev

/-- A strict Neumann defect makes the composed operator injective.
This is the norm-only algebraic part of the finite-dimensional Neumann gate;
it does not certify a numerical defect for the analytic moment matrix. -/
theorem injective_of_norm_sub_id_lt_one2587
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A X : E →L[ℂ] E)
    (hdefect : ‖(ContinuousLinearMap.id ℂ E) - X.comp A‖ < 1) :
    Function.Injective (X.comp A) := by
  let B : E →L[ℂ] E := X.comp A
  have hdefect_B : ‖(ContinuousLinearMap.id ℂ E) - B‖ < 1 := by
    simpa [B] using hdefect
  intro x y hxy
  have hzero : B (x - y) = 0 := by
    simp only [B, ContinuousLinearMap.comp_apply, map_sub, hxy, sub_self]
  have hidentity :
      B (x - y) + ((ContinuousLinearMap.id ℂ E) - B) (x - y) = x - y := by
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, map_sub]
    abel
  have hnorm : ‖x - y‖ ≤ ‖B (x - y)‖ + ‖((ContinuousLinearMap.id ℂ E) - B) (x - y)‖ := by
    calc
      ‖x - y‖ = ‖B (x - y) + ((ContinuousLinearMap.id ℂ E) - B) (x - y)‖ := by
        rw [hidentity]
      _ ≤ ‖B (x - y)‖ + ‖((ContinuousLinearMap.id ℂ E) - B) (x - y)‖ :=
        norm_add_le _ _
  have hnorm' : ‖x - y‖ ≤ ‖(ContinuousLinearMap.id ℂ E) - B‖ * ‖x - y‖ := by
    calc
      ‖x - y‖ ≤ ‖B (x - y)‖ + ‖((ContinuousLinearMap.id ℂ E) - B) (x - y)‖ := hnorm
      _ ≤ ‖(ContinuousLinearMap.id ℂ E) - B‖ * ‖x - y‖ := by
        rw [hzero, norm_zero]
        have hop := ContinuousLinearMap.le_opNorm ((ContinuousLinearMap.id ℂ E) - B) (x - y)
        linarith
  have hzero_norm : ‖x - y‖ = 0 := by
    have hnonneg : 0 ≤ ‖x - y‖ := norm_nonneg _
    nlinarith [hdefect_B]
  exact sub_eq_zero.mp (norm_eq_zero.mp hzero_norm)


theorem injective_of_norm_sub_id_lt_one2587_left_factor
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A X : E →L[ℂ] E)
    (hdefect : ‖(ContinuousLinearMap.id ℂ E) - X.comp A‖ < 1) :
    Function.Injective A := by
  intro x y hxy
  apply injective_of_norm_sub_id_lt_one2587 A X hdefect
  exact congrArg X hxy
end ConnesWeilRH.Dev