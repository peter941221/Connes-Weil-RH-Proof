import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import ConnesWeilRH.Dev.C1RouteANormBridge2453

/-  2531: center-plus-scalar-error interface for signed family cancellation.

This file proves only the algebraic transport used by the 2530 payload shape:
keep the complex center sum intact, and charge the perturbation by a scalar
sum.  It imports no numerical payload and makes no producer or RH claim.
-/

namespace ConnesWeilRH.Dev

open scoped BigOperators

set_option linter.style.longLine false

noncomputable def centerErrorNorm2531 (center : ℂ) (error : ℝ) : ℝ :=
  ‖center‖ + error

theorem norm_le_centerError2531 {value center : ℂ} {error : ℝ}
    (herr : ‖value - center‖ ≤ error) :
    ‖value‖ ≤ centerErrorNorm2531 center error := by
  unfold centerErrorNorm2531
  calc
    ‖value‖ = ‖(value - center) + center‖ := by rw [sub_add_cancel]
    _ ≤ ‖value - center‖ + ‖center‖ := norm_add_le _ _
    _ ≤ error + ‖center‖ := by
      simpa [add_comm] using add_le_add_right herr ‖center‖
    _ = ‖center‖ + error := by ring

theorem norm_sum_le_center_sum_add_error2531
    {ι : Type*}
    (s : Finset ι) (value center : ι → ℂ) (error : ι → ℝ)
    (herr : ∀ i ∈ s, ‖value i - center i‖ ≤ error i) :
    ‖s.sum value‖ ≤ ‖s.sum center‖ + s.sum error := by
  have hdiff : s.sum value - s.sum center =
      s.sum (fun i => value i - center i) := by
    rw [Finset.sum_sub_distrib]
  calc
    ‖s.sum value‖ = ‖(s.sum value - s.sum center) + s.sum center‖ := by
      rw [sub_add_cancel]
    _ ≤ ‖s.sum value - s.sum center‖ + ‖s.sum center‖ := norm_add_le _ _
    _ = ‖s.sum (fun i => value i - center i)‖ + ‖s.sum center‖ := by
      rw [hdiff]
    _ ≤ s.sum (fun i => ‖value i - center i‖) + ‖s.sum center‖ := by
      have hnorm : ‖s.sum (fun i => value i - center i)‖ ≤
          s.sum (fun i => ‖value i - center i‖) := norm_sum_le s _
      simpa [add_comm] using add_le_add_right hnorm ‖s.sum center‖
    _ ≤ s.sum error + ‖s.sum center‖ := by
      have hsum : s.sum (fun i => ‖value i - center i‖) ≤ s.sum error :=
        Finset.sum_le_sum fun i hi => herr i hi
      simpa [add_comm] using add_le_add_right hsum ‖s.sum center‖
    _ = ‖s.sum center‖ + s.sum error := by ring

end ConnesWeilRH.Dev


