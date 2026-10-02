import Mathlib.Analysis.Complex.Norm
import ConnesWeilRH.Dev.C1RouteAIntervalAlgebra

/-  2453 norm bridge: rectangle containment implies a complex-norm upper
bound.  This is the missing consumer side of the 2433/2437/2436 hypothesis
class: the 2436 owner consumer proves that a directed sum rectangle
contains `correctedPhysical`; the 2389/2390 scalar consumers need a norm
bound.  The bridge is owner-independent and uses no numerical data: for
any `z` inside the rectangle, the triangle inequality against the real
and imaginary parts gives `‖z‖ ≤ |z.re| + |z.im|`, and the rectangle
membership bounds each part by the corresponding corner maximum.  The
bound is intentionally the sum of corner maxima (no square root), so a
generator can emit the exact rational target directly. -/

namespace ConnesWeilRH.Dev

theorem norm_le_of_rect_mem_2453 {z : ℂ} (r : ComplexRect2427)
    (h : ComplexRect2427.Mem z r) :
    ‖z‖ ≤ max |r.reLo| |r.reHi| + max |r.imLo| |r.imHi| := by
  refine (Complex.norm_le_abs_re_add_abs_im z).trans ?_
  have hre : |z.re| ≤ max |r.reLo| |r.reHi| := by
    rcases le_total 0 z.re with hpos | hneg
    · rw [abs_of_nonneg hpos]
      exact h.2.1.trans (le_trans (le_abs_self _) (le_max_right _ _))
    · rw [abs_of_nonpos hneg]
      calc -z.re ≤ -r.reLo := neg_le_neg h.1
        _ ≤ |r.reLo| := by
            have habs := le_abs_self (-r.reLo)
            rwa [abs_neg] at habs
        _ ≤ max |r.reLo| |r.reHi| := le_max_left _ _
  have him : |z.im| ≤ max |r.imLo| |r.imHi| := by
    rcases le_total 0 z.im with hpos | hneg
    · rw [abs_of_nonneg hpos]
      exact h.2.2.2.trans (le_trans (le_abs_self _) (le_max_right _ _))
    · rw [abs_of_nonpos hneg]
      calc -z.im ≤ -r.imLo := neg_le_neg h.2.2.1
        _ ≤ |r.imLo| := by
            have habs := le_abs_self (-r.imLo)
            rwa [abs_neg] at habs
        _ ≤ max |r.imLo| |r.imHi| := le_max_left _ _
  exact add_le_add hre him

end ConnesWeilRH.Dev
