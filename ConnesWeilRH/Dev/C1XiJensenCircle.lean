import ConnesWeilRH.Dev.C1XiHAGrowthContract
import Mathlib.Analysis.Complex.JensenFormula

/-!
# C1XiJensenCircle - exact Jensen circle-average brick

This module records the circle-average identity for the completed xi function
at the fixed nonzero base point `2`.  The first theorem is an exact Jensen
identity.  The second theorem only gives the corresponding average lower
bound; it is deliberately not a pointwise minimum-modulus estimate.
-/

namespace ConnesWeilRH
namespace Source
namespace C1XiJensenCircle

open C1SpectralWeil
open CC20ZetaCounting
open Metric
open MeromorphicOn
open Real

noncomputable section

/-- Exact Jensen identity for the completed xi function on a positive-radius
circle centered at `2`.  The divisor is the same finite closed-ball owner used
by the existing spectral counting lemmas. -/
theorem xi_circleAverage_log_norm_eq_jensen
    {R : Real} (hR : 0 < R) :
    circleAverage (fun z : Complex => Real.log ‖completedRiemannXi z‖)
        (2 : Complex) R =
      ∑ᶠ u : Complex,
        (divisor completedRiemannXi (closedBall (2 : Complex) |R|) u : Real) *
          Real.log (R * ‖(2 : Complex) - u‖⁻¹) +
        Real.log ‖completedRiemannXi 2‖ := by
  simpa only [abs_of_pos hR] using
    (analyticOnNhd_completedRiemannXi
        (closedBall (2 : Complex) |R|)).circleAverage_log_norm
      hR.ne' completedRiemannXi_two_ne_zero

/-- The Jensen correction is nonnegative, so the circle average dominates the
center value.  This is an average statement only; it does not bound the
minimum of `‖xi‖` on the circle. -/
theorem xi_circleAverage_log_norm_ge_center
    {R : Real} (hR : 0 < R) :
    Real.log ‖completedRiemannXi 2‖ ≤
      circleAverage (fun z : Complex => Real.log ‖completedRiemannXi z‖)
        (2 : Complex) R := by
  rw [xi_circleAverage_log_norm_eq_jensen hR]
  have hsum : 0 ≤
      ∑ᶠ u : Complex,
        (divisor completedRiemannXi (closedBall (2 : Complex) |R|) u : Real) *
          Real.log (R * ‖(2 : Complex) - u‖⁻¹) := by
    apply finsum_nonneg
    intro u
    by_cases hu : u ∈ closedBall (2 : Complex) |R|
    · by_cases huc : u = (2 : Complex)
      · subst u
        simp
      · have hdiv : 0 ≤
            (divisor completedRiemannXi (closedBall (2 : Complex) |R|) u : Real) := by
          exact_mod_cast (analyticOnNhd_completedRiemannXi _).divisor_nonneg u
        have hdist : ‖(2 : Complex) - u‖ ≤ R := by
          simpa [abs_of_pos hR, dist_eq_norm, norm_sub_rev] using hu
        have hdist_pos : 0 < ‖(2 : Complex) - u‖ := by
          exact norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm huc))
        have hfactor : 1 ≤ R * ‖(2 : Complex) - u‖⁻¹ := by
          have hfactor' : 1 ≤ R / ‖(2 : Complex) - u‖ := by
            exact (le_div_iff₀ hdist_pos).2 (by simpa using hdist)
          simpa [div_eq_mul_inv] using hfactor'
        exact mul_nonneg hdiv (Real.log_nonneg hfactor)
    · simp [hu]
  linarith

end
end C1XiJensenCircle
end Source
end ConnesWeilRH
