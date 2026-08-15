import ConnesWeilRH.Dev.C1XiFiniteRegularization
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Normed.Module.Convex

/-!
# C1XiFiniteRegularizationCauchy - rectangle interface for Gate 2

The finite-factor regularized kernel is holomorphic on the factorization ball.
This module feeds exactly that local statement into Mathlib's rectangular
Cauchy-Goursat theorem.  The rectangle must be supplied inside the owning open
ball; a four-corner variant obtains the inclusion from convexity of the ball.

No principal-pole boundary contribution, contour limit, arithmetic readback,
explicit-formula equality, or RH claim is made here.
-/

namespace ConnesWeilRH
namespace Source
namespace C1XiFiniteRegularizationCauchy

open CC20ZetaCounting
open CCM25Concrete.CompactLogConvolution
open C1XiFiniteFactor
open C1XiFiniteRegularization
open scoped BigOperators Topology

/-- Cauchy-Goursat for a rectangle wholly contained in the local finite-factor
open ball.  The regularized kernel is the only function passed to Cauchy; the
finite principal poles are deliberately kept outside this theorem. -/
theorem integral_boundary_rect_eq_zero_of_rectangle_subset_xiBall
    (F : CompactLogTest) {c : Complex} {R : Real} {g : Complex -> Complex}
    (hanalytic : AnalyticOnNhd Complex g (Metric.closedBall c |R|))
    (hnonzero : ∀ u : Metric.closedBall c |R|, g u ≠ 0)
    {z w : Complex}
    (hrectangle : Complex.Rectangle z w ⊆ Metric.ball c |R|) :
    (∫ x : Real in z.re..w.re,
        xiClosedBallRegularizedKernel F c R g (x + z.im * Complex.I)) -
      (∫ x : Real in z.re..w.re,
        xiClosedBallRegularizedKernel F c R g (x + w.im * Complex.I)) +
      Complex.I • (∫ y : Real in z.im..w.im,
        xiClosedBallRegularizedKernel F c R g (w.re + y * Complex.I)) -
      Complex.I • (∫ y : Real in z.im..w.im,
        xiClosedBallRegularizedKernel F c R g (z.re + y * Complex.I)) = 0 := by
  apply Complex.integral_boundary_rect_eq_zero_of_differentiableOn
  exact (differentiableOn_xiClosedBallRegularizedKernel F hanalytic hnonzero).mono hrectangle

/-- Four corners in the same open ball imply the rectangle inclusion required
by `integral_boundary_rect_eq_zero_of_rectangle_subset_xiBall`. -/
theorem integral_boundary_rect_eq_zero_of_corners_in_xiBall
    (F : CompactLogTest) {c : Complex} {R : Real} {g : Complex -> Complex}
    (hanalytic : AnalyticOnNhd Complex g (Metric.closedBall c |R|))
    (hnonzero : ∀ u : Metric.closedBall c |R|, g u ≠ 0)
    {z w : Complex}
    (hz : z ∈ Metric.ball c |R|)
    (hw : w ∈ Metric.ball c |R|)
    (hzw : z.re + w.im * Complex.I ∈ Metric.ball c |R|)
    (hwz : w.re + z.im * Complex.I ∈ Metric.ball c |R|) :
    (∫ x : Real in z.re..w.re,
        xiClosedBallRegularizedKernel F c R g (x + z.im * Complex.I)) -
      (∫ x : Real in z.re..w.re,
        xiClosedBallRegularizedKernel F c R g (x + w.im * Complex.I)) +
      Complex.I • (∫ y : Real in z.im..w.im,
        xiClosedBallRegularizedKernel F c R g (w.re + y * Complex.I)) -
      Complex.I • (∫ y : Real in z.im..w.im,
        xiClosedBallRegularizedKernel F c R g (z.re + y * Complex.I)) = 0 := by
  apply integral_boundary_rect_eq_zero_of_rectangle_subset_xiBall
    F hanalytic hnonzero
  have hconvex : Convex ℝ (Metric.ball c |R|) := convex_ball c |R|
  exact Complex.Convex.rectangle_subset hconvex hz hw hzw hwz

end C1XiFiniteRegularizationCauchy
end Source
end ConnesWeilRH
