import ConnesWeilRH.Dev.C1XiFiniteLocalResidue

/-!
# C1XiFiniteCommonCircle - common finite-factor xi contour circles

One finite closed-ball factorization can read every xi pole enclosed by a
common circle.  The circle boundary must avoid the whole divisor support of
that factorization owner.  The regularized kernel is holomorphic on the
enclosed disc, while the finite principal part contributes exactly the poles
in the open disc.

No rectangle contour, support-to-source reindexing, contour limit, arithmetic
readback, explicit-formula equality, or RH claim is made here.
-/

namespace ConnesWeilRH
namespace Source
namespace C1XiFiniteCommonCircle

open Filter
open CC20ZetaCounting
open CCM25Concrete.CompactLogConvolution
open C1SpectralWeil
open C1XiFiniteFactor
open C1XiFiniteLocalResidue
open C1XiFinitePrincipalPart
open C1XiFiniteRegularization
open C1XiResidue
open C1XiVerticalFunctional
open scoped BigOperators Topology

/-- A common circle inside one finite-factorization ball reads the complete
finite principal part of `xiContourKernel`.  The finite divisor support is
the ambient support of this factorization owner, and the boundary exclusion
is required for every one of its points. -/
theorem circleIntegral_xiContourKernel_eq_sum_of_factor_support_mem_ball
    (F : CompactLogTest) {c : Complex} {R r : Real} {g : Complex -> Complex}
    (hanalytic : AnalyticOnNhd Complex g (Metric.closedBall c |R|))
    (hnonzero : ∀ u : Metric.closedBall c |R|, g u ≠ 0)
    (hfactor : completedRiemannXi =ᶠ[codiscreteWithin (Metric.closedBall c |R|)]
      xiClosedBallFactor c R • g)
    (hr : 0 < r)
    (hdisc : Metric.closedBall c r ⊆ Metric.ball c |R|)
    (hboundary : ∀ u ∈ (xiClosedBallDivisor_support_finite c R).toFinset,
      u ∉ Metric.sphere c r) :
    (∮ z in C(c, r), xiContourKernel F z) =
      ∑ u ∈ (xiClosedBallDivisor_support_finite c R).toFinset,
        @ite (α := ℂ) (u ∈ Metric.ball c r) (Classical.propDecidable _)
          (-(2 * (Real.pi : Complex) * Complex.I *
            ((xiClosedBallDivisor c R u : Complex) * centeredLaplaceWeight F u)))
          0 := by
  have hxi_nonzero (z : Complex) (hz : z ∈ Metric.sphere c r) :
      completedRiemannXi z ≠ 0 := by
    intro hzero
    have hzball : z ∈ Metric.ball c |R| :=
      hdisc (Metric.sphere_subset_closedBall hz)
    have hzsupport : z ∈ (xiClosedBallDivisor c R).support :=
      (xiClosedBallDivisor_mem_support_iff c R
        (Metric.ball_subset_closedBall hzball)).mpr hzero
    have hzfin : z ∈ (xiClosedBallDivisor_support_finite c R).toFinset :=
      (xiClosedBallDivisor_support_finite c R).mem_toFinset.mpr hzsupport
    exact hboundary z hzfin hz
  have hkernel_eq (z : Complex) (hz : z ∈ Metric.sphere c r) :
      xiContourKernel F z =
        xiClosedBallPrincipalKernel F c R z +
          xiClosedBallRegularizedKernel F c R g z :=
    xiContourKernel_eq_principal_add_regularized F hanalytic hnonzero hfactor
      (hdisc (Metric.sphere_subset_closedBall hz)) (hxi_nonzero z hz)
  have hregular_continuous :
      ContinuousOn (xiClosedBallRegularizedKernel F c R g)
        (Metric.closedBall c r) := by
    intro z hz
    exact
      (differentiableAt_xiClosedBallRegularizedKernel F hanalytic hnonzero
        (hdisc hz)).continuousAt.continuousWithinAt
  have hregular_circle :
      CircleIntegrable (xiClosedBallRegularizedKernel F c R g) c r :=
    (hregular_continuous.mono Metric.sphere_subset_closedBall).circleIntegrable hr.le
  have hxi_continuous : ContinuousOn (xiContourKernel F) (Metric.sphere c r) := by
    intro z hz
    exact
      (differentiableAt_xiContourKernel_of_completedRiemannXi_ne_zero F
        (hxi_nonzero z hz)).continuousAt.continuousWithinAt
  have hxi_circle : CircleIntegrable (xiContourKernel F) c r :=
    hxi_continuous.circleIntegrable hr.le
  have hprincipal_eq : Set.EqOn (xiClosedBallPrincipalKernel F c R)
      (fun z => xiContourKernel F z - xiClosedBallRegularizedKernel F c R g z)
      (Metric.sphere c r) := by
    intro z hz
    calc
      xiClosedBallPrincipalKernel F c R z =
          (xiClosedBallPrincipalKernel F c R z +
            xiClosedBallRegularizedKernel F c R g z) -
              xiClosedBallRegularizedKernel F c R g z := by ring
      _ = xiContourKernel F z - xiClosedBallRegularizedKernel F c R g z := by
        rw [← hkernel_eq z hz]
  have hprincipal_eq_abs : Set.EqOn (xiClosedBallPrincipalKernel F c R)
      (fun z => xiContourKernel F z - xiClosedBallRegularizedKernel F c R g z)
      (Metric.sphere c |r|) := by
    simpa [abs_of_nonneg hr.le] using hprincipal_eq
  have hprincipal_circle :
      CircleIntegrable (xiClosedBallPrincipalKernel F c R) c r := by
    rw [circleIntegrable_congr hprincipal_eq_abs]
    exact hxi_circle.sub hregular_circle
  have hregular_zero :=
    circleIntegral_xiClosedBallRegularizedKernel_eq_zero_of_closedBall_subset
      F hanalytic hnonzero hr.le hdisc
  calc
    (∮ z in C(c, r), xiContourKernel F z) =
        (∮ z in C(c, r),
          xiClosedBallPrincipalKernel F c R z +
            xiClosedBallRegularizedKernel F c R g z) := by
      apply circleIntegral.integral_congr hr.le
      intro z hz
      exact hkernel_eq z hz
    _ = (∮ z in C(c, r), xiClosedBallPrincipalKernel F c R z) +
        (∮ z in C(c, r), xiClosedBallRegularizedKernel F c R g z) :=
      circleIntegral.integral_add hprincipal_circle hregular_circle
    _ = (∮ z in C(c, r), xiClosedBallPrincipalKernel F c R z) := by
      rw [hregular_zero, add_zero]
    _ = ∑ u ∈ (xiClosedBallDivisor_support_finite c R).toFinset,
        @ite (α := ℂ) (u ∈ Metric.ball c r) (Classical.propDecidable _)
          (-(2 * (Real.pi : Complex) * Complex.I *
            ((xiClosedBallDivisor c R u : Complex) * centeredLaplaceWeight F u)))
          0 :=
      circleIntegral_xiClosedBallPrincipalKernel_eq_sum_of_support_mem_ball
        F hr hboundary

end C1XiFiniteCommonCircle
end Source
end ConnesWeilRH
