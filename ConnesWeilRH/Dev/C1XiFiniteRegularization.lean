import ConnesWeilRH.Dev.C1XiFiniteFactor
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# C1XiFiniteRegularization - remove finite xi principal parts for Gate 2

On an open ball contained in a finite xi factorization domain, the weighted
xi logarithmic derivative is the sum of its finite principal pole part and a
regularized kernel.  The latter is differentiable on the whole open ball.

This is a local contour interface only.  It does not apply Cauchy's theorem to
a rectangle, take contour limits, identify the arithmetic boundary terms,
prove the explicit formula, or claim RH.
-/

namespace ConnesWeilRH
namespace Source
namespace C1XiFiniteRegularization

open Filter
open CC20ZetaCounting
open CCM25Concrete.CompactLogConvolution
open C1SpectralWeil
open C1XiVerticalFunctional
open C1XiResidue
open C1XiFiniteFactor
open scoped BigOperators Topology

/-- The finite multiplicity-weighted principal part of the xi contour kernel.
This definition is used only away from the local divisor support. -/
noncomputable def xiClosedBallPrincipalKernel
    (F : CompactLogTest) (c : Complex) (R : Real) (z : Complex) : Complex :=
  ∑ u ∈ (xiClosedBallDivisor_support_finite c R).toFinset,
    -((xiClosedBallDivisor c R u : Complex) * centeredLaplaceWeight F u / (z - u))

/-- The finite-factor regularization of the xi contour kernel.  `dslope`
extends the difference quotient of the centered Laplace weight across each
finite divisor point. -/
noncomputable def xiClosedBallRegularizedKernel
    (F : CompactLogTest) (c : Complex) (R : Real) (g : Complex -> Complex) (z : Complex) :
    Complex :=
  -(∑ u ∈ (xiClosedBallDivisor_support_finite c R).toFinset,
      (xiClosedBallDivisor c R u : Complex) * dslope (centeredLaplaceWeight F) u z) -
    logDeriv g z * centeredLaplaceWeight F z

/-- The removable-singularity extension of every centered-Laplace-weight
difference quotient is complex differentiable. -/
theorem differentiable_dslope_centeredLaplaceWeight
    (F : CompactLogTest) (u : Complex) :
    Differentiable Complex (dslope (centeredLaplaceWeight F) u) := by
  intro z
  have hweight : DifferentiableOn Complex (centeredLaplaceWeight F) Set.univ := by
    intro w _hw
    exact (differentiable_centeredLaplaceWeight F w).differentiableWithinAt
  have hdslope : DifferentiableOn Complex (dslope (centeredLaplaceWeight F) u) Set.univ :=
    (Complex.differentiableOn_dslope (s := Set.univ) (c := u) (by simp)).mpr hweight
  simpa only [differentiableWithinAt_univ] using hdslope z (by simp)

/-- Away from xi zeros in the open factorization ball, the weighted xi
logarithmic derivative equals its finite principal part plus the differentiable
finite-factor remainder. -/
theorem xiContourKernel_eq_principal_add_regularized
    (F : CompactLogTest) {c : Complex} {R : Real} {g : Complex -> Complex}
    (hanalytic : AnalyticOnNhd Complex g (Metric.closedBall c |R|))
    (hnonzero : ∀ u : Metric.closedBall c |R|, g u ≠ 0)
    (hfactor : completedRiemannXi =ᶠ[codiscreteWithin (Metric.closedBall c |R|)]
      xiClosedBallFactor c R • g)
    {z : Complex} (hzball : z ∈ Metric.ball c |R|)
    (hzxi : completedRiemannXi z ≠ 0) :
    xiContourKernel F z =
      xiClosedBallPrincipalKernel F c R z +
        xiClosedBallRegularizedKernel F c R g z := by
  classical
  have hlog := logDeriv_completedRiemannXi_eq_sum_add_cofactor_of_ne_zero
    hanalytic hnonzero hfactor hzball hzxi
  have hzu (u : Complex) (hu : u ∈ (xiClosedBallDivisor_support_finite c R).toFinset) :
      z ≠ u := by
    intro hzu
    apply hzxi
    rw [hzu]
    exact (xiClosedBallDivisor_mem_closedBall_and_xi_eq_zero_of_mem_support c R
      ((xiClosedBallDivisor_support_finite c R).mem_toFinset.mp hu)).2
  unfold xiContourKernel negativeXiLogDeriv xiClosedBallPrincipalKernel
    xiClosedBallRegularizedKernel
  rw [hlog]
  calc
    -(∑ u ∈ (xiClosedBallDivisor_support_finite c R).toFinset,
        (xiClosedBallDivisor c R u : Complex) / (z - u) + logDeriv g z) *
        centeredLaplaceWeight F z =
    -(∑ u ∈ (xiClosedBallDivisor_support_finite c R).toFinset,
          (xiClosedBallDivisor c R u : Complex) / (z - u)) * centeredLaplaceWeight F z -
        logDeriv g z * centeredLaplaceWeight F z := by
      ring
    _ =
      (∑ u ∈ (xiClosedBallDivisor_support_finite c R).toFinset,
        -((xiClosedBallDivisor c R u : Complex) / (z - u) * centeredLaplaceWeight F z)) -
        logDeriv g z * centeredLaplaceWeight F z := by
      rw [← Finset.sum_neg_distrib, Finset.sum_mul]
      apply congrArg (fun value : Complex =>
        value - logDeriv g z * centeredLaplaceWeight F z)
      apply Finset.sum_congr rfl
      intro u _hu
      ring
    _ =
      (∑ u ∈ (xiClosedBallDivisor_support_finite c R).toFinset,
        (-((xiClosedBallDivisor c R u : Complex) * centeredLaplaceWeight F u / (z - u)) -
          (xiClosedBallDivisor c R u : Complex) *
            dslope (centeredLaplaceWeight F) u z)) -
        logDeriv g z * centeredLaplaceWeight F z := by
      apply congrArg (fun value : Complex =>
        value - logDeriv g z * centeredLaplaceWeight F z)
      apply Finset.sum_congr rfl
      intro u hu
      rw [dslope_of_ne, slope_def_module]
      · simp only [smul_eq_mul]
        field_simp [hzu u hu]
        ring
      · exact hzu u hu
    _ =
      (∑ u ∈ (xiClosedBallDivisor_support_finite c R).toFinset,
        -((xiClosedBallDivisor c R u : Complex) * centeredLaplaceWeight F u / (z - u))) +
        (-(∑ u ∈ (xiClosedBallDivisor_support_finite c R).toFinset,
          (xiClosedBallDivisor c R u : Complex) *
            dslope (centeredLaplaceWeight F) u z) -
          logDeriv g z * centeredLaplaceWeight F z) := by
      rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
      ring

/-- The finite-factor regularized kernel is differentiable at every interior
point of the closed-ball factorization domain. -/
theorem differentiableAt_xiClosedBallRegularizedKernel
    (F : CompactLogTest) {c : Complex} {R : Real} {g : Complex -> Complex}
    (hanalytic : AnalyticOnNhd Complex g (Metric.closedBall c |R|))
    (hnonzero : ∀ u : Metric.closedBall c |R|, g u ≠ 0)
    {z : Complex} (hzball : z ∈ Metric.ball c |R|) :
    DifferentiableAt Complex (xiClosedBallRegularizedKernel F c R g) z := by
  classical
  unfold xiClosedBallRegularizedKernel
  apply DifferentiableAt.sub
  · apply DifferentiableAt.neg
    have hsum :
        DifferentiableAt Complex
          (∑ u ∈ (xiClosedBallDivisor_support_finite c R).toFinset, fun w =>
            (xiClosedBallDivisor c R u : Complex) * dslope (centeredLaplaceWeight F) u w) z := by
      apply DifferentiableAt.sum
      intro u _hu
      exact
        (differentiable_const (c := (xiClosedBallDivisor c R u : Complex))).differentiableAt.mul
          (differentiable_dslope_centeredLaplaceWeight F u z)
    convert hsum using 1
    ext w
    simp
  · apply DifferentiableAt.mul
    · exact differentiableAt_logDeriv_of_analyticAt_of_ne_zero
        (hanalytic z (Metric.ball_subset_closedBall hzball))
        (hnonzero ⟨z, Metric.ball_subset_closedBall hzball⟩)
    · exact differentiable_centeredLaplaceWeight F z

/-- The finite-factor regularized kernel is differentiable throughout the
open ball.  This is the form consumed by rectangle Cauchy arguments whose
closure is contained in that ball. -/
theorem differentiableOn_xiClosedBallRegularizedKernel
    (F : CompactLogTest) {c : Complex} {R : Real} {g : Complex -> Complex}
    (hanalytic : AnalyticOnNhd Complex g (Metric.closedBall c |R|))
    (hnonzero : ∀ u : Metric.closedBall c |R|, g u ≠ 0) :
    DifferentiableOn Complex (xiClosedBallRegularizedKernel F c R g) (Metric.ball c |R|) := by
  intro z hz
  exact
    (differentiableAt_xiClosedBallRegularizedKernel F hanalytic hnonzero hz).differentiableWithinAt

end C1XiFiniteRegularization
end Source
end ConnesWeilRH
