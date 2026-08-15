import ConnesWeilRH.Dev.C1XiFinitePrincipalPart
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# C1XiFiniteLocalResidue - complete local finite-factor xi residues

Inside one finite closed-ball factorization domain, the xi contour kernel is
the sum of its finite principal part and a differentiable regularized kernel.
This module proves that the regularized kernel has zero circle integral on a
closed disc contained in that factorization ball, then combines it with the
finite principal-part calculation for a circle containing exactly one local
divisor point.

No punctured rectangle, contour limit, arithmetic readback, explicit-formula
equality, or RH claim is made here.
-/

namespace ConnesWeilRH
namespace Source
namespace C1XiFiniteLocalResidue

open Filter
open CC20ZetaCounting
open CC20YoshidaNearZeros
open CCM25Concrete.CompactLogConvolution
open C1SpectralWeil
open C1XiFiniteFactor
open C1XiFinitePrincipalPart
open C1XiFiniteRegularization
open C1XiResidue
open C1XiVerticalFunctional
open scoped BigOperators Topology

/-- The regularized finite-factor kernel has zero integral around every circle
whose closed disc lies inside its owning open factorization ball.  This is the
only Cauchy-Goursat use in the finite local-residue assembly. -/
theorem circleIntegral_xiClosedBallRegularizedKernel_eq_zero_of_closedBall_subset
    (F : CompactLogTest) {c : Complex} {R : Real} {g : Complex -> Complex}
    (hanalytic : AnalyticOnNhd Complex g (Metric.closedBall c |R|))
    (hnonzero : ∀ u : Metric.closedBall c |R|, g u ≠ 0)
    {center : Complex} {r : Real}
    (hr : 0 ≤ r)
    (hdisc : Metric.closedBall center r ⊆ Metric.ball c |R|) :
    (∮ z in C(center, r), xiClosedBallRegularizedKernel F c R g z) = 0 := by
  apply Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hr
    Set.countable_empty
  · intro z hz
    exact
      (differentiableAt_xiClosedBallRegularizedKernel F hanalytic hnonzero
        (hdisc hz)).continuousAt.continuousWithinAt
  · intro z hz
    exact differentiableAt_xiClosedBallRegularizedKernel F hanalytic hnonzero
      (hdisc (Metric.ball_subset_closedBall hz.1))

/-- A finite-factor circle around one selected source xi zero has the same
complete weighted residue as the local one-cofactor calculation, provided its
closed disc contains no other divisor support point and stays inside the
factorization ball. -/
theorem circleIntegral_xiContourKernel_eq_neg_spectralTerm_of_factorization_unique_support
    (F : CompactLogTest) (rho : sourceNontrivialZeroSet)
    {c : Complex} {R r : Real} {g : Complex -> Complex}
    (hanalytic : AnalyticOnNhd Complex g (Metric.closedBall c |R|))
    (hnonzero : ∀ u : Metric.closedBall c |R|, g u ≠ 0)
    (hfactor : completedRiemannXi =ᶠ[codiscreteWithin (Metric.closedBall c |R|)]
      xiClosedBallFactor c R • g)
    (hr : 0 < r)
    (hdisc : Metric.closedBall rho.1 r ⊆ Metric.ball c |R|)
    (hother : ∀ u ∈ (xiClosedBallDivisor_support_finite c R).toFinset,
      u ≠ rho.1 → u ∉ Metric.closedBall rho.1 r) :
    (∮ z in C(rho.1, r), xiContourKernel F z) =
      -(2 * (Real.pi : Complex) * Complex.I * spectralTerm F rho) := by
  have hrho_disc : rho.1 ∈ Metric.closedBall rho.1 r := by
    simpa only [Metric.mem_closedBall, dist_self] using hr.le
  have hrho_ball : rho.1 ∈ Metric.ball c |R| := hdisc hrho_disc
  have hrho_owner : rho.1 ∈ Metric.closedBall c |R| :=
    Metric.ball_subset_closedBall hrho_ball
  have hxi_nonzero (z : Complex) (hz : z ∈ Metric.sphere rho.1 r) :
      completedRiemannXi z ≠ 0 := by
    intro hzero
    have hzball : z ∈ Metric.ball c |R| :=
      hdisc (Metric.sphere_subset_closedBall hz)
    have hzsupport : z ∈ (xiClosedBallDivisor c R).support :=
      (xiClosedBallDivisor_mem_support_iff c R
        (Metric.ball_subset_closedBall hzball)).mpr hzero
    have hzfin : z ∈ (xiClosedBallDivisor_support_finite c R).toFinset :=
      (xiClosedBallDivisor_support_finite c R).mem_toFinset.mpr hzsupport
    by_cases hzrho : z = rho.1
    · subst z
      rw [Metric.mem_sphere] at hz
      have hzero_radius : (0 : Real) = r := by
        simpa only [dist_self] using hz
      exact hr.ne' hzero_radius.symm
    · exact (hother z hzfin hzrho) (Metric.sphere_subset_closedBall hz)
  have hkernel_eq (z : Complex) (hz : z ∈ Metric.sphere rho.1 r) :
      xiContourKernel F z =
        xiClosedBallPrincipalKernel F c R z +
          xiClosedBallRegularizedKernel F c R g z :=
    xiContourKernel_eq_principal_add_regularized F hanalytic hnonzero hfactor
      (hdisc (Metric.sphere_subset_closedBall hz)) (hxi_nonzero z hz)
  have hregular_continuous :
      ContinuousOn (xiClosedBallRegularizedKernel F c R g)
        (Metric.closedBall rho.1 r) := by
    intro z hz
    exact
      (differentiableAt_xiClosedBallRegularizedKernel F hanalytic hnonzero
        (hdisc hz)).continuousAt.continuousWithinAt
  have hregular_circle :
      CircleIntegrable (xiClosedBallRegularizedKernel F c R g) rho.1 r :=
    (hregular_continuous.mono Metric.sphere_subset_closedBall).circleIntegrable hr.le
  have hxi_continuous : ContinuousOn (xiContourKernel F) (Metric.sphere rho.1 r) := by
    intro z hz
    exact
      (differentiableAt_xiContourKernel_of_completedRiemannXi_ne_zero F
        (hxi_nonzero z hz)).continuousAt.continuousWithinAt
  have hxi_circle : CircleIntegrable (xiContourKernel F) rho.1 r :=
    hxi_continuous.circleIntegrable hr.le
  have hprincipal_eq : Set.EqOn (xiClosedBallPrincipalKernel F c R)
      (fun z => xiContourKernel F z - xiClosedBallRegularizedKernel F c R g z)
      (Metric.sphere rho.1 r) := by
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
      (Metric.sphere rho.1 |r|) := by
    simpa [abs_of_nonneg hr.le] using hprincipal_eq
  have hprincipal_circle : CircleIntegrable (xiClosedBallPrincipalKernel F c R) rho.1 r := by
    rw [circleIntegrable_congr hprincipal_eq_abs]
    exact hxi_circle.sub hregular_circle
  have hregular_zero :=
    circleIntegral_xiClosedBallRegularizedKernel_eq_zero_of_closedBall_subset
      F hanalytic hnonzero hr.le hdisc
  calc
    (∮ z in C(rho.1, r), xiContourKernel F z) =
        (∮ z in C(rho.1, r),
          xiClosedBallPrincipalKernel F c R z +
            xiClosedBallRegularizedKernel F c R g z) := by
      apply circleIntegral.integral_congr hr.le
      intro z hz
      exact hkernel_eq z hz
    _ = (∮ z in C(rho.1, r), xiClosedBallPrincipalKernel F c R z) +
        (∮ z in C(rho.1, r), xiClosedBallRegularizedKernel F c R g z) :=
      circleIntegral.integral_add hprincipal_circle hregular_circle
    _ = (∮ z in C(rho.1, r), xiClosedBallPrincipalKernel F c R z) := by
      rw [hregular_zero, add_zero]
    _ = -(2 * (Real.pi : Complex) * Complex.I * spectralTerm F rho) :=
      circleIntegral_xiClosedBallPrincipalKernel_eq_neg_spectralTerm_of_unique_support
        F rho hrho_owner hr hother

end C1XiFiniteLocalResidue
end Source
end ConnesWeilRH
