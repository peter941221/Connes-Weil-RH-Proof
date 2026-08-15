import ConnesWeilRH.Dev.C1XiFiniteRegularization
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# C1XiFinitePrincipalPart - finite principal-pole circle integrals

The finite factorization separates the xi contour kernel into principal poles
and a holomorphic remainder.  This file computes the circle integral of one
finite principal part under an explicit geometric condition: the circle
contains its selected pole and no other support point.  It also proves that a
pole outside the closed circle contributes zero.

No punctured rectangle, contour limit, arithmetic readback, explicit-formula
equality, or RH claim is made here.
-/

namespace ConnesWeilRH
namespace Source
namespace C1XiFinitePrincipalPart

open CC20ZetaCounting
open CC20YoshidaNearZeros
open CCM25Concrete.CompactLogConvolution
open C1SpectralWeil
open C1XiFiniteFactor
open C1XiFiniteRegularization
open C1XiVerticalFunctional
open scoped BigOperators Topology

private noncomputable def principalPole
    (F : CompactLogTest) (c : Complex) (R : Real) (u z : Complex) : Complex :=
  -((xiClosedBallDivisor c R u : Complex) * centeredLaplaceWeight F u / (z - u))

private theorem principalPole_eq_const_mul_inv
    (F : CompactLogTest) (c : Complex) (R : Real) (u z : Complex) :
    principalPole F c R u z =
      (-((xiClosedBallDivisor c R u : Complex) * centeredLaplaceWeight F u)) *
        (z - u)⁻¹ := by
  simp only [principalPole, div_eq_mul_inv]
  ring

theorem circleIntegral_principalPole_eq_of_mem_ball
    (F : CompactLogTest) {c : Complex} {R : Real} {u : Complex} {r : Real}
    (hu : u ∈ Metric.ball u r) :
    (∮ z in C(u, r), principalPole F c R u z) =
      -(2 * (Real.pi : Complex) * Complex.I *
        ((xiClosedBallDivisor c R u : Complex) * centeredLaplaceWeight F u)) := by
  rw [show (fun z : Complex => principalPole F c R u z) =
      fun z => (-((xiClosedBallDivisor c R u : Complex) * centeredLaplaceWeight F u)) *
        (z - u)⁻¹ by
        funext z
        exact principalPole_eq_const_mul_inv F c R u z]
  rw [circleIntegral.integral_const_mul, circleIntegral.integral_sub_inv_of_mem_ball hu]
  ring

/-- The same principal-pole readout for an arbitrary enclosing circle. -/
theorem circleIntegral_principalPole_eq_of_mem_ball'
    (F : CompactLogTest) {c center u : Complex} {R r : Real}
    (hu : u ∈ Metric.ball center r) :
    (∮ z in C(center, r), principalPole F c R u z) =
      -(2 * (Real.pi : Complex) * Complex.I *
        ((xiClosedBallDivisor c R u : Complex) * centeredLaplaceWeight F u)) := by
  rw [show (fun z : Complex => principalPole F c R u z) =
      fun z => (-((xiClosedBallDivisor c R u : Complex) * centeredLaplaceWeight F u)) *
        (z - u)⁻¹ by
        funext z
        exact principalPole_eq_const_mul_inv F c R u z]
  rw [circleIntegral.integral_const_mul, circleIntegral.integral_sub_inv_of_mem_ball hu]
  ring

theorem circleIntegral_principalPole_eq_of_mem_center
    (F : CompactLogTest) {c : Complex} {R : Real} {u : Complex} {r : Real}
    (hr : 0 < r) :
    (∮ z in C(u, r), principalPole F c R u z) =
      -(2 * (Real.pi : Complex) * Complex.I *
        ((xiClosedBallDivisor c R u : Complex) * centeredLaplaceWeight F u)) := by
  apply circleIntegral_principalPole_eq_of_mem_ball F
  exact Metric.mem_ball_self hr

theorem circleIntegral_principalPole_eq_zero_of_not_mem_closedBall
    (F : CompactLogTest) {c center u : Complex} {R r : Real}
    (hr : 0 ≤ r) (hu : u ∉ Metric.closedBall center |r|) :
    (∮ z in C(center, r), principalPole F c R u z) = 0 := by
  have hbase : ContinuousOn (fun z : Complex => z - u)
      (Metric.closedBall center |r|) :=
    continuousOn_id.sub continuousOn_const
  have hne : ∀ z ∈ Metric.closedBall center |r|, z - u ≠ 0 := by
    intro z hz hzero
    apply hu
    rw [Metric.mem_closedBall]
    have hzu : z = u := sub_eq_zero.mp hzero
    rw [hzu] at hz
    simpa using hz
  have hinv : ContinuousOn (fun z : Complex => (z - u)⁻¹)
      (Metric.closedBall center |r|) :=
    hbase.inv₀ hne
  have hcont : ContinuousOn (fun z : Complex => principalPole F c R u z)
      (Metric.closedBall center |r|) := by
    rw [show (fun z : Complex => principalPole F c R u z) =
        fun z => (-((xiClosedBallDivisor c R u : Complex) * centeredLaplaceWeight F u)) *
          (z - u)⁻¹ by
          funext z
          exact principalPole_eq_const_mul_inv F c R u z]
    exact continuousOn_const.mul hinv
  have hdiff : ∀ z ∈ Metric.ball center |r|, DifferentiableAt Complex
      (principalPole F c R u) z := by
    intro z hz
    have hz_ne : z - u ≠ 0 := by
      exact hne z (Metric.ball_subset_closedBall hz)
    rw [show principalPole F c R u =
        fun z => (-((xiClosedBallDivisor c R u : Complex) * centeredLaplaceWeight F u)) *
          (z - u)⁻¹ by
          funext z
          exact principalPole_eq_const_mul_inv F c R u z]
    exact (differentiable_const (c :=
      -((xiClosedBallDivisor c R u : Complex) * centeredLaplaceWeight F u))).differentiableAt.mul
      ((differentiableAt_id.sub
        (differentiable_const (c := u)).differentiableAt).inv hz_ne)
  apply Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hr
    Set.countable_empty (f := principalPole F c R u)
  · simpa [abs_of_nonneg hr] using hcont
  · intro z hz
    have hz' : z ∈ Metric.ball center |r| := by
      simpa [abs_of_nonneg hr] using hz.1
    exact hdiff z hz'

/-- On a circle that avoids the finite divisor support, the finite principal
part integrates to the sum of exactly the poles inside that circle.  The
boundary exclusion is deliberately stated for every ambient divisor point of
the same finite factorization owner; it is not inferred from a selected
source-zero family. -/
theorem circleIntegral_xiClosedBallPrincipalKernel_eq_sum_of_support_mem_ball
    (F : CompactLogTest) {c center : Complex} {R r : Real}
    (hr : 0 < r)
    (hboundary : ∀ u ∈ (xiClosedBallDivisor_support_finite c R).toFinset,
      u ∉ Metric.sphere center r) :
    (∮ z in C(center, r), xiClosedBallPrincipalKernel F c R z) =
      ∑ u ∈ (xiClosedBallDivisor_support_finite c R).toFinset,
        @ite (α := ℂ) (u ∈ Metric.ball center r) (Classical.propDecidable _)
          (-(2 * (Real.pi : Complex) * Complex.I *
            ((xiClosedBallDivisor c R u : Complex) * centeredLaplaceWeight F u)))
          0 := by
  classical
  unfold xiClosedBallPrincipalKernel
  have hcircle : ∀ u ∈ (xiClosedBallDivisor_support_finite c R).toFinset,
      CircleIntegrable (fun z : Complex =>
        -((xiClosedBallDivisor c R u : Complex) * centeredLaplaceWeight F u /
          (z - u))) center r := by
    intro u hu
    rw [show (fun z : Complex =>
        -((xiClosedBallDivisor c R u : Complex) * centeredLaplaceWeight F u /
          (z - u))) = fun z =>
        (-((xiClosedBallDivisor c R u : Complex) * centeredLaplaceWeight F u)) *
          (z - u)⁻¹ by
      funext z
      exact principalPole_eq_const_mul_inv F c R u z]
    refine CircleIntegrable.mul_of_continuousOn
      (f := fun z : Complex => (z - u)⁻¹)
      (g := fun _ : Complex => -((xiClosedBallDivisor c R u : Complex) *
        centeredLaplaceWeight F u))
      (circleIntegrable_sub_inv_iff.mpr ?_) continuousOn_const
    right
    intro hus
    exact hboundary u hu (by simpa [abs_of_pos hr] using hus)
  rw [circleIntegral.integral_fun_sum hcircle]
  apply Finset.sum_congr rfl
  intro u hu
  by_cases huinside : u ∈ Metric.ball center r
  · rw [if_pos huinside]
    simpa [principalPole] using
      (circleIntegral_principalPole_eq_of_mem_ball' F (c := c) (center := center)
        (R := R) (u := u) (r := r) huinside)
  · rw [if_neg huinside]
    have hout : u ∉ Metric.closedBall center |r| := by
      intro hclosed
      have hclosed' : dist u center ≤ r := by
        simpa [Metric.mem_closedBall, abs_of_pos hr] using hclosed
      have hnotball : ¬ dist u center < r := by
        simpa [Metric.mem_ball] using huinside
      have heq : dist u center = r :=
        le_antisymm hclosed' (le_of_not_gt hnotball)
      exact hboundary u hu (Metric.mem_sphere.mpr heq)
    exact circleIntegral_principalPole_eq_zero_of_not_mem_closedBall F
      (c := c) (center := center) (R := R) (u := u) (r := r)
      (le_of_lt hr) hout

theorem circleIntegral_xiClosedBallPrincipalKernel_eq_of_unique_support
    (F : CompactLogTest) {c : Complex} {R r : Real}
    {rho : Complex}
    (hr : 0 < r)
    (hrho : rho ∈ (xiClosedBallDivisor_support_finite c R).toFinset)
    (hother : ∀ u ∈ (xiClosedBallDivisor_support_finite c R).toFinset,
      u ≠ rho → u ∉ Metric.closedBall rho r) :
    (∮ z in C(rho, r), xiClosedBallPrincipalKernel F c R z) =
      -(2 * (Real.pi : Complex) * Complex.I *
        ((xiClosedBallDivisor c R rho : Complex) * centeredLaplaceWeight F rho)) := by
  classical
  unfold xiClosedBallPrincipalKernel
  have hcircle : ∀ u ∈ (xiClosedBallDivisor_support_finite c R).toFinset,
      CircleIntegrable (fun z : Complex =>
        -((xiClosedBallDivisor c R u : Complex) * centeredLaplaceWeight F u /
          (z - u))) rho r := by
    intro u hu
    rw [show (fun z : Complex =>
        -((xiClosedBallDivisor c R u : Complex) * centeredLaplaceWeight F u /
          (z - u))) = fun z =>
        (-((xiClosedBallDivisor c R u : Complex) * centeredLaplaceWeight F u)) *
          (z - u)⁻¹ by
      funext z
      exact principalPole_eq_const_mul_inv F c R u z]
    refine CircleIntegrable.mul_of_continuousOn
      (f := fun z : Complex => (z - u)⁻¹)
      (g := fun _ : Complex => -((xiClosedBallDivisor c R u : Complex) *
        centeredLaplaceWeight F u))
      (circleIntegrable_sub_inv_iff.mpr ?_) continuousOn_const
    · right
      intro hus
      by_cases huc : u = rho
      · subst u
        have : (0 : Real) = r := by
          simpa [Metric.mem_sphere, abs_of_pos hr] using hus
        linarith
      · have hnot : u ∉ Metric.closedBall rho |r| := by
          simpa [abs_of_pos hr] using hother u hu huc
        exact hnot (Metric.sphere_subset_closedBall hus)
  rw [circleIntegral.integral_fun_sum hcircle]
  have hterm : ∀ u ∈ (xiClosedBallDivisor_support_finite c R).toFinset,
      (∮ z in C(rho, r),
        -((xiClosedBallDivisor c R u : Complex) * centeredLaplaceWeight F u /
          (z - u))) = if u = rho then
        -(2 * (Real.pi : Complex) * Complex.I *
          ((xiClosedBallDivisor c R u : Complex) * centeredLaplaceWeight F u))
        else 0 := by
    intro u hu
    by_cases huc : u = rho
    · subst u
      simpa [principalPole] using
        (circleIntegral_principalPole_eq_of_mem_center F (c := c) (R := R)
          (u := rho) hr)
    · rw [if_neg huc]
      have hnot : u ∉ Metric.closedBall rho |r| := by
        simpa [abs_of_pos hr] using hother u hu huc
      exact circleIntegral_principalPole_eq_zero_of_not_mem_closedBall F
        (c := c) (center := rho) (R := R) (u := u) (r := r) (le_of_lt hr) hnot
  calc
    (∑ u ∈ (xiClosedBallDivisor_support_finite c R).toFinset,
        ∮ z in C(rho, r),
          -((xiClosedBallDivisor c R u : Complex) * centeredLaplaceWeight F u /
            (z - u))) =
        ∑ u ∈ (xiClosedBallDivisor_support_finite c R).toFinset,
          if u = rho then
            -(2 * (Real.pi : Complex) * Complex.I *
              ((xiClosedBallDivisor c R u : Complex) * centeredLaplaceWeight F u))
          else 0 := by
      apply Finset.sum_congr rfl
      intro u hu
      exact hterm u hu
    _ = -(2 * (Real.pi : Complex) * Complex.I *
          ((xiClosedBallDivisor c R rho : Complex) * centeredLaplaceWeight F rho)) := by
      rw [Finset.sum_ite_eq' _ rho]
      simp [hrho]

/-- On a circle which contains one source-indexed xi zero and no other local
divisor point, the finite principal part contributes exactly the corresponding
one-weight spectral residue.  The ambient closed ball is retained explicitly:
the divisor multiplicity is read back from that same factorization owner. -/
theorem circleIntegral_xiClosedBallPrincipalKernel_eq_neg_spectralTerm_of_unique_support
    (F : CompactLogTest) (rho : sourceNontrivialZeroSet) {c : Complex} {R r : Real}
    (hball : rho.1 ∈ Metric.closedBall c |R|)
    (hr : 0 < r)
    (hother : ∀ u ∈ (xiClosedBallDivisor_support_finite c R).toFinset,
      u ≠ rho.1 → u ∉ Metric.closedBall rho.1 r) :
    (∮ z in C(rho.1, r), xiClosedBallPrincipalKernel F c R z) =
      -(2 * (Real.pi : Complex) * Complex.I * spectralTerm F rho) := by
  have hrho_support : rho.1 ∈ (xiClosedBallDivisor c R).support :=
    (xiClosedBallDivisor_mem_support_iff c R hball).mpr
      (completedRiemannXi_eq_zero_of_sourceNontrivialZero rho.2)
  have hrho_fin : rho.1 ∈ (xiClosedBallDivisor_support_finite c R).toFinset :=
    (xiClosedBallDivisor_support_finite c R).mem_toFinset.mpr hrho_support
  have hprincipal := circleIntegral_xiClosedBallPrincipalKernel_eq_of_unique_support
    F hr hrho_fin hother
  have hdiv : xiClosedBallDivisor c R rho.1 = (xiMultiplicity rho : Int) := by
    change MeromorphicOn.divisor completedRiemannXi (Metric.closedBall c |R|) rho.1 =
      (xiMultiplicity rho : Int)
    exact (xiMultiplicity_cast_eq_divisor_of_mem_closedBall rho hball).symm
  calc
    (∮ z in C(rho.1, r), xiClosedBallPrincipalKernel F c R z) =
        -(2 * (Real.pi : Complex) * Complex.I *
          ((xiClosedBallDivisor c R rho.1 : Complex) * centeredLaplaceWeight F rho.1)) :=
      hprincipal
    _ = -(2 * (Real.pi : Complex) * Complex.I *
          ((xiMultiplicity rho : Complex) * centeredLaplaceWeight F rho.1)) := by
      rw [hdiv]
      norm_num
    _ = -(2 * (Real.pi : Complex) * Complex.I * spectralTerm F rho) := by
      rw [spectralTerm_eq_multiplicity_mul_centeredLaplaceWeight]

end C1XiFinitePrincipalPart
end Source
end ConnesWeilRH
