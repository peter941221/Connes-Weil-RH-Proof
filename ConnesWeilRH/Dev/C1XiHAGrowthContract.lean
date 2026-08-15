import ConnesWeilRH.Dev.C1XiGlobalDifference

/-!
# C1XiHAGrowthContract - the honest H-A3 growth interface

The global extension from `C1XiGlobalDifference` is analytic, but that fact
does not bound it at large radius.  This file records the exact circle data
needed by the standard minimum-modulus route:

* selected circle radii;
* zero-freeness on each circle;
* a positive lower bound for `‖xi‖` there;
* an upper bound for `‖xi'‖` there; and
* an upper bound for the weighted regularized zero sum.

The consumer proves the resulting bound for `G` on the same circle.  There is
deliberately no producer for the contract: a zero-free circle alone does not
provide a quantitative minimum-modulus or cofactor estimate.
-/

namespace ConnesWeilRH
namespace Source
namespace C1XiHAGrowthContract

open C1XiGlobalDifference
open C1XiGlobalWeightedZeroSum
open CC20ZetaCounting
open scoped Topology

noncomputable section

/-- Data-bearing H-A3 input for origin-centred circles.  The bounds are
separated by owner: the first two concern xi itself, while `zero_sum_bound`
concerns the already-defined weighted spectral sum. -/
structure XiGlobalDifferenceCircleGrowthContract where
  radius : Nat -> Real
  radius_pos : ∀ n, 0 < radius n
  minimum_modulus : Nat -> Real
  minimum_modulus_pos : ∀ n, 0 < minimum_modulus n
  derivative_bound : Nat -> Real
  derivative_bound_nonneg : ∀ n, 0 ≤ derivative_bound n
  zero_sum_bound : Nat -> Real
  zero_sum_bound_nonneg : ∀ n, 0 ≤ zero_sum_bound n
  circle_zero_free : ∀ n z, ‖z‖ = radius n →
    completedRiemannXi z ≠ 0
  minimum_modulus_lower : ∀ n z, ‖z‖ = radius n →
    minimum_modulus n ≤ ‖completedRiemannXi z‖
  derivative_upper : ∀ n z, ‖z‖ = radius n →
    ‖deriv completedRiemannXi z‖ ≤ derivative_bound n
  zero_sum_upper : ∀ n z, ‖z‖ = radius n →
    ‖weightedRegularizedZeroSum z‖ ≤ zero_sum_bound n

/-- Minimum modulus and derivative bounds control the ordinary logarithmic
derivative on a selected circle. -/
theorem xiLogDeriv_norm_le_of_circle_growth
    (H : XiGlobalDifferenceCircleGrowthContract) {n : Nat} {z : Complex}
    (hz : ‖z‖ = H.radius n) :
    ‖logDeriv completedRiemannXi z‖ ≤
      H.derivative_bound n / H.minimum_modulus n := by
  have hxi : completedRiemannXi z ≠ 0 := H.circle_zero_free n z hz
  have hxi_norm_pos : 0 < ‖completedRiemannXi z‖ :=
    norm_pos_iff.mpr hxi
  have hratio :
      ‖deriv completedRiemannXi z‖ / ‖completedRiemannXi z‖ ≤
        H.derivative_bound n / H.minimum_modulus n := by
    calc
      ‖deriv completedRiemannXi z‖ / ‖completedRiemannXi z‖ ≤
          H.derivative_bound n / ‖completedRiemannXi z‖ := by
            exact div_le_div_of_nonneg_right
              (H.derivative_upper n z hz) (norm_nonneg _)
      _ ≤ H.derivative_bound n / H.minimum_modulus n := by
            rw [div_le_div_iff₀ hxi_norm_pos (H.minimum_modulus_pos n)]
            exact mul_le_mul_of_nonneg_left
              (H.minimum_modulus_lower n z hz)
              (H.derivative_bound_nonneg n)
  simpa only [logDeriv_apply, norm_div] using hratio

/-- H-A3 consumer: the global entire difference has the explicit circle
envelope obtained from the minimum-modulus quotient and the weighted zero sum. -/
theorem xiGlobalWeightedDifference_norm_le_of_circle_growth
    (H : XiGlobalDifferenceCircleGrowthContract) {n : Nat} {z : Complex}
    (hz : ‖z‖ = H.radius n) :
    ‖xiGlobalWeightedDifference z‖ ≤
      H.derivative_bound n / H.minimum_modulus n + H.zero_sum_bound n := by
  have hxi : completedRiemannXi z ≠ 0 := H.circle_zero_free n z hz
  rw [xiGlobalWeightedDifference_eq_raw hxi]
  calc
    ‖xiLogDerivWeightedDifferenceRaw z‖ ≤
        ‖logDeriv completedRiemannXi z‖ +
          ‖weightedRegularizedZeroSum z‖ := by
            exact norm_sub_le _ _
    _ ≤ H.derivative_bound n / H.minimum_modulus n +
          H.zero_sum_bound n := by
            exact add_le_add
              (xiLogDeriv_norm_le_of_circle_growth H hz)
              (H.zero_sum_upper n z hz)

end
end C1XiHAGrowthContract
end Source
end ConnesWeilRH
