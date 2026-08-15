import ConnesWeilRH.Dev.C1XiGlobalDifference
import ConnesWeilRH.Dev.C1XiQuantitativeHeight
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Liouville

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
open C1XiQuantitativeHeight
open C1SpectralSummability
open C1SpectralWeil
open CC20ZetaCounting
open CC20YoshidaNearZeros
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

/-- The zero-free condition for an origin-centred xi circle. -/
def xiCircleBoundaryAvoidsZeros (R : Real) : Prop :=
  ∀ z : Complex, ‖z‖ = R → completedRiemannXi z ≠ 0

/-- The finite radius values that can occur on a zero in the bounded height
window used to select a circle.  The image is tied to the same source-zero
owner as `finiteHeightZeros`; it is not an arbitrary sampled zero family. -/
noncomputable def xiCircleForbiddenRadii (B : Real) : Finset Real :=
  (finiteHeightZeros (B + 2)).image fun rho => ‖rho.1‖

/- A zero-free compact circle gives a positive minimum modulus.  This is the
qualitative producer available before any quantitative lower-modulus estimate:
the latter remains a separate analytic problem. -/
theorem exists_circle_minimum_modulus
    {r : Real} (hr : 0 < r)
    (hfree : ∀ z : Complex, ‖z‖ = r → completedRiemannXi z ≠ 0) :
    ∃ m : Real, 0 < m ∧ ∀ z : Complex, ‖z‖ = r →
      m ≤ ‖completedRiemannXi z‖ := by
  let S : Set Complex := Metric.sphere 0 r
  have hS : IsCompact S := isCompact_sphere 0 r
  have hSne : S.Nonempty := by
    exact NormedSpace.sphere_nonempty.mpr hr.le
  have hcont : ContinuousOn
      (fun z : Complex => ‖completedRiemannXi z‖) S := by
    exact (differentiable_completedRiemannXi.continuous.norm).continuousOn
  have hpos : ∀ z ∈ S, 0 < ‖completedRiemannXi z‖ := by
    intro z hz
    apply norm_pos_iff.mpr
    apply hfree z
    simpa [S, Metric.mem_sphere, dist_zero_right] using hz
  obtain ⟨m, hm, hmin⟩ := hS.exists_forall_le' hcont hpos
  refine ⟨m, hm, ?_⟩
  intro z hz
  apply hmin z
  simpa [S, Metric.mem_sphere, dist_zero_right] using hz

/-- Every nonnegative base radius has a zero-free circle in the next unit
window.  The auxiliary separation is explicit: it is the same finite-grid
gap used by the height producer, now applied to the radius image of the
bounded source-zero owner. -/
theorem exists_quantitative_xiCircleBoundaryAvoidsZeros
    (B : Real) (hB : 0 ≤ B) :
    ∃ R : Real, B < R ∧ R < B + 1 ∧ 0 < R ∧
      xiCircleBoundaryAvoidsZeros R ∧
      ∀ rho ∈ finiteHeightZeros (B + 2),
        gridGap (xiCircleForbiddenRadii B).card ≤
          |R - ‖rho.1‖| := by
  classical
  let S : Finset Real := xiCircleForbiddenRadii B
  obtain ⟨R, hRwindow, hRsep⟩ := exists_point_Ioo_away_from_finset S B
  have hRpos : 0 < R := lt_of_le_of_lt hB hRwindow.1
  have hsep (rho : sourceNontrivialZeroSet)
      (hrho : rho ∈ finiteHeightZeros (B + 2)) :
      gridGap S.card ≤ |R - ‖rho.1‖| := by
    have hnorm_mem : ‖rho.1‖ ∈ S := by
      dsimp only [S, xiCircleForbiddenRadii]
      exact Finset.mem_image.mpr ⟨rho, hrho, rfl⟩
    exact hRsep _ hnorm_mem
  refine ⟨R, hRwindow.1, hRwindow.2, hRpos, ?_, ?_⟩
  · intro z hz hzero
    let rho : sourceNontrivialZeroSet :=
      ⟨z, sourceNontrivialZero_of_completedRiemannXi_eq_zero hzero⟩
    have hheight : |z.im| ≤ B + 2 := by
      have him : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
      rw [hz] at him
      linarith [hRwindow.2]
    have hrho : rho ∈ finiteHeightZeros (B + 2) := by
      rw [mem_finiteHeightZeros_iff]
      simpa [rho] using hheight
    have hzero_radius : R = ‖rho.1‖ := by
      simpa [rho] using hz.symm
    have hgap_le_zero : gridGap S.card ≤ 0 := by
      rw [hzero_radius] at hsep
      simpa using hsep rho hrho
    exact (not_le_of_gt (gridGap_pos S.card)) hgap_le_zero
  · intro rho hrho
    exact hsep rho hrho

/-- A same-radius certificate combining finite-grid circle selection with the
qualitative compact minimum-modulus producer.  This is deliberately a data
bridge only: no uniform lower-modulus rate is asserted across different `B`. -/
theorem exists_quantitative_xiCircleMinimumModulusCertificate
    (B : Real) (hB : 0 ≤ B) :
    ∃ R m : Real, B < R ∧ R < B + 1 ∧ 0 < m ∧
      xiCircleBoundaryAvoidsZeros R ∧
      (∀ z : Complex, ‖z‖ = R → m ≤ ‖completedRiemannXi z‖) := by
  obtain ⟨R, hRlower, hRupper, hRpos, hfree, _⟩ :=
    exists_quantitative_xiCircleBoundaryAvoidsZeros B hB
  obtain ⟨m, hm, hmin⟩ := exists_circle_minimum_modulus
    hRpos hfree
  exact ⟨R, m, hRlower, hRupper, hm, hfree, hmin⟩

/-- The explicit derivative scale obtained from the existing dyadic xi growth
bound.  This is intentionally an exponential numerator estimate; the
minimum-modulus denominator is a separate H-A3 input. -/
noncomputable def xiDyadicDerivativeBound (n : Nat) : Real :=
  Real.exp (xiGrowthFixedConstant + 1 + 192 * (3 : Real) ^ n)

theorem xiDyadicDerivativeBound_pos (n : Nat) :
    0 < xiDyadicDerivativeBound n := by
  unfold xiDyadicDerivativeBound
  exact Real.exp_pos _

/-- Cauchy's estimate for `xi'` on a dyadic-size ball.  The boundary is first
folded to the right half-plane, so the estimate uses only the existing
functional equation and the unconditional dyadic xi growth theorem. -/
theorem xi_deriv_norm_le_of_norm_le_dyadic
    (n : Nat) {z : Complex}
    (hz : ‖z‖ ≤ (2 : Real) ^ (n + 3)) :
    ‖deriv completedRiemannXi z‖ ≤ xiDyadicDerivativeBound n := by
  have hderiv :
      ‖deriv completedRiemannXi z‖ ≤ xiDyadicDerivativeBound n / 1 := by
    apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
      (c := z) (R := (1 : Real)) (C := xiDyadicDerivativeBound n)
      (f := completedRiemannXi) (by norm_num)
      differentiable_completedRiemannXi.diffContOnCl
    intro w hw
    have hwDist : dist w z = (1 : Real) := by
      simpa only [Metric.mem_sphere] using hw
    have hwNorm : ‖w‖ ≤ ‖z‖ + 1 := by
      calc
        ‖w‖ = ‖(w - z) + z‖ := by rw [sub_add_cancel]
        _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
        _ = dist w z + ‖z‖ := by rw [dist_eq_norm]
        _ = ‖z‖ + 1 := by rw [hwDist]; ring
    have hwNormStrong : ‖w‖ ≤ (2 : Real) ^ (n + 3) + 1 := by
      linarith
    obtain ⟨u, huRe, huNorm, huXi⟩ :=
      exists_half_le_re_norm_le_add_one_and_norm_completedRiemannXi_eq w
    rw [← huXi]
    apply norm_completedRiemannXi_le_exp_of_halfplane_dyadic n huRe
    have hpow : (2 : Real) ≤ (2 : Real) ^ (n + 3) := by
      have hpow' : (2 : Real) ^ 1 ≤ (2 : Real) ^ (n + 3) :=
        pow_right_mono₀ (by norm_num) (by omega)
      simpa using hpow'
    have hpowSucc : (2 : Real) ^ (n + 4) =
        (2 : Real) ^ (n + 3) * 2 := by
      rw [show n + 4 = (n + 3) + 1 by omega, pow_succ]
    calc
      ‖u‖ ≤ ‖w‖ + 1 := huNorm
      _ ≤ (2 : Real) ^ (n + 3) + 2 := by linarith
      _ ≤ (2 : Real) ^ (n + 4) := by
        rw [hpowSucc]
        nlinarith [hpow]
  simpa only [div_one] using hderiv

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

/- The maximum modulus principle transports the same circle estimate to the
closed disc.  This is only a consumer of the circle contract: it does not
produce the missing minimum-modulus or cofactor-growth fields. -/
theorem xiGlobalWeightedDifference_norm_le_of_circle_growth_on_closedBall
    (H : XiGlobalDifferenceCircleGrowthContract) {n : Nat} {z : Complex}
    (hz : ‖z‖ ≤ H.radius n) :
    ‖xiGlobalWeightedDifference z‖ ≤
      H.derivative_bound n / H.minimum_modulus n + H.zero_sum_bound n := by
  have hdiff : Differentiable Complex xiGlobalWeightedDifference :=
    (Complex.analyticOnNhd_univ_iff_differentiable).mp
      xiGlobalWeightedDifference_analyticOnNhd
  apply Complex.norm_le_of_forall_mem_frontier_norm_le
    (Metric.isBounded_ball (x := (0 : Complex)) (r := H.radius n))
    hdiff.diffContOnCl
  · intro w hw
    have hw' : ‖w‖ = H.radius n := by
      rw [frontier_ball (0 : Complex) (ne_of_gt (H.radius_pos n))] at hw
      simpa [Metric.mem_sphere, dist_zero_right] using hw
    exact xiGlobalWeightedDifference_norm_le_of_circle_growth H hw'
  · rw [closure_ball (0 : Complex) (ne_of_gt (H.radius_pos n))]
    simpa [Metric.mem_closedBall, dist_zero_right] using hz

end
end C1XiHAGrowthContract
end Source
end ConnesWeilRH
