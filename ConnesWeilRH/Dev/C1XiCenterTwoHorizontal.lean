import ConnesWeilRH.Dev.C1XiCofactorBorel
import ConnesWeilRH.Dev.C1XiHABridge

/-!
# C1XiCenterTwoHorizontal - same-owner horizontal xi growth

This module combines the center-`2` Borel cofactor estimate with the explicit
zero-free dyadic height tubes.  The finite principal part and the cofactor
logarithmic derivative remain attached to the same closed-ball factorization
owner throughout.
-/

namespace ConnesWeilRH
namespace Source
namespace C1XiCenterTwoHorizontal

open Set
open CC20ZetaCounting
open C1SpectralWeil
open C1SpectralSummability
open C1XiFiniteFactor
open C1XiFiniteHeightRectangle
open C1XiHABridge
open C1XiQuantitativeHeight
open C1XiQuantitativePrincipalBound
open C1XiCofactorBorel
open C1XiVerticalFunctional
open scoped BigOperators Topology

noncomputable section

/-- Explicit budget for the complete finite principal part of the center-`2`
factor owner on the selected dyadic horizontal lines. -/
noncomputable def dyadicCenterTwoPrincipalBound (n : Nat) : Real :=
  4 * dyadicCofactorMassBound n *
    (spectralMultiplicityConstant * (3 : Real) ^ (n + 1) + 2)

theorem dyadicCenterTwoPrincipalBound_nonneg (n : Nat) :
    0 ≤ dyadicCenterTwoPrincipalBound n := by
  unfold dyadicCenterTwoPrincipalBound
  have hmass := dyadicCofactorMassBound_nonneg n
  have hsecond :
      0 ≤ spectralMultiplicityConstant * (3 : Real) ^ (n + 1) + 2 := by
    exact add_nonneg
      (mul_nonneg spectralMultiplicityConstant_nonneg (by positivity))
      (by norm_num)
  exact mul_nonneg (mul_nonneg (by norm_num) hmass) hsecond

/-- Every pole of the center-`2` factor remains outside a zero-free tube, so
the exact divisor mass controls its finite principal sum on the tube center. -/
theorem norm_centerTwoPrincipalSum_le_of_tube
    (n : Nat) {t x : Real}
    (htube : ∀ y : Real, ∀ z ∈ Metric.ball (verticalPoint y t)
      (dyadicXiHeightTubeRadius n), completedRiemannXi z ≠ 0) :
    ‖xiClosedBallPrincipalSum (2 : Complex) (dyadicCofactorFactorRadius n)
      (verticalPoint x t)‖ ≤ dyadicCenterTwoPrincipalBound n := by
  have hradius : 0 < dyadicXiHeightTubeRadius n :=
    dyadicXiHeightTubeRadius_pos n
  have hraw := norm_xiClosedBall_principalSum_le_divisorMass_div
    (2 : Complex) (dyadicCofactorFactorRadius n)
      (dyadicXiHeightTubeRadius n) hradius (z := verticalPoint x t) (by
        intro u hu
        by_contra hsep
        have hlt : dist (verticalPoint x t) u < dyadicXiHeightTubeRadius n :=
          lt_of_not_ge hsep
        have huBall : u ∈ Metric.ball (verticalPoint x t)
            (dyadicXiHeightTubeRadius n) := by
          rw [Metric.mem_ball]
          simpa only [dist_comm] using hlt
        exact (htube x u huBall)
          (xiClosedBallDivisor_mem_closedBall_and_xi_eq_zero_of_mem_support
            (2 : Complex) (dyadicCofactorFactorRadius n)
            ((xiClosedBallDivisor_support_finite (2 : Complex)
              (dyadicCofactorFactorRadius n)).mem_toFinset.mp hu)).2)
  calc
    ‖xiClosedBallPrincipalSum (2 : Complex) (dyadicCofactorFactorRadius n)
        (verticalPoint x t)‖ ≤
        xiClosedBallDivisorMass (2 : Complex)
          (dyadicCofactorFactorRadius n) /
            dyadicXiHeightTubeRadius n := hraw
    _ ≤ dyadicCofactorMassBound n / dyadicXiHeightTubeRadius n :=
      div_le_div_of_nonneg_right
        (xiClosedBallDivisorMass_two_dyadic_le n) hradius.le
    _ = dyadicCenterTwoPrincipalBound n := by
      rw [dyadicXiHeightTubeRadius_eq_reciprocal]
      unfold dyadicCenterTwoPrincipalBound
      simp only [div_eq_mul_inv, one_mul, inv_inv]
      ring

/-- One dyadic horizontal owner: a single center-`2` factor/cofactor, one
selected height, its two zero-free tubes, and both same-owner principal-part
bounds. -/
structure DyadicCenterTwoHorizontalData (n : Nat) where
  factorData : DyadicCenterTwoCofactorData n
  height : Real
  height_lower : dyadicCofactorBase n < height
  height_upper : height < dyadicCofactorBase n + 1
  boundary_avoids : xiHeightBoundaryAvoidsZeros height
  upper_tube : ∀ x : Real, ∀ z ∈ Metric.ball (verticalPoint x height)
    (dyadicXiHeightTubeRadius n), completedRiemannXi z ≠ 0
  lower_tube : ∀ x : Real, ∀ z ∈ Metric.ball (verticalPoint x (-height))
    (dyadicXiHeightTubeRadius n), completedRiemannXi z ≠ 0
  principal_upper : ∀ x : Real,
    ‖xiClosedBallPrincipalSum (2 : Complex) (dyadicCofactorFactorRadius n)
      (verticalPoint x height)‖ ≤ dyadicCenterTwoPrincipalBound n
  principal_lower : ∀ x : Real,
    ‖xiClosedBallPrincipalSum (2 : Complex) (dyadicCofactorFactorRadius n)
      (verticalPoint x (-height))‖ ≤ dyadicCenterTwoPrincipalBound n

/-- The Borel factor producer and dyadic tube producer can be selected
independently and then combined because both are indexed by the same scale
`n`; the resulting structure retains the exact factor owner. -/
theorem exists_dyadicCenterTwoHorizontalData (n : Nat) :
    Nonempty (DyadicCenterTwoHorizontalData n) := by
  obtain ⟨D⟩ := exists_dyadic_centerTwo_factorization_analyticLog_boundary_bound n
  obtain ⟨T, hTlower, hTupper, hboundary, hupper, hlower⟩ :=
    exists_dyadic_quantitative_xiHeightBoundaryAvoidsZeros_tubes n
  have hupper' : ∀ x : Real, ∀ z ∈ Metric.ball (verticalPoint x T)
      (dyadicXiHeightTubeRadius n), completedRiemannXi z ≠ 0 := by
    intro x z hz
    apply hupper x z
    simpa only [verticalPoint] using hz
  have hlower' : ∀ x : Real, ∀ z ∈ Metric.ball (verticalPoint x (-T))
      (dyadicXiHeightTubeRadius n), completedRiemannXi z ≠ 0 := by
    intro x z hz
    apply hlower x z
    have hcenter : verticalPoint x (-T) =
        (x : Complex) - T * Complex.I := by
      simp [verticalPoint]
      ring
    rwa [hcenter] at hz
  refine ⟨{
    factorData := D
    height := T
    height_lower := ?_
    height_upper := ?_
    boundary_avoids := hboundary
    upper_tube := hupper'
    lower_tube := hlower'
    principal_upper := fun x =>
      norm_centerTwoPrincipalSum_le_of_tube n hupper'
    principal_lower := fun x =>
      norm_centerTwoPrincipalSum_le_of_tube n hlower' }⟩
  · simpa only [dyadicCofactorBase] using hTlower
  · simpa only [dyadicCofactorBase] using hTupper

theorem DyadicCenterTwoHorizontalData.height_pos
    {n : Nat} (H : DyadicCenterTwoHorizontalData n) : 0 < H.height := by
  have hbase : 0 < dyadicCofactorBase n := by
    unfold dyadicCofactorBase
    positivity
  exact lt_trans hbase H.height_lower

theorem DyadicCenterTwoHorizontalData.height_abs
    {n : Nat} (H : DyadicCenterTwoHorizontalData n) :
    |H.height| = H.height := abs_of_pos H.height_pos

/-- Combined same-owner budget for the negative xi logarithmic derivative. -/
noncomputable def dyadicCenterTwoXiLogDerivBound (n : Nat) : Real :=
  dyadicCenterTwoPrincipalBound n + dyadicCofactorLogDerivBound n

theorem dyadicCenterTwoXiLogDerivBound_nonneg (n : Nat) :
    0 ≤ dyadicCenterTwoXiLogDerivBound n :=
  add_nonneg (dyadicCenterTwoPrincipalBound_nonneg n)
    (dyadicCofactorLogDerivBound_pos n).le

private theorem point_mem_factor_ball
    {n : Nat} {x t : Real}
    (hx : x ∈ Icc (-1 : Real) 2)
    (ht : |t| < dyadicCofactorBase n + 1) :
    verticalPoint x t ∈ Metric.ball (2 : Complex)
      (dyadicCofactorFactorRadius n) := by
  rw [Metric.mem_ball, dist_eq_norm]
  have hinner := norm_verticalPoint_sub_two_lt_dyadic_innerRadius n hx ht
  unfold dyadicCofactorFactorRadius
  linarith

private theorem DyadicCenterTwoHorizontalData.factor_identity
    {n : Nat} (H : DyadicCenterTwoHorizontalData n) {z : Complex}
    (hzball : z ∈ Metric.ball (2 : Complex) (dyadicCofactorFactorRadius n))
    (hzxi : completedRiemannXi z ≠ 0) :
    negativeXiLogDeriv z =
      -(xiClosedBallPrincipalSum (2 : Complex)
          (dyadicCofactorFactorRadius n) z +
        logDeriv H.factorData.cofactor z) := by
  have hRabs : |dyadicCofactorFactorRadius n| =
      dyadicCofactorFactorRadius n :=
    abs_of_pos (dyadicCofactorFactorRadius_pos n)
  have hlocal := negativeXiLogDeriv_eq_neg_factorPole_add_cofactor
    (c := (2 : Complex)) (R := dyadicCofactorFactorRadius n)
    (g := H.factorData.cofactor)
    (by simpa only [hRabs] using H.factorData.cofactor_analytic)
    (fun u => H.factorData.cofactor_nonzero
      ⟨u.1, by simpa only [hRabs] using u.2⟩)
    (by simpa only [hRabs] using H.factorData.factorization)
    (by simpa only [hRabs] using hzball) hzxi
  simpa only [xiFiniteFactorPoleSum, xiClosedBallPrincipalSum] using hlocal

/-- Uniform upper-horizontal estimate on the fixed wide strip `[-1, 2]`. -/
theorem DyadicCenterTwoHorizontalData.norm_negativeXiLogDeriv_upper_le
    {n : Nat} (H : DyadicCenterTwoHorizontalData n) {x : Real}
    (hx : x ∈ Icc (-1 : Real) 2) :
    ‖negativeXiLogDeriv (verticalPoint x H.height)‖ ≤
      dyadicCenterTwoXiLogDerivBound n := by
  have ht : |H.height| < dyadicCofactorBase n + 1 := by
    rw [H.height_abs]
    exact H.height_upper
  have hzball := point_mem_factor_ball hx ht
  have hzxi : completedRiemannXi (verticalPoint x H.height) ≠ 0 :=
    H.upper_tube x _ (Metric.mem_ball_self (dyadicXiHeightTubeRadius_pos n))
  rw [H.factor_identity hzball hzxi]
  calc
    ‖-(xiClosedBallPrincipalSum (2 : Complex)
          (dyadicCofactorFactorRadius n) (verticalPoint x H.height) +
        logDeriv H.factorData.cofactor (verticalPoint x H.height))‖ =
        ‖xiClosedBallPrincipalSum (2 : Complex)
          (dyadicCofactorFactorRadius n) (verticalPoint x H.height) +
        logDeriv H.factorData.cofactor (verticalPoint x H.height)‖ := norm_neg _
    _ ≤ ‖xiClosedBallPrincipalSum (2 : Complex)
          (dyadicCofactorFactorRadius n) (verticalPoint x H.height)‖ +
        ‖logDeriv H.factorData.cofactor
          (verticalPoint x H.height)‖ := norm_add_le _ _
    _ ≤ dyadicCenterTwoPrincipalBound n +
        dyadicCofactorLogDerivBound n :=
      add_le_add (H.principal_upper x)
        (H.factorData.norm_logDeriv_cofactor_le_on_dyadicStrip hx ht)
    _ = dyadicCenterTwoXiLogDerivBound n := rfl

/-- Uniform lower-horizontal estimate on the same fixed wide strip. -/
theorem DyadicCenterTwoHorizontalData.norm_negativeXiLogDeriv_lower_le
    {n : Nat} (H : DyadicCenterTwoHorizontalData n) {x : Real}
    (hx : x ∈ Icc (-1 : Real) 2) :
    ‖negativeXiLogDeriv (verticalPoint x (-H.height))‖ ≤
      dyadicCenterTwoXiLogDerivBound n := by
  have ht : |-H.height| < dyadicCofactorBase n + 1 := by
    rw [abs_neg, H.height_abs]
    exact H.height_upper
  have hzball := point_mem_factor_ball hx ht
  have hzxi : completedRiemannXi (verticalPoint x (-H.height)) ≠ 0 :=
    H.lower_tube x _ (Metric.mem_ball_self (dyadicXiHeightTubeRadius_pos n))
  rw [H.factor_identity hzball hzxi]
  calc
    ‖-(xiClosedBallPrincipalSum (2 : Complex)
          (dyadicCofactorFactorRadius n) (verticalPoint x (-H.height)) +
        logDeriv H.factorData.cofactor (verticalPoint x (-H.height)))‖ =
        ‖xiClosedBallPrincipalSum (2 : Complex)
          (dyadicCofactorFactorRadius n) (verticalPoint x (-H.height)) +
        logDeriv H.factorData.cofactor (verticalPoint x (-H.height))‖ := norm_neg _
    _ ≤ ‖xiClosedBallPrincipalSum (2 : Complex)
          (dyadicCofactorFactorRadius n) (verticalPoint x (-H.height))‖ +
        ‖logDeriv H.factorData.cofactor
          (verticalPoint x (-H.height))‖ := norm_add_le _ _
    _ ≤ dyadicCenterTwoPrincipalBound n +
        dyadicCofactorLogDerivBound n :=
      add_le_add (H.principal_lower x)
        (H.factorData.norm_logDeriv_cofactor_le_on_dyadicStrip hx ht)
    _ = dyadicCenterTwoXiLogDerivBound n := rfl

end
end C1XiCenterTwoHorizontal
end Source
end ConnesWeilRH
