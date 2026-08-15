import ConnesWeilRH.Dev.C1XiGlobalWeightedZeroSum
import ConnesWeilRH.Dev.C1XiFiniteFactor

/-!
# C1XiHABridge - same-owner H-A1/cofactor interface

H-A1 proves that the multiplicity-weighted regularized zero sum is analytic
off the xi divisor.  A finite xi factorization supplies a different, local
description of the same logarithmic derivative: finite divisor poles plus the
logarithmic derivative of one zero-free cofactor.

This module joins those descriptions without claiming the missing global
Hadamard comparison.  The comparison is a data-bearing contract; once supplied,
the theorem below transports it to the exact cofactor owned by the finite
factorization.
-/

namespace ConnesWeilRH
namespace Source
namespace C1XiHABridge

open CC20ZetaCounting
open C1XiFiniteFactor
open C1XiGlobalWeightedZeroSum
open C1XiVerticalFunctional
open Filter

noncomputable section

/-- The finite pole part carried by one closed-ball xi factor owner. -/
noncomputable def xiFiniteFactorPoleSum
    (c : Complex) (R : Real) (z : Complex) : Complex :=
  ∑ u ∈ (xiClosedBallDivisor_support_finite c R).toFinset,
    (xiClosedBallDivisor c R u : Complex) / (z - u)

/-- The global comparison still needed after H-A1: a single constant and the
regularized weighted zero sum recover the negative xi logarithmic derivative
on a zero-free open ball.  This is a contract, not an axiom or a producer. -/
structure GlobalWeightedLogDerivComparison
    (c : Complex) (R : Real) where
  constant : Complex
  formula : ∀ z ∈ Metric.ball c |R|,
    completedRiemannXi z ≠ 0 →
      negativeXiLogDeriv z = constant + weightedRegularizedZeroSum z

/-- The local finite-factor logarithmic derivative, with its pole sum kept on
the exact same factor owner. -/
theorem negativeXiLogDeriv_eq_neg_factorPole_add_cofactor
    {c : Complex} {R : Real} {g : Complex -> Complex}
    (hanalytic : AnalyticOnNhd Complex g (Metric.closedBall c |R|))
    (hnonzero : ∀ u : Metric.closedBall c |R|, g u ≠ 0)
    (hfactor : completedRiemannXi =ᶠ[codiscreteWithin
      (Metric.closedBall c |R|)]
        xiClosedBallFactor c R • g)
    {z : Complex} (hzball : z ∈ Metric.ball c |R|)
    (hzxi : completedRiemannXi z ≠ 0) :
    negativeXiLogDeriv z =
      -(xiFiniteFactorPoleSum c R z + logDeriv g z) := by
  have hlog :=
    logDeriv_completedRiemannXi_eq_sum_add_cofactor_of_ne_zero
      hanalytic hnonzero hfactor hzball hzxi
  simpa [negativeXiLogDeriv, xiFiniteFactorPoleSum] using
    congrArg Neg.neg hlog

/-- H-A1 plus a global comparison contract read back through the same finite
factor owner.  The result is deliberately local: it identifies the cofactor
logarithmic derivative, but does not assert that the comparison contract is
available for all tests. -/
theorem cofactor_logDeriv_eq_of_globalWeightedComparison
    {c : Complex} {R : Real} {g : Complex -> Complex}
    (hanalytic : AnalyticOnNhd Complex g (Metric.closedBall c |R|))
    (hnonzero : ∀ u : Metric.closedBall c |R|, g u ≠ 0)
    (hfactor : completedRiemannXi =ᶠ[codiscreteWithin
      (Metric.closedBall c |R|)]
        xiClosedBallFactor c R • g)
    (H : GlobalWeightedLogDerivComparison c R)
    {z : Complex} (hzball : z ∈ Metric.ball c |R|)
    (hzxi : completedRiemannXi z ≠ 0) :
    logDeriv g z =
      -H.constant - weightedRegularizedZeroSum z -
        xiFiniteFactorPoleSum c R z := by
  have hlocal := negativeXiLogDeriv_eq_neg_factorPole_add_cofactor
    hanalytic hnonzero hfactor hzball hzxi
  have hglobal := H.formula z hzball hzxi
  rw [hglobal] at hlocal
  linear_combination hlocal

end
end C1XiHABridge
end Source
end ConnesWeilRH
