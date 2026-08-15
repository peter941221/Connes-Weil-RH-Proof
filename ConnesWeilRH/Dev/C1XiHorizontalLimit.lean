import ConnesWeilRH.Dev.C1XiHABridge
import ConnesWeilRH.Dev.C1XiHorizontalDecay

/-!
# C1XiHorizontalLimit - cofactor growth contract and horizontal limit

The finite factorization splits `-xi'/xi` into a finite pole part and the
logarithmic derivative of the same analytic cofactor.  A zero-free tube gives
the pole estimate, but it does not give a uniform estimate for the cofactor.
This file records the missing estimate as data and proves exactly what it buys:
the horizontal contour tends to zero when the resulting envelope is
`o(T^4)` along the selected heights.
-/

namespace ConnesWeilRH
namespace Source
namespace C1XiHorizontalLimit

open Set
open Filter
open CCM25Concrete.CompactLogConvolution
open C1XiFiniteFactor
open C1XiHABridge
open C1XiHorizontalDecay
open C1XiFiniteHeightRectangle
open C1XiFiniteHeightRectangleAssembly
open C1XiVerticalFunctional
open CC20ZetaCounting
open scoped Topology

noncomputable section

/-- A horizontal envelope for the logarithmic derivative of one finite-factor
cofactor.  The cofactor remains tied to its factorization owner. -/
def xiCofactorHorizontalLogDerivEnvelope
    (g : Complex -> Complex) (T M : Real) : Prop :=
  0 <= M ∧
    (∀ x ∈ Icc (0 : Real) 1,
      ‖logDeriv g (verticalPoint x (-T))‖ <= M ∧
        ‖logDeriv g (verticalPoint x T)‖ <= M)

/-- Finite poles plus a cofactor envelope imply the envelope used by the
horizontal contour estimate.  The factorization and all nonzero hypotheses
refer to one and the same cofactor owner. -/
theorem xiHorizontalLogDerivEnvelope_of_factorization
    {c : Complex} {R T P M : Real} {g : Complex -> Complex}
    (hanalytic : AnalyticOnNhd Complex g (Metric.closedBall c |R|))
    (hnonzero : ∀ u : Metric.closedBall c |R|, g u ≠ 0)
    (hfactor : completedRiemannXi =ᶠ[codiscreteWithin
      (Metric.closedBall c |R|)]
        xiClosedBallFactor c R • g)
    (hT : 0 < T) (hP : 0 <= P) (hM : 0 <= M)
    (hball_lower : ∀ x ∈ Icc (0 : Real) 1,
      verticalPoint x (-T) ∈ Metric.ball c |R|)
    (hball_upper : ∀ x ∈ Icc (0 : Real) 1,
      verticalPoint x T ∈ Metric.ball c |R|)
    (hxi_lower : ∀ x ∈ Icc (0 : Real) 1,
      completedRiemannXi (verticalPoint x (-T)) ≠ 0)
    (hxi_upper : ∀ x ∈ Icc (0 : Real) 1,
      completedRiemannXi (verticalPoint x T) ≠ 0)
    (hpole_lower : ∀ x ∈ Icc (0 : Real) 1,
      ‖xiFiniteFactorPoleSum c R (verticalPoint x (-T))‖ <= P)
    (hpole_upper : ∀ x ∈ Icc (0 : Real) 1,
      ‖xiFiniteFactorPoleSum c R (verticalPoint x T)‖ <= P)
    (hcofactor : xiCofactorHorizontalLogDerivEnvelope g T M) :
    xiHorizontalLogDerivEnvelope T (P + M) := by
  rcases hcofactor with ⟨hM', hcofactor⟩
  refine ⟨add_nonneg hP hM', ?_⟩
  intro x hx
  constructor
  · have hlocal := negativeXiLogDeriv_eq_neg_factorPole_add_cofactor
      hanalytic hnonzero hfactor (hball_lower x hx) (hxi_lower x hx)
    rw [hlocal]
    calc
      ‖-(xiFiniteFactorPoleSum c R (verticalPoint x (-T)) +
          logDeriv g (verticalPoint x (-T)))‖ =
          ‖xiFiniteFactorPoleSum c R (verticalPoint x (-T)) +
            logDeriv g (verticalPoint x (-T))‖ := norm_neg _
      _ <= ‖xiFiniteFactorPoleSum c R (verticalPoint x (-T))‖ +
          ‖logDeriv g (verticalPoint x (-T))‖ := norm_add_le _ _
      _ <= P + M := add_le_add (hpole_lower x hx) (hcofactor x hx |>.1)
  · have hlocal := negativeXiLogDeriv_eq_neg_factorPole_add_cofactor
      hanalytic hnonzero hfactor (hball_upper x hx) (hxi_upper x hx)
    rw [hlocal]
    calc
      ‖-(xiFiniteFactorPoleSum c R (verticalPoint x T) +
          logDeriv g (verticalPoint x T))‖ =
          ‖xiFiniteFactorPoleSum c R (verticalPoint x T) +
            logDeriv g (verticalPoint x T)‖ := norm_neg _
      _ <= ‖xiFiniteFactorPoleSum c R (verticalPoint x T)‖ +
          ‖logDeriv g (verticalPoint x T)‖ := norm_add_le _ _
      _ <= P + M := add_le_add (hpole_upper x hx) (hcofactor x hx |>.2)

/-- A data-bearing selected-height contract.  The `boundary_bound` field is
the uniform fourth-order estimate, while `decay` is the genuinely new
cofactor-growth input that makes the horizontal edges vanish. -/
structure XiHorizontalBoundaryGrowthContract
    (F : CompactLogTest) (T M : Nat -> Real) where
  constant : Real
  constant_nonneg : 0 <= constant
  height_pos : ∀ n, 0 < T n
  boundary_avoids : ∀ n, xiHeightBoundaryAvoidsZeros (T n)
  envelopes : ∀ n, xiHorizontalLogDerivEnvelope (T n) (M n)
  boundary_bound : ∀ n,
    ‖criticalStripHorizontalBoundaryIntegral F (T n)‖ <=
      2 * (M n * constant / ‖T n / (2 * Real.pi)‖ ^ 4)
  decay : Tendsto
    (fun n => 2 * (M n * constant / ‖T n / (2 * Real.pi)‖ ^ 4))
    atTop (𝓝 0)

/-- The selected horizontal boundary vanishes under the explicit growth
contract. -/
theorem horizontalBoundary_tendsto_zero_of_growth_contract
    {F : CompactLogTest} {T M : Nat -> Real}
    (H : XiHorizontalBoundaryGrowthContract F T M) :
    Tendsto (fun n => criticalStripHorizontalBoundaryIntegral F (T n))
      atTop (𝓝 0) := by
  exact squeeze_zero_norm H.boundary_bound H.decay

end
end C1XiHorizontalLimit
end Source
end ConnesWeilRH
