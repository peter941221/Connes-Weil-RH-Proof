import ConnesWeilRH.Dev.C1XiFiniteFactor
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Convex.Contractible

/-!
# C1XiAnalyticLog

This module begins the logarithmic control of the zero-free cofactor in the
finite xi factorization.  The first interface retains the exact cofactor owner
and supplies its continuous logarithm on an open ball.  The later analytic
upgrade and quantitative Borel--Caratheodory estimate must consume this same
owner; they may not replace it with an unrelated local factor.
-/

namespace ConnesWeilRH
namespace Source
namespace C1XiAnalyticLog

open Set
open Filter
open CC20ZetaCounting
open C1XiFiniteFactor
open scoped Topology

/-- An open complex ball is simply connected because it is a nonempty convex
set. -/
theorem isSimplyConnected_metric_ball (c : Complex) {R : Real} (hR : 0 < R) :
    IsSimplyConnected (Metric.ball c R) := by
  letI : ContractibleSpace (Metric.ball c R) :=
    (convex_ball c R).contractibleSpace ⟨c, by simpa using hR⟩
  change SimplyConnectedSpace (Metric.ball c R)
  infer_instance

/-- A zero-free analytic function on an open ball admits a continuous branch
of its complex logarithm there. -/
theorem exists_continuousOn_log_of_analyticOnNhd_nonzero_ball
    {g : Complex -> Complex} {c : Complex} {R : Real} (hR : 0 < R)
    (hanalytic : AnalyticOnNhd Complex g (Metric.ball c R))
    (hnonzero : ∀ z ∈ Metric.ball c R, g z ≠ 0) :
    ∃ L : Complex -> Complex,
      ContinuousOn L (Metric.ball c R) ∧
      EqOn (Complex.exp ∘ L) g (Metric.ball c R) := by
  apply Complex.exists_continuousOn_eqOn_exp_comp
    (isSimplyConnected_metric_ball c hR) Metric.isOpen_ball
    hanalytic.continuousOn
  rintro ⟨z, hz, hzero⟩
  exact (hnonzero z hz) hzero

/-- At every nonzero analytic point there is a locally analytic logarithm.
The branch is chosen after rotating by `-1` when the principal logarithm's
slit would otherwise pass through the value.  Its derivative is the intrinsic
logarithmic derivative, so this statement is independent of that branch
choice. -/
theorem exists_local_analytic_log_of_analyticAt_nonzero
    {g : Complex -> Complex} {z : Complex}
    (hanalytic : AnalyticAt Complex g z) (hnonzero : g z ≠ 0) :
    ∃ L : Complex -> Complex,
      AnalyticAt Complex L z ∧
      (∀ᶠ w in 𝓝 z, Complex.exp (L w) = g w) ∧
      deriv L z = logDeriv g z := by
  rcases Complex.mem_slitPlane_or_neg_mem_slitPlane hnonzero with hslit | hslit
  · refine ⟨fun w => Complex.log (g w), hanalytic.clog hslit, ?_, ?_⟩
    · filter_upwards [hanalytic.continuousAt.preimage_mem_nhds
        (Complex.isOpen_slitPlane.mem_nhds hslit)] with w hw
      exact Complex.exp_log (Complex.slitPlane_ne_zero hw)
    · simpa only [Function.comp_def] using
        Complex.deriv_log_comp_eq_logDeriv hanalytic.differentiableAt hslit
  · refine ⟨fun w => Complex.log (-g w) - Complex.log (-1),
      (hanalytic.neg.clog hslit).sub analyticAt_const, ?_, ?_⟩
    · filter_upwards [(hanalytic.neg.continuousAt.preimage_mem_nhds
        (Complex.isOpen_slitPlane.mem_nhds hslit))] with w hw
      have hminus : (-g) w ≠ 0 := Complex.slitPlane_ne_zero hw
      change Complex.exp (Complex.log ((-g) w) - Complex.log (-1)) = g w
      rw [Complex.exp_sub, Complex.exp_log hminus,
        Complex.exp_log (by norm_num : (-1 : Complex) ≠ 0)]
      change (-(g w)) / (-1 : Complex) = g w
      ring
    · rw [deriv_sub_const]
      calc
        deriv (fun w => Complex.log (-g w)) z = logDeriv (fun w => -g w) z := by
          simpa only [Function.comp_def] using
            Complex.deriv_log_comp_eq_logDeriv hanalytic.neg.differentiableAt hslit
        _ = logDeriv g z := by
          simp only [logDeriv_apply, deriv.fun_neg, neg_div_neg_eq]

/-- A continuous logarithm lift of a nonvanishing analytic function is analytic.
At each point, a local analytic branch is translated to agree with the given
lift.  Covering-map uniqueness then identifies the two branches on a small
connected ball, preserving the chosen global lift rather than changing it. -/
theorem analyticOnNhd_of_continuousOn_exp_eqOn
    {U : Set Complex} {g L : Complex -> Complex}
    (hUopen : IsOpen U)
    (hanalytic : AnalyticOnNhd Complex g U)
    (hnonzero : ∀ z ∈ U, g z ≠ 0)
    (hLcont : ContinuousOn L U)
    (hLexp : EqOn (Complex.exp ∘ L) g U) :
    AnalyticOnNhd Complex L U := by
  intro z hz
  obtain ⟨K, hKanalytic, hKexp, _⟩ :=
    exists_local_analytic_log_of_analyticAt_nonzero (hanalytic z hz) (hnonzero z hz)
  let Kshift : Complex -> Complex := fun w => K w + (L z - K z)
  have hKshiftAt : AnalyticAt Complex Kshift z := by
    simpa only [Kshift] using hKanalytic.add analyticAt_const
  have hLexpAt : Complex.exp (L z) = g z := by
    simpa only [Function.comp_apply] using hLexp hz
  have hKexpAt : Complex.exp (K z) = g z := hKexp.self_of_nhds
  have hshiftExp : Complex.exp (L z - K z) = 1 := by
    rw [Complex.exp_sub, hLexpAt, hKexpAt, div_self (hnonzero z hz)]
  have hKshiftExp : ∀ᶠ w in 𝓝 z, Complex.exp (Kshift w) = g w := by
    filter_upwards [hKexp] with w hw
    simp only [Kshift]
    rw [Complex.exp_add, hshiftExp, mul_one, hw]
  obtain ⟨rU, hrU, hUball⟩ := (Metric.isOpen_iff.mp hUopen) z hz
  obtain ⟨rK, hrK, hKball⟩ := hKshiftAt.exists_ball_analyticOnNhd
  obtain ⟨rE, hrE, hEball⟩ := Metric.eventually_nhds_iff_ball.mp hKshiftExp
  let r : Real := min rU (min rK rE)
  have hr : 0 < r := by
    dsimp only [r]
    exact lt_min hrU (lt_min hrK hrE)
  let B : Set Complex := Metric.ball z r
  have hBsubsetU : B ⊆ U := by
    intro w hw
    apply hUball
    exact Metric.ball_subset_ball (by dsimp only [r]; exact min_le_left _ _) hw
  have hBsubsetK : B ⊆ Metric.ball z rK := by
    apply Metric.ball_subset_ball
    dsimp only [r]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hBsubsetE : B ⊆ Metric.ball z rE := by
    apply Metric.ball_subset_ball
    dsimp only [r]
    exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hKshiftBall : AnalyticOnNhd Complex Kshift B :=
    hKball.mono hBsubsetK
  have hExpEqBall : B.EqOn (Complex.exp ∘ L) (Complex.exp ∘ Kshift) := by
    intro w hw
    rw [hLexp (hBsubsetU hw)]
    exact (hEball w (hBsubsetE hw)).symm
  have hzB : z ∈ B := by
    exact Metric.mem_ball_self hr
  have hKshiftAtZ : Kshift z = L z := by
    dsimp only [Kshift]
    ring
  have hExpToNonzeroEqBall :
      B.EqOn
        ((fun w : Complex => (⟨Complex.exp w, Complex.exp_ne_zero w⟩ : {v : Complex // v ≠ 0}))
          ∘ L)
        ((fun w : Complex => (⟨Complex.exp w, Complex.exp_ne_zero w⟩ : {v : Complex // v ≠ 0}))
          ∘ Kshift) := by
    intro w hw
    apply Subtype.ext
    exact hExpEqBall hw
  have hEqOn : B.EqOn L Kshift :=
    Complex.isCoveringMap_exp.eqOn_of_comp_eqOn (convex_ball z r).isPreconnected
      (hLcont.mono hBsubsetU) hKshiftBall.continuousOn hExpToNonzeroEqBall hzB hKshiftAtZ.symm
  refine hKshiftBall z hzB |>.congr ?_
  filter_upwards [Metric.ball_mem_nhds z hr] with w hw
  exact (hEqOn hw).symm

/-- The exact zero-free cofactor supplied by a finite xi divisor factorization
has a continuous logarithm on the corresponding open factorization ball. -/
theorem exists_xiClosedBall_factorization_with_continuous_log_on_ball
    (c : Complex) (R : Real) (hR : 0 < R) :
    ∃ g L : Complex -> Complex,
      AnalyticOnNhd Complex g (Metric.closedBall c R) ∧
      (∀ u : Metric.closedBall c R, g u ≠ 0) ∧
      completedRiemannXi =ᶠ[codiscreteWithin (Metric.closedBall c R)]
        xiClosedBallFactor c R • g ∧
      ContinuousOn L (Metric.ball c R) ∧
      EqOn (Complex.exp ∘ L) g (Metric.ball c R) := by
  obtain ⟨g, hanalytic, hnonzero, hfactor⟩ :=
    exists_xiClosedBall_factorization c R
  rw [abs_of_pos hR] at hanalytic hnonzero hfactor
  have hgBall : AnalyticOnNhd Complex g (Metric.ball c R) := by
    intro z hz
    exact hanalytic z (Metric.ball_subset_closedBall hz)
  have hnonzeroBall : ∀ z ∈ Metric.ball c R, g z ≠ 0 := by
    intro z hz
    exact hnonzero ⟨z, Metric.ball_subset_closedBall hz⟩
  obtain ⟨L, hLcont, hLexp⟩ :=
    exists_continuousOn_log_of_analyticOnNhd_nonzero_ball (g := g) (c := c) (R := R)
      hR hgBall hnonzeroBall
  exact ⟨g, L, hanalytic, hnonzero, hfactor, hLcont, hLexp⟩

/-- The continuous logarithm carried by a finite xi cofactor factorization is
analytic on the same open factorization ball.  This preserves the exact
finite-factor owner, rather than selecting unrelated pointwise log branches. -/
theorem exists_xiClosedBall_factorization_with_analytic_log_on_ball
    (c : Complex) (R : Real) (hR : 0 < R) :
    ∃ g L : Complex -> Complex,
      AnalyticOnNhd Complex g (Metric.closedBall c R) ∧
      (∀ u : Metric.closedBall c R, g u ≠ 0) ∧
      completedRiemannXi =ᶠ[codiscreteWithin (Metric.closedBall c R)]
        xiClosedBallFactor c R • g ∧
      AnalyticOnNhd Complex L (Metric.ball c R) ∧
      ContinuousOn L (Metric.ball c R) ∧
      EqOn (Complex.exp ∘ L) g (Metric.ball c R) := by
  obtain ⟨g, L, hganalytic, hgnonzero, hfactor, hLcont, hLexp⟩ :=
    exists_xiClosedBall_factorization_with_continuous_log_on_ball c R hR
  have hgBall : AnalyticOnNhd Complex g (Metric.ball c R) := by
    intro z hz
    exact hganalytic z (Metric.ball_subset_closedBall hz)
  have hgnonzeroBall : ∀ z ∈ Metric.ball c R, g z ≠ 0 := by
    intro z hz
    exact hgnonzero ⟨z, Metric.ball_subset_closedBall hz⟩
  have hLanalytic : AnalyticOnNhd Complex L (Metric.ball c R) :=
    analyticOnNhd_of_continuousOn_exp_eqOn Metric.isOpen_ball hgBall hgnonzeroBall hLcont hLexp
  exact ⟨g, L, hganalytic, hgnonzero, hfactor, hLanalytic, hLcont, hLexp⟩

end C1XiAnalyticLog
end Source
end ConnesWeilRH
