import ConnesWeilRH.Dev.C1XiResidue
import Mathlib.Analysis.Meromorphic.FactorizedRational

/-!
# C1XiFiniteFactor - finite xi divisor factorization for Gate 2

On every closed complex ball, the completed xi function has only finitely many
zeros with analytic multiplicity.  Mathlib's meromorphic factorization API
therefore splits xi into the finite divisor product and one analytic, zero-free
remainder, with equality stated on the correct codiscrete domain.

This is a finite-contour interface only.  It does not choose an outer contour,
differentiate the factorization, prove a punctured-domain Cauchy theorem, read
back the arithmetic side, prove the explicit formula, or claim RH.
-/

namespace ConnesWeilRH
namespace Source
namespace C1XiFiniteFactor

open Filter
open CC20ZetaCounting
open C1SpectralWeil
open MeromorphicOn
open scoped BigOperators Topology

/-- The xi divisor on a closed ball.  Keeping the domain in the owner makes
the finite factorization and all later contour readbacks refer to the same
local zero family. -/
noncomputable def xiClosedBallDivisor (c : Complex) (R : Real) : Complex -> Int :=
  divisor completedRiemannXi (Metric.closedBall c |R|)

/-- The factorized rational function attached to the exact xi divisor on a
closed ball. -/
noncomputable def xiClosedBallFactor (c : Complex) (R : Real) : Complex -> Complex :=
  ∏ᶠ u, (fun z : Complex => (z - u) ^ xiClosedBallDivisor c R u)

/-- The local xi divisor has finite support because its domain is compact. -/
theorem xiClosedBallDivisor_support_finite (c : Complex) (R : Real) :
    (xiClosedBallDivisor c R).support.Finite := by
  exact (divisor completedRiemannXi (Metric.closedBall c |R|)).finiteSupport
    (isCompact_closedBall c |R|)

/-- Every point in the local divisor support is both in its owning closed
ball and a genuine xi zero.  This is the direction needed to exclude a local
pole from an xi-nonzero punctured contour point. -/
theorem xiClosedBallDivisor_mem_closedBall_and_xi_eq_zero_of_mem_support
    (c : Complex) (R : Real) {z : Complex}
    (hz : z ∈ (xiClosedBallDivisor c R).support) :
    z ∈ Metric.closedBall c |R| ∧ completedRiemannXi z = 0 := by
  have hzero_set :
      Metric.closedBall c |R| ∩ completedRiemannXi ⁻¹' {0} =
        Function.support (xiClosedBallDivisor c R) := by
    simpa only [xiClosedBallDivisor] using
      MeromorphicNFOn.zero_set_eq_divisor_support
        ((analyticOnNhd_completedRiemannXi (Metric.closedBall c |R|)).meromorphicNFOn)
        (fun u => by
          rw [(differentiable_completedRiemannXi.analyticAt u).meromorphicOrderAt_eq]
          intro htop
          exact completedRiemannXi_analyticOrderAt_ne_top u
            (ENat.map_eq_top_iff.mp htop))
  rw [← hzero_set] at hz
  simpa only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff] using hz

/-- On its owning closed ball, the finite xi divisor support is exactly the
zero set of xi.  This bridge lets contour callers state their punctured-domain
condition with the ordinary analytic predicate `completedRiemannXi z != 0`,
without unfolding the local divisor. -/
theorem xiClosedBallDivisor_mem_support_iff
    (c : Complex) (R : Real) {z : Complex}
    (hz : z ∈ Metric.closedBall c |R|) :
    z ∈ (xiClosedBallDivisor c R).support ↔ completedRiemannXi z = 0 := by
  have hzero_set :
      Metric.closedBall c |R| ∩ completedRiemannXi ⁻¹' {0} =
        Function.support (xiClosedBallDivisor c R) := by
    simpa only [xiClosedBallDivisor] using
      MeromorphicNFOn.zero_set_eq_divisor_support
        ((analyticOnNhd_completedRiemannXi (Metric.closedBall c |R|)).meromorphicNFOn)
        (fun u => by
          rw [(differentiable_completedRiemannXi.analyticAt u).meromorphicOrderAt_eq]
          intro htop
          exact completedRiemannXi_analyticOrderAt_ne_top u
            (ENat.map_eq_top_iff.mp htop))
  rw [← hzero_set]
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
  exact and_iff_right hz

/-- Every local xi divisor value is nonnegative: the completed xi function is
entire, so the finite factor has zeros but no poles. -/
theorem xiClosedBallDivisor_nonneg (c : Complex) (R : Real) (z : Complex) :
    0 <= xiClosedBallDivisor c R z := by
  exact ((analyticOnNhd_completedRiemannXi _).divisor_nonneg) z

/-- The finite xi divisor factor is analytic everywhere: xi is entire, so
its local divisor has no negative exponents. -/
theorem xiClosedBallFactor_analyticAt (c : Complex) (R : Real) (z : Complex) :
    AnalyticAt Complex (xiClosedBallFactor c R) z := by
  simpa only [xiClosedBallFactor] using
    (Function.FactorizedRational.analyticAt
      (xiClosedBallDivisor_nonneg c R z))

/-- The factorized xi divisor is exactly a finite product over its support.
This avoids later accidentally treating a `finprod` as an infinite product. -/
theorem xiClosedBallFactor_eq_product_support (c : Complex) (R : Real) :
    xiClosedBallFactor c R = fun z =>
      ∏ u ∈ (xiClosedBallDivisor_support_finite c R).toFinset,
        (z - u) ^ xiClosedBallDivisor c R u := by
  classical
  rw [xiClosedBallFactor]
  calc
    (∏ᶠ u : Complex, fun z : Complex => (z - u) ^ xiClosedBallDivisor c R u) =
        fun z : Complex => ∏ᶠ u : Complex, (z - u) ^ xiClosedBallDivisor c R u :=
      Function.FactorizedRational.finprod_eq_fun
        (xiClosedBallDivisor_support_finite c R)
    _ = fun z =>
        ∏ u ∈ (xiClosedBallDivisor_support_finite c R).toFinset,
          (z - u) ^ xiClosedBallDivisor c R u := by
      funext z
      apply finprod_eq_prod_of_mulSupport_subset
      intro u hu
      contrapose! hu
      simp_all

/-- On a closed ball, xi factors into its exact finite divisor product and a
zero-free analytic remainder.  The equality is deliberately only
`codiscreteWithin`: Mathlib's meromorphic normal form is an equivalence class
at isolated exceptional points, so treating it as pointwise equality would be
unsound. -/
theorem exists_xiClosedBall_factorization (c : Complex) (R : Real) :
    ∃ g : Complex -> Complex,
      AnalyticOnNhd Complex g (Metric.closedBall c |R|) ∧
      (∀ u : Metric.closedBall c |R|, g u ≠ 0) ∧
      completedRiemannXi =ᶠ[codiscreteWithin (Metric.closedBall c |R|)]
        xiClosedBallFactor c R • g := by
  have hmeromorphic : MeromorphicOn completedRiemannXi (Metric.closedBall c |R|) :=
    (analyticOnNhd_completedRiemannXi _).meromorphicOn
  obtain ⟨g, hanalytic, hnonzero, hfactor⟩ :=
    hmeromorphic.extract_zeros_poles
      (fun u => by
        rw [(differentiable_completedRiemannXi.analyticAt u).meromorphicOrderAt_eq]
        intro htop
        exact completedRiemannXi_analyticOrderAt_ne_top u
          (ENat.map_eq_top_iff.mp htop))
      (by simpa only [xiClosedBallDivisor] using
        xiClosedBallDivisor_support_finite c R)
  refine ⟨g, hanalytic, hnonzero, ?_⟩
  simpa only [xiClosedBallFactor, xiClosedBallDivisor] using hfactor

/-- At an interior point, the codiscrete factorization agrees on a whole
neighborhood.  This is the derivative-safe form of the local factorization;
later `logDeriv` arguments must use it rather than rewriting from a bare
codiscrete equality. -/
theorem xiClosedBall_factorization_eventuallyEq_nhds_of_mem_ball
    {c : Complex} {R : Real} {g : Complex -> Complex}
    (hanalytic : AnalyticOnNhd Complex g (Metric.closedBall c |R|))
    (hfactor : completedRiemannXi =ᶠ[codiscreteWithin (Metric.closedBall c |R|)]
      xiClosedBallFactor c R • g)
    {z : Complex} (hz : z ∈ Metric.ball c |R|) :
    completedRiemannXi =ᶠ[𝓝 z] xiClosedBallFactor c R • g := by
  have hfactor_analytic : AnalyticAt Complex (xiClosedBallFactor c R) z :=
    xiClosedBallFactor_analyticAt c R z
  have hg_analytic : AnalyticAt Complex g z :=
    hanalytic z (Metric.ball_subset_closedBall hz)
  have hrhs_analytic : AnalyticAt Complex (xiClosedBallFactor c R • g) z := by
    simpa only [Pi.smul_apply, smul_eq_mul] using hfactor_analytic.mul hg_analytic
  have hacc_ball : AccPt z (𝓟 (Metric.ball c |R|)) :=
    Metric.isOpen_ball.preperfect z hz
  have hacc_closedBall : AccPt z (𝓟 (Metric.closedBall c |R|)) :=
    hacc_ball.mono (principal_mono.mpr Metric.ball_subset_closedBall)
  have hxi_meromorphic : MeromorphicAt completedRiemannXi z :=
    (differentiable_completedRiemannXi.analyticAt z).meromorphicAt
  have hpunctured : completedRiemannXi =ᶠ[𝓝[≠] z] xiClosedBallFactor c R • g :=
    hxi_meromorphic.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin
      hrhs_analytic.meromorphicAt
      (Metric.ball_subset_closedBall hz)
      hacc_closedBall
      hfactor
  have hxi_continuous : ContinuousAt completedRiemannXi z :=
    (differentiable_completedRiemannXi.analyticAt z).continuousAt
  exact (ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
    hxi_continuous hrhs_analytic.continuousAt).mp hpunctured

/-- The codiscrete normal-form factorization is pointwise on the open ball.
At an interior point, both sides are analytic; the meromorphic identity
principle first upgrades the codiscrete equality to a punctured neighborhood,
then continuity restores the center point.  No corresponding boundary claim is
made here, because the factorization theorem itself only supplies a
codiscrete-within equality on the closed ball. -/
theorem xiClosedBall_factorization_eq_of_mem_ball
    {c : Complex} {R : Real} {g : Complex -> Complex}
    (hanalytic : AnalyticOnNhd Complex g (Metric.closedBall c |R|))
    (hfactor : completedRiemannXi =ᶠ[codiscreteWithin (Metric.closedBall c |R|)]
      xiClosedBallFactor c R • g)
    {z : Complex} (hz : z ∈ Metric.ball c |R|) :
    completedRiemannXi z = xiClosedBallFactor c R z * g z := by
  have hneighborhood : completedRiemannXi =ᶠ[𝓝 z] xiClosedBallFactor c R • g :=
    xiClosedBall_factorization_eventuallyEq_nhds_of_mem_ball hanalytic hfactor hz
  simpa only [Pi.smul_apply, smul_eq_mul] using hneighborhood.eq_of_nhds

/-- Away from the finite local divisor support, the factorized xi divisor has
the expected finite logarithmic-derivative sum.  The support hypothesis is
essential: it excludes the zeros where the total Lean `logDeriv` value is not
the meromorphic principal part. -/
theorem logDeriv_xiClosedBallFactor_eq_sum_of_not_mem_support
    (c : Complex) (R : Real) {z : Complex}
    (hz : z ∉ (xiClosedBallDivisor c R).support) :
    logDeriv (xiClosedBallFactor c R) z =
      ∑ u ∈ (xiClosedBallDivisor_support_finite c R).toFinset,
        (xiClosedBallDivisor c R u : Complex) / (z - u) := by
  classical
  rw [xiClosedBallFactor_eq_product_support]
  rw [logDeriv_prod]
  · apply Finset.sum_congr rfl
    intro u hu
    rw [logDeriv_fun_zpow (f := fun w : Complex => w - u) (by fun_prop)]
    rw [logDeriv_apply, deriv_sub_const]
    simp [div_eq_mul_inv]
  · intro u hu
    have hzu : z ≠ u := by
      intro hzu
      apply hz
      rw [hzu]
      simpa only [Set.Finite.mem_toFinset, Function.mem_support] using hu
    exact zpow_ne_zero _ (sub_ne_zero.mpr hzu)
  · intro u _hu
    exact (AnalyticAt.fun_zpow_nonneg (by fun_prop)
      (xiClosedBallDivisor_nonneg c R u)).differentiableAt

/-- Inside the ball and away from its finite xi divisor support, the xi
logarithmic derivative splits into the exact finite multiplicity pole sum and
the logarithmic derivative of the same zero-free cofactor.  The input is a
neighborhood equality, obtained from the codiscrete normal form by the
identity principle; pointwise equality alone would not justify the derivative
transport used here. -/
theorem logDeriv_completedRiemannXi_eq_sum_add_cofactor
    {c : Complex} {R : Real} {g : Complex -> Complex}
    (hanalytic : AnalyticOnNhd Complex g (Metric.closedBall c |R|))
    (hnonzero : ∀ u : Metric.closedBall c |R|, g u ≠ 0)
    (hfactor : completedRiemannXi =ᶠ[codiscreteWithin (Metric.closedBall c |R|)]
      xiClosedBallFactor c R • g)
    {z : Complex} (hzball : z ∈ Metric.ball c |R|)
    (hzsupport : z ∉ (xiClosedBallDivisor c R).support) :
    logDeriv completedRiemannXi z =
      (∑ u ∈ (xiClosedBallDivisor_support_finite c R).toFinset,
        (xiClosedBallDivisor c R u : Complex) / (z - u)) + logDeriv g z := by
  have hneighborhood : completedRiemannXi =ᶠ[𝓝 z]
      (fun w => xiClosedBallFactor c R w * g w) := by
    simpa only [Pi.smul_apply, smul_eq_mul] using
      xiClosedBall_factorization_eventuallyEq_nhds_of_mem_ball hanalytic hfactor hzball
  have hfactor_nonzero : xiClosedBallFactor c R z ≠ 0 := by
    rw [xiClosedBallFactor]
    apply Function.FactorizedRational.ne_zero
    simpa only [Function.mem_support, not_not] using hzsupport
  have hg_nonzero : g z ≠ 0 :=
    hnonzero ⟨z, Metric.ball_subset_closedBall hzball⟩
  have hfactor_analytic : AnalyticAt Complex (xiClosedBallFactor c R) z :=
    xiClosedBallFactor_analyticAt c R z
  have hg_analytic : AnalyticAt Complex g z :=
    hanalytic z (Metric.ball_subset_closedBall hzball)
  calc
    logDeriv completedRiemannXi z =
        logDeriv (fun w => xiClosedBallFactor c R w * g w) z := by
      simp only [logDeriv_apply]
      rw [hneighborhood.deriv_eq, hneighborhood.eq_of_nhds]
    _ = logDeriv (xiClosedBallFactor c R) z + logDeriv g z :=
      logDeriv_mul z hfactor_nonzero hg_nonzero
        hfactor_analytic.differentiableAt hg_analytic.differentiableAt
    _ = (∑ u ∈ (xiClosedBallDivisor_support_finite c R).toFinset,
        (xiClosedBallDivisor c R u : Complex) / (z - u)) + logDeriv g z := by
      rw [logDeriv_xiClosedBallFactor_eq_sum_of_not_mem_support c R hzsupport]

/-- The finite logarithmic-derivative formula in the public xi-nonzero form.
Inside the open ball, `completedRiemannXi z != 0` is equivalent to avoiding the
same local divisor support, so this preserves the finite-factor owner while
giving contour callers the usual punctured-domain predicate. -/
theorem logDeriv_completedRiemannXi_eq_sum_add_cofactor_of_ne_zero
    {c : Complex} {R : Real} {g : Complex -> Complex}
    (hanalytic : AnalyticOnNhd Complex g (Metric.closedBall c |R|))
    (hnonzero : ∀ u : Metric.closedBall c |R|, g u ≠ 0)
    (hfactor : completedRiemannXi =ᶠ[codiscreteWithin (Metric.closedBall c |R|)]
      xiClosedBallFactor c R • g)
    {z : Complex} (hzball : z ∈ Metric.ball c |R|)
    (hzxi : completedRiemannXi z ≠ 0) :
    logDeriv completedRiemannXi z =
      (∑ u ∈ (xiClosedBallDivisor_support_finite c R).toFinset,
        (xiClosedBallDivisor c R u : Complex) / (z - u)) + logDeriv g z := by
  apply logDeriv_completedRiemannXi_eq_sum_add_cofactor hanalytic hnonzero hfactor hzball
  intro hzsupport
  exact hzxi ((xiClosedBallDivisor_mem_support_iff c R
    (Metric.ball_subset_closedBall hzball)).mp hzsupport)

/-- A single cofactor simultaneously owns the original codiscrete
factorization and its pointwise open-ball continuation. -/
theorem exists_xiClosedBall_factorization_on_ball (c : Complex) (R : Real) :
    ∃ g : Complex -> Complex,
      AnalyticOnNhd Complex g (Metric.closedBall c |R|) ∧
      (∀ u : Metric.closedBall c |R|, g u ≠ 0) ∧
      completedRiemannXi =ᶠ[codiscreteWithin (Metric.closedBall c |R|)]
        xiClosedBallFactor c R • g ∧
      ∀ z ∈ Metric.ball c |R|,
        completedRiemannXi z = xiClosedBallFactor c R z * g z := by
  obtain ⟨g, hanalytic, hnonzero, hfactor⟩ :=
    exists_xiClosedBall_factorization c R
  refine ⟨g, hanalytic, hnonzero, hfactor, ?_⟩
  intro z hz
  exact xiClosedBall_factorization_eq_of_mem_ball hanalytic hfactor hz

end C1XiFiniteFactor
end Source
end ConnesWeilRH
