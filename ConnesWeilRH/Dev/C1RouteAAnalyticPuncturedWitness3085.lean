import ConnesWeilRH.Dev.C1RouteANonzeroNegativeEnergy3084
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Route A analytic punctured-neighbourhood witness (record 3085)

This module converts the isolated-zero theorem into the exact witness shape
needed by record 3084.  It deliberately leaves the owner-specific analytic
premise explicit.
-/

namespace ConnesWeilRH
namespace Source
namespace C1RouteAAnalyticPuncturedWitness3085

open Filter
open Metric
open scoped Topology

noncomputable section

theorem exists_nonzero_point_in_ball_of_analyticAt_not_eventually_zero
    {f : Real → Complex} (r : Real) (hr : 0 < r)
    (hf : AnalyticAt Real f 0)
    (hnot : ¬ (∀ᶠ x in 𝓝 (0 : Real), f x = 0)) :
    ∃ x : Real, x ≠ 0 ∧ |x| < r ∧ f x ≠ 0 := by
  have hpunct : ∀ᶠ x in 𝓝[≠] (0 : Real), f x ≠ 0 := by
    exact hf.eventually_eq_zero_or_eventually_ne_zero.resolve_left hnot
  have hball : ∀ᶠ x in 𝓝[≠] (0 : Real), |x| < r := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds
      (Metric.ball_mem_nhds (0 : Real) hr)] with x hx
    simpa [Real.dist_eq, abs_sub_comm] using hx
  have hne : ∀ᶠ x in 𝓝[≠] (0 : Real), x ≠ 0 := by
    exact self_mem_nhdsWithin
  obtain ⟨x, hx_nonzero, hx_ball, hx_ne⟩ :=
    (hpunct.and (hball.and hne)).exists
  exact ⟨x, hx_ne, hx_ball, hx_nonzero⟩

end
end C1RouteAAnalyticPuncturedWitness3085
end Source
end ConnesWeilRH
