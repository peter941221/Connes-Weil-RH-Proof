import ConnesWeilRH.Dev.C1RouteALaplaceFourierBridge3086
import ConnesWeilRH.Dev.C1RouteAAnalyticPuncturedWitness3085
import Mathlib.Analysis.Analytic.Uniqueness

/-!
# Route A owner punctured nonzero bridge (record 3087)

This is the owner-level adapter for record 3085.  It keeps the analytic
premise explicit and uses one global nonzero Fourier value to rule out an
eventually-zero neighbourhood at the origin.
-/

namespace ConnesWeilRH
namespace Source
namespace C1RouteAOwnerPuncturedBridge3087

open C1RouteAAnalyticPuncturedWitness3085
open C1RouteALaplaceFourierBridge3086
open C1RouteAJointSymbolData3080
open Filter
open CC20YoshidaNearZeros
open CC20YoshidaConvolution
open CCM25Concrete.CompactLogConvolution
open scoped FourierTransform Topology

noncomputable section

theorem routeAOrbitTransform_not_eventually_zero_of_fourier_nonzero
    {rho : sourceNontrivialZeroSet}
    {g : CompactLogTest}
    (geometry : C1G8R0OrbitGeometry.OrbitG8Geometry rho g)
    (hanalytic : AnalyticOnNhd Real
      (fun xi : Real => routeAOrbitTransform geometry xi) Set.univ)
    (hglobal : ∃ xi : Real, routeAOrbitTransform geometry xi ≠ 0) :
    ¬ (∀ᶠ xi in 𝓝 (0 : Real), routeAOrbitTransform geometry xi = 0) := by
  intro hzero
  obtain ⟨xi, hxi⟩ := hglobal
  have hEq : Set.EqOn (fun t : Real => routeAOrbitTransform geometry t) 0
      Set.univ := by
    exact AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      hanalytic isPreconnected_univ (by simp) hzero
  have hxi_zero := hEq (Set.mem_univ xi)
  apply hxi
  simpa using hxi_zero

theorem exists_routeA_nonzero_transform_in_ball
    {rho : sourceNontrivialZeroSet}
    {g : CompactLogTest}
    (geometry : C1G8R0OrbitGeometry.OrbitG8Geometry rho g)
    (r : Real) (hr : 0 < r)
    (hanalytic : AnalyticOnNhd Real
      (fun xi : Real => routeAOrbitTransform geometry xi) Set.univ)
    (hglobal : ∃ xi : Real, routeAOrbitTransform geometry xi ≠ 0) :
    ∃ xi : Real, xi ≠ 0 ∧ |xi| < r ∧ routeAOrbitTransform geometry xi ≠ 0 := by
  apply exists_nonzero_point_in_ball_of_analyticAt_not_eventually_zero r hr
  · exact hanalytic 0 (by simp)
  · exact routeAOrbitTransform_not_eventually_zero_of_fourier_nonzero
      geometry hanalytic hglobal

end
end C1RouteAOwnerPuncturedBridge3087
end Source
end ConnesWeilRH
