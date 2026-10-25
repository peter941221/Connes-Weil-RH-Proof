import ConnesWeilRH.Dev.C1RouteAOwnerPuncturedBridge3087

/-!
# Route A strict negative joint-symbol neighbourhood (record 3088)

This file isolates the topological part of the local negative-energy screen.
Continuity and a strict negative value at zero produce a negative ball. The
remaining special-function work is only the scalar margin at zero.
-/

namespace ConnesWeilRH
namespace Source
namespace C1RouteAJointSymbolNegativeNeighbourhood3088

open C1RouteAJointSymbolData3080
open C1G8R0OrbitGeometry
open CC20YoshidaNearZeros
open CC20YoshidaConvolution
open CCM25Concrete.CompactLogConvolution
open Filter
open scoped Topology

noncomputable section

theorem exists_negative_ball_of_continuousAt_strict_neg
    {rho : sourceNontrivialZeroSet}
    {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g)
    (hcont : ContinuousAt (routeAJointSymbol geometry) 0)
    (hzero : routeAJointSymbol geometry 0 < 0) :
    ∃ r : Real, 0 < r ∧ ∀ xi : Real, |xi| < r →
      routeAJointSymbol geometry xi < 0 := by
  have hopen : IsOpen (Set.Iio (0 : Real)) := isOpen_Iio
  have hmem : Set.Iio (0 : Real) ∈ 𝓝 (routeAJointSymbol geometry 0) :=
    hopen.mem_nhds hzero
  have hpre : (routeAJointSymbol geometry) ⁻¹' Set.Iio (0 : Real) ∈ 𝓝 (0 : Real) :=
    hcont.preimage_mem_nhds hmem
  rcases Metric.mem_nhds_iff.mp hpre with ⟨r, hr, hball⟩
  refine ⟨r, hr, ?_⟩
  intro xi hxi
  exact hball (by simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using hxi)

end
end C1RouteAJointSymbolNegativeNeighbourhood3088
end Source
end ConnesWeilRH
