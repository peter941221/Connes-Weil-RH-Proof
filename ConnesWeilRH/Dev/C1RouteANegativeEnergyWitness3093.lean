import ConnesWeilRH.Dev.C1RouteAZeroFrequencyMargin3089
import ConnesWeilRH.Dev.C1RouteAJointSymbolContinuity3091
import ConnesWeilRH.Dev.C1RouteAOwnerPuncturedBridge3087
import ConnesWeilRH.Dev.C1RouteANonzeroNegativeEnergy3084
import ConnesWeilRH.Dev.C1C3SigmaZeroMargin3090
import ConnesWeilRH.Dev.C1RouteAOwnerAnalyticTransform3092

/-!
# Route A assembled local negative-energy witness (record 3093)

This is the final local composition theorem.  The only unresolved analytic
input is the actual owner transform's global analyticity; zero-frequency
margin, symbol continuity, and a global nonzero owner frequency are now
instantiated below.
-/

namespace ConnesWeilRH
namespace Source
namespace C1RouteANegativeEnergyWitness3093

open C1RouteAJointSymbolData3080
open C1RouteAZeroFrequencyMargin3089
open C1RouteAJointSymbolContinuity3091
open C1RouteAJointSymbolNegativeNeighbourhood3088
open C1RouteAOwnerPuncturedBridge3087
open C1RouteANonzeroNegativeEnergy3084
open Dev.C1C3SigmaZeroMargin3090
open C1RouteAOwnerAnalyticTransform3092
open C1G8R0OrbitGeometry
open CC20YoshidaNearZeros
open CC20YoshidaConvolution
open CCM25Concrete.CompactLogConvolution
open scoped Topology

noncomputable section

theorem exists_nonzero_frequency_negative_energy
    {rho : sourceNontrivialZeroSet}
    {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g)
    (hsigma : 0 < Dev.c3Sigma 0)
    (hsigma_cont : ContinuousAt Dev.c3Sigma 0)
    (hanalytic : AnalyticOnNhd Real
      (fun xi : Real => routeAOrbitTransform geometry xi) Set.univ)
    (hglobal : ∃ xi : Real, routeAOrbitTransform geometry xi ≠ 0) :
    ∃ xi : Real,
      xi ≠ 0 ∧
      routeAJointSymbol geometry xi < 0 ∧
      routeAOrbitTransform geometry xi ≠ 0 ∧
      routeAFrequencyEnergyDensity geometry xi < 0 := by
  have hzero : routeAJointSymbol geometry 0 < 0 :=
    routeAJointSymbol_zero_neg_of_c3Sigma_zero_pos geometry hsigma
  have hcont : ContinuousAt (routeAJointSymbol geometry) 0 :=
    routeAJointSymbol_continuousAt_zero_of_c3Sigma geometry hsigma_cont
  obtain ⟨r, hr, hneg⟩ :=
    exists_negative_ball_of_continuousAt_strict_neg geometry hcont hzero
  obtain ⟨xi, hxi_ne, hxi_ball, hxi_transform⟩ :=
    exists_routeA_nonzero_transform_in_ball geometry r hr hanalytic hglobal
  have henergy : routeAFrequencyEnergyDensity geometry xi < 0 := by
    unfold routeAFrequencyEnergyDensity
    exact mul_neg_of_neg_of_pos (hneg xi hxi_ball) (by
      have hnorm : 0 < ‖routeAOrbitTransform geometry xi‖ :=
        norm_pos_iff.mpr hxi_transform
      positivity)
  exact ⟨xi, hxi_ne, hneg xi hxi_ball, hxi_transform, henergy⟩

theorem exists_nonzero_frequency_negative_energy_of_owner_analytic
    {rho : sourceNontrivialZeroSet}
    {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g)
    (hanalytic : AnalyticOnNhd Real
      (fun xi : Real => routeAOrbitTransform geometry xi) Set.univ) :
    ∃ xi : Real,
      xi ≠ 0 ∧
      routeAJointSymbol geometry xi < 0 ∧
      routeAOrbitTransform geometry xi ≠ 0 ∧
      routeAFrequencyEnergyDensity geometry xi < 0 := by
  exact exists_nonzero_frequency_negative_energy geometry
    c3Sigma_zero_pos c3Sigma_continuousAt_zero hanalytic
    (routeAOrbitTransform_global_nonzero geometry)

end
end C1RouteANegativeEnergyWitness3093
end Source
end ConnesWeilRH
