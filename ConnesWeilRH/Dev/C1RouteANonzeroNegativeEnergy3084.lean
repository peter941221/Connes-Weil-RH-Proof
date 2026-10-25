import ConnesWeilRH.Dev.C1RouteAJointSymbolData3080

/-!
# Route A nonzero-frequency negative-energy contract (record 3084)

The zero-frequency joint symbol may be negative while the owner transform
vanishes there because of an interpolation pin.  This module isolates the
correct local replacement: a negative symbol neighbourhood together with one
nonzero transform point inside it forces a genuinely negative energy density.
-/

namespace ConnesWeilRH
namespace Source
namespace C1RouteANonzeroNegativeEnergy3084

open C1RouteAJointSymbolData3080
open C1G8R0OrbitGeometry
open CC20YoshidaNearZeros
open CC20YoshidaConvolution
open CC20YoshidaConvolution.CompactLogTest

noncomputable section

structure LocalNegativeEnergyWitness
    {rho : sourceNontrivialZeroSet}
    {g : CCM25Concrete.CompactLogConvolution.CompactLogTest}
    (geometry : OrbitG8Geometry rho g) where
  radius : Real
  radius_pos : 0 < radius
  symbol_neg_on_ball : ∀ xi : Real, |xi| < radius →
    routeAJointSymbol geometry xi < 0
  nonzero_transform_point : ∃ xi : Real,
    xi ≠ 0 ∧ |xi| < radius ∧ routeAOrbitTransform geometry xi ≠ 0

theorem exists_negative_energy_density_of_localWitness
    {rho : sourceNontrivialZeroSet}
    {g : CCM25Concrete.CompactLogConvolution.CompactLogTest}
    {geometry : OrbitG8Geometry rho g}
    (h : LocalNegativeEnergyWitness geometry) :
    ∃ xi : Real, routeAFrequencyEnergyDensity geometry xi < 0 := by
  obtain ⟨xi, hxi_ne, hxi_ball, htransform⟩ := h.nonzero_transform_point
  have hsymbol : routeAJointSymbol geometry xi < 0 :=
    h.symbol_neg_on_ball xi hxi_ball
  have hnorm : 0 < ‖routeAOrbitTransform geometry xi‖ ^ 2 := by
    have hnorm' : 0 < ‖routeAOrbitTransform geometry xi‖ :=
      norm_pos_iff.mpr htransform
    positivity
  refine ⟨xi, ?_⟩
  unfold routeAFrequencyEnergyDensity
  exact mul_neg_of_neg_of_pos hsymbol hnorm

end
end C1RouteANonzeroNegativeEnergy3084
end Source
end ConnesWeilRH
