import ConnesWeilRH.Dev.C1RouteANegativeEnergyWitness3093

namespace ConnesWeilRH
namespace Source
namespace C1RouteANegativeEnergyWitness3093Audit

open C1RouteAJointSymbolData3080
open C1RouteANonzeroNegativeEnergy3084
open C1RouteAJointSymbolSquareScreen3082
open C1G8R0OrbitGeometry
open CC20YoshidaNearZeros
open CCM25Concrete.CompactLogConvolution
open Dev.C1C3SigmaZeroMargin3090

-- The strict zero margin does not require any prime to be present.
theorem empty_prime_set_zero_margin :
    -Dev.c3Sigma 0 -
      (∑ p ∈ (∅ : Finset Nat), Real.log (p : Real) * routeAPrimePoissonSymbol p 0) < 0 := by
  simpa using (neg_lt_zero.mpr c3Sigma_zero_pos)

-- A zero transform at the origin gives zero energy, even with a negative symbol.
theorem energy_at_zero_eq_zero_of_off_line
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (hoff : rho.1.re ≠ 1 / 2) :
    routeAFrequencyEnergyDensity geometry 0 = 0 := by
  simp [routeAFrequencyEnergyDensity,
    routeAOrbitTransform_zero_eq_zero_of_off_line geometry hoff]

-- The witness must carry a nonzero transform point within its own radius.
theorem no_localWitness_when_transform_vanishes_on_its_ball
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    {geometry : OrbitG8Geometry rho g}
    (w : LocalNegativeEnergyWitness geometry)
    (hzero : ∀ xi : Real, |xi| < w.radius → routeAOrbitTransform geometry xi = 0) :
    False := by
  obtain ⟨xi, _, hball, hnonzero⟩ := w.nonzero_transform_point
  exact hnonzero (hzero xi hball)

#print axioms C1RouteANegativeEnergyWitness3093.exists_nonzero_frequency_negative_energy
#print axioms C1RouteANegativeEnergyWitness3093.exists_nonzero_frequency_negative_energy_of_owner_analytic
#check C1RouteANegativeEnergyWitness3093.exists_nonzero_frequency_negative_energy_witness
#print axioms C1RouteANegativeEnergyWitness3093.exists_nonzero_frequency_negative_energy_witness
#print axioms C1RouteANegativeEnergyWitness3093.not_routeAFrequencyEnergyDensity_pointwise_nonneg
#print axioms empty_prime_set_zero_margin
#print axioms energy_at_zero_eq_zero_of_off_line
#print axioms no_localWitness_when_transform_vanishes_on_its_ball

end C1RouteANegativeEnergyWitness3093Audit
end Source
end ConnesWeilRH
