import ConnesWeilRH.Dev.C1RouteAJointSymbolData3080

/-!
# Route A joint-symbol readback contract (record 3081)

This file isolates the exact remaining analytic obligations.  It does not
assert the missing Fourier/prime-power identity.  A witness must provide the
full-line readback of `qw` and the positive-credit-versus-deficit inequality;
the sign conclusion is then elementary.
-/

namespace ConnesWeilRH
namespace Source
namespace C1RouteAJointSymbolReadback3081

open C1RouteAJointSymbolData3080
open C1G8R0OrbitGeometry
open C1SameOwnerWeil
open CCM25Concrete.CompactLogConvolution
open CC20YoshidaNearZeros
open scoped BigOperators

noncomputable section

def routeAFrequencyEnergyIntegral
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) : Real :=
  ∫ xi : Real, routeAFrequencyEnergyDensity geometry xi

def routeAFrequencyCreditIntegral
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) : Real :=
  ∫ xi : Real, routeAFrequencyCreditDensity geometry xi

def routeAFrequencyDeficitIntegral
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) : Real :=
  ∫ xi : Real, routeAFrequencyDeficitDensity geometry xi

structure RouteAJointSymbolReadbackContract
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) : Prop where
  qw_eq_energyIntegral : C1SameOwnerWeil.qw g =
    routeAFrequencyEnergyIntegral geometry
  credit_integrable : MeasureTheory.Integrable
    (routeAFrequencyCreditDensity geometry)
  deficit_integrable : MeasureTheory.Integrable
    (routeAFrequencyDeficitDensity geometry)
  energy_eq_credit_sub_deficit :
    routeAFrequencyEnergyIntegral geometry =
      routeAFrequencyCreditIntegral geometry -
        routeAFrequencyDeficitIntegral geometry
  deficit_le_credit : routeAFrequencyDeficitIntegral geometry ≤
    routeAFrequencyCreditIntegral geometry

theorem qw_nonneg_of_routeAJointSymbolReadback
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    {geometry : OrbitG8Geometry rho g}
    (h : RouteAJointSymbolReadbackContract geometry) :
    0 ≤ C1SameOwnerWeil.qw g := by
  rw [h.qw_eq_energyIntegral]
  rw [h.energy_eq_credit_sub_deficit]
  linarith [h.deficit_le_credit]

end
end C1RouteAJointSymbolReadback3081
end Source
end ConnesWeilRH
