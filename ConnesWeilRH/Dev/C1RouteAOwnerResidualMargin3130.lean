import ConnesWeilRH.Dev.C1RouteAOwnerPrimePowerResidual3128

/-!
# Route A owner residual to margin bridge

This module isolates the exact analytic interface needed after the
prime-power residual was named.  It defines the finite owner symbol and
proves that the existing Route-A symbol is the finite symbol minus the
owner-specific residual.  The integral transfer theorem keeps integrability
as an explicit premise; it does not manufacture a residual bound.
-/

namespace ConnesWeilRH
namespace Source
namespace C1RouteAOwnerResidualMargin3130

open MeasureTheory
open C1G8R0OrbitGeometry
open C1RouteAJointSymbolData3080
open C1RouteAPrimePowerExpansion3127
open C1RouteAOwnerPrimePowerResidual3128
open scoped BigOperators

noncomputable section

/-- The Route-A prime symbol after replacing the infinite prime-base
Poisson expansion by the exact finite owner kernel. -/
def routeAActualOwnerSymbol
    {rho : CC20YoshidaNearZeros.sourceNontrivialZeroSet}
    {g : CCM25Concrete.CompactLogConvolution.CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (xi : Real) : Real :=
  -Dev.c3Sigma xi - routeAActualFinitePrimeKernel geometry xi

def routeAActualOwnerEnergyDensity
    {rho : CC20YoshidaNearZeros.sourceNontrivialZeroSet}
    {g : CCM25Concrete.CompactLogConvolution.CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (xi : Real) : Real :=
  routeAActualOwnerSymbol geometry xi *
    ‖routeAOrbitTransform geometry xi‖ ^ 2

def routeAOwnerFrequencyEnergyIntegral
    {rho : CC20YoshidaNearZeros.sourceNontrivialZeroSet}
    {g : CCM25Concrete.CompactLogConvolution.CompactLogTest}
    (geometry : OrbitG8Geometry rho g) : Real :=
  ∫ xi : Real, routeAFrequencyEnergyDensity geometry xi

def routeAOwnerResidualEnergyDensity
    {rho : CC20YoshidaNearZeros.sourceNontrivialZeroSet}
    {g : CCM25Concrete.CompactLogConvolution.CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (xi : Real) : Real :=
  routeAOwnerPrimePowerResidual geometry xi *
    ‖routeAOrbitTransform geometry xi‖ ^ 2

theorem routeAJointSymbol_eq_actualOwnerSymbol_sub_residual
    {rho : CC20YoshidaNearZeros.sourceNontrivialZeroSet}
    {g : CCM25Concrete.CompactLogConvolution.CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (xi : Real) :
    routeAJointSymbol geometry xi =
      routeAActualOwnerSymbol geometry xi -
        routeAOwnerPrimePowerResidual geometry xi := by
  unfold routeAActualOwnerSymbol routeAOwnerPrimePowerResidual
    routeAInfinitePrimePowerKernel routeAJointSymbol
  have hprimeSum :
      (∑ p ∈ routeAVisiblePrimes geometry,
        Real.log (p : Real) * routeAPrimePoissonSymbol p xi) =
      ∑ p ∈ routeAVisiblePrimes geometry,
        Real.log (p : Real) * routeAPrimePowerExpansion p xi := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [routeAPrimePoissonSymbol_eq_primePowerExpansion p
      (Finset.mem_filter.mp hp).2 xi]
  rw [hprimeSum]
  ring

theorem routeAFrequencyEnergyDensity_eq_actual_sub_residual
    {rho : CC20YoshidaNearZeros.sourceNontrivialZeroSet}
    {g : CCM25Concrete.CompactLogConvolution.CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (xi : Real) :
    routeAFrequencyEnergyDensity geometry xi =
      routeAActualOwnerEnergyDensity geometry xi -
        routeAOwnerResidualEnergyDensity geometry xi := by
  unfold routeAFrequencyEnergyDensity routeAActualOwnerEnergyDensity
    routeAOwnerResidualEnergyDensity
  rw [routeAJointSymbol_eq_actualOwnerSymbol_sub_residual geometry xi]
  ring

theorem routeAFrequencyEnergyIntegral_eq_actual_sub_residual
    {rho : CC20YoshidaNearZeros.sourceNontrivialZeroSet}
    {g : CCM25Concrete.CompactLogConvolution.CompactLogTest}
    (geometry : OrbitG8Geometry rho g)
    (hactual : Integrable (routeAActualOwnerEnergyDensity geometry))
    (hresidual : Integrable (routeAOwnerResidualEnergyDensity geometry)) :
    routeAOwnerFrequencyEnergyIntegral geometry =
      (∫ xi : Real, routeAActualOwnerEnergyDensity geometry xi) -
        ∫ xi : Real, routeAOwnerResidualEnergyDensity geometry xi := by
  unfold routeAOwnerFrequencyEnergyIntegral
  rw [show (fun xi : Real => routeAFrequencyEnergyDensity geometry xi) =
      (fun xi : Real => routeAActualOwnerEnergyDensity geometry xi -
        routeAOwnerResidualEnergyDensity geometry xi) by
    funext xi
    exact routeAFrequencyEnergyDensity_eq_actual_sub_residual geometry xi]
  exact integral_sub hactual hresidual

end
end C1RouteAOwnerResidualMargin3130
end Source
end ConnesWeilRH
